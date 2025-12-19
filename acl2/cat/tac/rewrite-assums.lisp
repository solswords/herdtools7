;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause
;;
;;****************************************************************************;;
;; Disclaimer:                                                                ;;
;; This material covers both ASLv0 (viz, the existing ASL pseudocode language ;;
;; which appears in the Arm Architecture Reference Manual) and ASLv1, a new,  ;;
;; experimental, and as yet unreleased version of ASL.                        ;;
;; This material is work in progress, more precisely at pre-Alpha quality as  ;;
;; per Arm’s quality standards.                                               ;;
;; In particular, this means that it would be premature to base any           ;;
;; production tool development on this material.                              ;;
;; However, any feedback, question, query and feature request would be most   ;;
;; welcome; those can be sent to Arm’s Architecture Formal Team Lead          ;;
;; Jade Alglave <jade.alglave@arm.com>, or by raising issues or PRs to the    ;;
;; herdtools7 github repository.                                              ;;
;;****************************************************************************;;

(in-package "TAC")
(include-book "toplevel-rewriter")
(include-book "pos-neg-rewriter")
(local (include-book "common-thms"))
(local (include-book "std/lists/sets" :dir :system))
(local (std::add-default-post-define-hook :fix))


(fty::defmap used-subst-map :key-type pseudo-termp :val-type term-used-subst-database-p
  :true-listp t :valp-of-nil t)

(define is-negated-lit ((x pseudo-termp))
  (pseudo-term-case x :fncall (eq x.fn 'not) :otherwise nil))


(define unnegated-lit ((x pseudo-termp))
  :returns (lit pseudo-termp)
  :prepwork ((local (in-theory (enable is-negated-lit))))
  (if (is-negated-lit x)
      (first (pseudo-term-call->args x))
    (pseudo-term-fix x))
  ///
  (defret eval-of-<fn>
    (iff (tac-ev lit env)
         (xor (is-negated-lit x)
              (tac-ev x env))))

  (defret type-of-<fn>
    (implies (equal (tac-term-type x ctx) :pred)
             (equal (tac-term-type lit ctx) :pred))
    :hints(("Goal" :in-theory (enable tac-termlist-types acl2::prefixp))))

  (defret vars-of-<fn>
    (implies (not (member v (cmr::term-vars x)))
             (not (member v (cmr::term-vars lit))))
    :hints(("Goal" 
            :expand ((cmr::termlist-vars (pseudo-term-call->args x))
                     (cmr::term-vars x))))))

(define negate-lit ((x pseudo-termp))
  :returns (neg pseudo-termp)
  :prepwork ((local (in-theory (enable is-negated-lit))))
  (if (is-negated-lit x)
      (first (pseudo-term-call->args x))
    (pseudo-term-call 'not (list x)))
  ///
  (defret eval-of-<fn>
    (iff (tac-ev neg env)
         (not (tac-ev x env))))

  (defret type-of-<fn>
    (implies (equal (tac-term-type x ctx) :pred)
             (equal (tac-term-type neg ctx) :pred))
    :hints(("Goal" :in-theory (enable tac-termlist-types acl2::prefixp))))

  (defret vars-of-<fn>
    (implies (not (member v (cmr::term-vars x)))
             (not (member v (cmr::term-vars neg))))
    :hints(("Goal" 
            :expand ((cmr::termlist-vars (pseudo-term-call->args x))
                     (cmr::term-vars x)
                     (cmr::term-vars (pseudo-term-fncall 'not (list x)))
                     (cmr::termlist-vars (list x)))))))

(fty::deflist pseudo-term-list-list
  :pred pseudo-term-list-listp :elt-type pseudo-term-listp :true-listp t)



(define termlistlist-vars ((x pseudo-term-list-listp))
  :returns (vars cmr::pseudo-var-list-p)
  :verify-guards nil
  (if (atom x)
      nil
    (union-eq (cmr::termlist-vars (car x))
              (termlistlist-vars (cdr x))))
  ///
  (verify-guards termlistlist-vars))

(define tac-termlistlist-typed ((x pseudo-term-list-listp) (type tac-type-p) (ctx type-ctx-p))
  (if (atom x)
      t
    (and (subsetp-equal (tac-termlist-types (car x) ctx) (list (tac-type-fix type)))
         (tac-termlistlist-typed (cdr x) type ctx))))

(define termlistlist-subst-strict ((x pseudo-term-list-listp)
                                   (subst cmr::pseudo-term-subst-p))
  :returns (new-x pseudo-term-list-listp)
  (if (atom x)
      nil
    (cons (cmr::termlist-subst-strict (car x) subst)
          (termlistlist-subst-strict (cdr x) subst))))

(define tac-ev-clause ((x pseudo-term-listp)
                       env)
  :verify-guards nil
  (if (atom x)
      nil
    (or (tac-ev (car x) env)
        (tac-ev-clause (cdr x) env))))

(define tac-ev-conj-of-disjunctions ((x pseudo-term-list-listp)
                                     env)
  :verify-guards nil
  (if (atom x)
      t
    (and (tac-ev-clause (car x) env)
         (tac-ev-conj-of-disjunctions (cdr x) env))))

(define tac-ev-disj-of-conjunctions ((x pseudo-term-list-listp)
                                     env)
  :verify-guards nil
  (if (atom x)
      nil
    (or (tac-ev-cube (car x) env)
        (tac-ev-disj-of-conjunctions (cdr x) env))))

(define cube-to-singleton-clauses ((x pseudo-term-listp))
  :returns (new-x pseudo-term-list-listp)
  (if (atom x)
      nil
    (cons (list (pseudo-term-fix (car x)))
          (cube-to-singleton-clauses (cdr x))))
  ///
  (defret eval-of-<fn>
    (iff (tac-ev-conj-of-disjunctions new-x env)
         (tac-ev-cube x env))
    :hints(("Goal" :in-theory (enable tac-ev-conj-of-disjunctions
                                      tac-ev-clause
                                      tac-ev-cube))))

  (defret type-of-<fn>
    (implies (subsetp-equal (tac-termlist-types x ctx) (list (tac-type-fix type)))
             (tac-termlistlist-typed new-x type ctx))
    :hints(("Goal" :in-theory (enable tac-termlistlist-typed
                                      tac-termlist-types))))

  (defret vars-of-<fn>
    (acl2::set-equiv (termlistlist-vars new-x)
                     (cmr::termlist-vars x))
    :hints(("Goal" :in-theory (enable termlistlist-vars
                                      cmr::termlist-vars)))))

(define interpret-ruleres-branch-negative ((x tac-ruleres-branch-p))
  :returns (new-x pseudo-term-list-listp)
  (b* (((tac-ruleres-branch x)))
    (cons (list (pseudo-term-fncall 'pred-nonempty (list x.ctx-result)))
          (cube-to-singleton-clauses x.assums)))
  ///
  (defret eval-of-<fn>
    (iff (tac-ev-conj-of-disjunctions new-x env)
         (pred-nonempty (tac-eval-ruleres-branch x env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch
                                      tac-ev-conj-of-disjunctions
                                      tac-ev-clause))))

  (defret type-of-<fn>
    (implies (tac-ruleres-branch-typed x :set ctx)
             (tac-termlistlist-typed new-x :pred ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-typed
                                      tac-termlistlist-typed
                                      tac-termlist-types))))

  (defret vars-of-<fn>
    (implies (not (member-equal v (tac-ruleres-branch-vars x)))
             (not (member-equal v (termlistlist-vars new-x))))
    :hints(("Goal" :in-theory (enable termlistlist-vars
                                      cmr::termlist-vars
                                      cmr::term-vars
                                      tac-ruleres-branch-vars)))))

(define interpret-ruleres-branchlist-disjunction ((x tac-ruleres-branchlist-p))
  :returns (mv ok (new-x pseudo-term-listp))
  (b* (((when (atom x)) (mv t nil))
       ((tac-ruleres-branch x1) (car x))
       ((when (consp x1.assums)) (mv nil nil))
       ((mv ok rest) (interpret-ruleres-branchlist-disjunction (cdr x))))
    (mv ok (cons (pseudo-term-fncall 'pred-nonempty (list x1.ctx-result)) rest)))
  ///
  (defret eval-of-<fn>
    (implies ok
             (equal (tac-ev-clause new-x env)
                    (pred-nonempty
                     (union-list (tac-eval-ruleres-branchlist x env)))))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branchlist
                                      tac-eval-ruleres-branch
                                      union-list
                                      tac-ev-cube
                                      tac-ev-clause))))

  (defret type-of-<fn>
    (implies (tac-ruleres-branchlist-typed x :set ctx)
             (subsetp-equal (tac-termlist-types new-x ctx) '(:pred)))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-typed
                                      tac-ruleres-branch-typed
                                      tac-termlistlist-typed
                                      tac-termlist-types))))

  (defret vars-of-<fn>
    (implies (not (member-equal v (tac-ruleres-branchlist-vars x)))
             (not (member-equal v (cmr::termlist-vars new-x))))
    :hints(("Goal" :in-theory (enable cmr::termlist-vars
                                      cmr::term-vars
                                      tac-ruleres-branch-vars
                                      tac-ruleres-branchlist-vars)))))
    

(define interpret-ruleres-branchlist-negative ((x tac-ruleres-branchlist-p)) ;; disjunction of conjunctions
  :returns (mv ok (results pseudo-term-list-listp)) ;; conjunction of disjunctions
  (cond ((atom x) (mv t (list nil))) ;; false
        ((atom (cdr x)) (mv t (interpret-ruleres-branch-negative (car x))))
        (t (b* (((mv ok disj) (interpret-ruleres-branchlist-disjunction x)))
             (if ok
                 (mv t (list disj))
               (mv nil nil)))))
  ///
  (defret eval-of-<fn>
    (implies ok
             (iff (tac-ev-conj-of-disjunctions results env)
                  (pred-nonempty (union-list (tac-eval-ruleres-branchlist x env)))))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branchlist
                                      tac-ev-conj-of-disjunctions
                                      tac-ev-clause
                                      union-list))))

  (defret type-of-<fn>
    (implies (tac-ruleres-branchlist-typed x :set ctx)
             (tac-termlistlist-typed results :pred ctx))
    :hints(("Goal" :in-theory (enable tac-termlistlist-typed
                                      tac-ruleres-branchlist-typed
                                      tac-termlist-types))))

  (defret vars-of-<fn>
    (implies (not (member-equal v (tac-ruleres-branchlist-vars x)))
             (not (member-equal v (termlistlist-vars results))))
    :hints(("Goal" :in-theory (enable termlistlist-vars
                                      cmr::termlist-vars
                                      cmr::term-vars
                                      tac-ruleres-branch-vars
                                      tac-ruleres-branchlist-vars)))))




(define apply-a-rewrite-to-negative-assum ((x pseudo-termp)
                                           (assums1 pseudo-term-listp)
                                           (assums2 pseudo-term-listp)
                                           (substmap used-subst-map-p))
  ;; We want to either rewrite x with toplevel rewrite rules, which can replace
  ;; x with a conjunction of terms (which will actually cause a case split
  ;; since x is negated), or rewrite with negative contextual rewrites -- which
  ;; can return either a disjunction or a conjunction (but, we'll check, not a
  ;; disjunction of conjunctions). We'll synthesize both of these into a
  ;; conjunction of disjunctions, which (since x is negated) will be then
  ;; treated as a disjunction of conjunctions.
  :returns (mv ok
               (results pseudo-term-list-listp)
               (new-substmap used-subst-map-p))
  (b* (((mv ok results) (tac-toplevel-rewrite-apply-rules (tac-negative-toplevel-normalize-rules) x))
       ((when ok) (mv ok (cube-to-singleton-clauses results) (used-subst-map-fix substmap))))
    (pseudo-term-case x
      :fncall (if (eq x.fn 'pred-nonempty)
                  (b* ((set (first x.args))
                       (term-subst-db (cdr (hons-assoc-equal set (used-subst-map-fix substmap))))
                       ((mv ok results new-subst-db subst-db-updated)
                        (tac-apply-rule-in-context set assums1 assums2 (tac-negative-normalize-rules) term-subst-db))
                       ((unless ok) (mv nil nil (used-subst-map-fix substmap)))
                       ((mv ok results) (interpret-ruleres-branchlist-negative results))
                       ((unless ok) (mv nil nil (used-subst-map-fix substmap))))
                    (mv t results
                        (if subst-db-updated
                            (cons (cons set new-subst-db) (used-subst-map-fix substmap))
                          (used-subst-map-fix substmap))))
                (mv nil nil (used-subst-map-fix substmap)))
      :otherwise (mv nil nil (used-subst-map-fix substmap))))
  ///
  (defret eval-of-<fn>
    (implies (and ok
                  (tac-typed-env-p env ctx)
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums1)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums2)))
                  (equal (tac-term-type x ctx) :pred)
                  (subsetp-equal (tac-termlist-types assums1 ctx) '(:pred))
                  (subsetp-equal (tac-termlist-types assums2 ctx) '(:pred))
                  (tac-ev-cube assums1 env)
                  (tac-ev-cube assums2 env))
             (iff (tac-ev-conj-of-disjunctions results env)
                  (tac-ev x env)))
    :hints (("goal" :expand ((:free (x) (tac-ev-conj-of-disjunctions (list x) env))
                             (tac-ev-conj-of-disjunctions nil env)
                             (cmr::term-vars x)
                             (cmr::termlist-vars (pseudo-term-call->args x)))
             :in-theory (enable acl2::prefixp))))

  (defret type-of-<fn>
    (implies (and ok
                  (equal (tac-term-type x ctx) :pred)
                  (subsetp-equal (tac-termlist-types assums1 ctx) '(:pred))
                  (subsetp-equal (tac-termlist-types assums2 ctx) '(:pred))
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums1)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums2))))
             (tac-termlistlist-typed results :pred ctx))
    :hints(("Goal" :in-theory (enable acl2::prefixp)
            :expand ((tac-termlist-types (pseudo-term-call->args x) ctx)
                     (cmr::term-vars x)
                     (cmr::termlist-vars (pseudo-term-call->args x))))))

  (defret vars-of-<fn>
    (implies (and (not (member-equal v (cmr::term-vars x)))
                  (not (member-equal v (cmr::termlist-vars assums1)))
                  (not (member-equal v (cmr::termlist-vars assums2))))
             (not (member-equal v (termlistlist-vars results))))
    :hints(("Goal"
            :expand ((cmr::term-vars x)
                     (cmr::termlist-vars (pseudo-term-call->args x)))))))

(define termlist-negate ((x pseudo-term-listp))
  :returns (new-x pseudo-term-listp)
  (if (atom x)
      nil
    (cons (negate-lit (car x))
          (termlist-negate (cdr x))))
  ///
  (defret eval-cube-of-<fn>
    (iff (tac-ev-cube new-x env)
         (not (tac-ev-clause x env)))
    :hints(("Goal" :in-theory (enable tac-ev-clause
                                      tac-ev-cube))))
  
  (defret eval-clause-of-<fn>
    (iff (tac-ev-clause new-x env)
         (not (tac-ev-cube x env)))
    :hints(("Goal" :in-theory (enable tac-ev-clause
                                      tac-ev-cube))))

  (defret vars-of-<fn>
    (implies (not (member v (cmr::termlist-vars x)))
             (not (member v (cmr::termlist-vars new-x))))
    :hints(("Goal" :in-theory (enable cmr::termlist-vars))))

  (defret type-of-<fn>
    (implies (subsetp-equal (tac-termlist-types x ctx) '(:pred))
             (subsetp-equal (tac-termlist-types new-x ctx) '(:pred)))
    :hints(("Goal" :in-theory (enable tac-termlist-types)))))

(define termlistlist-negate ((x pseudo-term-list-listp))
  :returns (new-x pseudo-term-list-listp)
  (if (atom x)
      nil
    (cons (termlist-negate (car x))
          (termlistlist-negate (cdr x))))
  ///
  (defret tac-ev-conj-of-disjunctions-of-<fn>
    (iff (tac-ev-conj-of-disjunctions new-x env)
         (not (tac-ev-disj-of-conjunctions x env)))
    :hints(("Goal" :in-theory (enable tac-ev-disj-of-conjunctions
                                      tac-ev-conj-of-disjunctions))))

  (defret tac-ev-disj-of-conjunctions-of-<fn>
    (iff (tac-ev-disj-of-conjunctions new-x env)
         (not (tac-ev-conj-of-disjunctions x env)))
    :hints(("Goal" :in-theory (enable tac-ev-disj-of-conjunctions
                                      tac-ev-conj-of-disjunctions))))

  (defret vars-of-<fn>
    (implies (not (member v (termlistlist-vars x)))
             (not (member v (termlistlist-vars new-x))))
    :hints(("Goal" :in-theory (enable termlistlist-vars))))

  (defret type-of-<fn>
    (implies (tac-termlistlist-typed x :pred ctx)
             (tac-termlistlist-typed new-x :pred ctx))
    :hints(("Goal" :in-theory (enable tac-termlistlist-typed)))))



(define interpret-ruleres-branch-positive ((x tac-ruleres-branch-p))
  :returns (new-x pseudo-term-listp)
  (b* (((tac-ruleres-branch x)))
    (cons (pseudo-term-fncall 'pred-nonempty (list x.ctx-result))
          x.assums))
  ///
  (defret eval-of-<fn>
    (iff (tac-ev-cube new-x env)
         (pred-nonempty (tac-eval-ruleres-branch x env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch
                                      tac-ev-cube))))

  (defret type-of-<fn>
    (implies (tac-ruleres-branch-typed x :set ctx)
             (subsetp-equal (tac-termlist-types new-x ctx) '(:pred)))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-typed
                                      tac-termlistlist-typed
                                      tac-termlist-types))))

  (defret vars-of-<fn>
    (implies (not (member-equal v (tac-ruleres-branch-vars x)))
             (not (member-equal v (cmr::termlist-vars new-x))))
    :hints(("Goal" :in-theory (enable cmr::termlist-vars
                                      cmr::term-vars
                                      tac-ruleres-branch-vars)))))
    

(define interpret-ruleres-branchlist-positive ((x tac-ruleres-branchlist-p)) ;; disjunction of conjunctions
  :returns (results pseudo-term-list-listp) ;; conjunction of disjunctions
  (if (atom x)
      nil
    (cons (interpret-ruleres-branch-positive (car x))
          (interpret-ruleres-branchlist-positive (cdr x))))
  ///
  (defret eval-of-<fn>
    (iff (tac-ev-disj-of-conjunctions results env)
         (pred-nonempty (union-list (tac-eval-ruleres-branchlist x env))))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branchlist
                                      tac-ev-disj-of-conjunctions
                                      union-list))))

  (defret type-of-<fn>
    (implies (tac-ruleres-branchlist-typed x :set ctx)
             (tac-termlistlist-typed results :pred ctx))
    :hints(("Goal" :in-theory (enable tac-termlistlist-typed
                                      tac-ruleres-branchlist-typed
                                      tac-termlist-types))))

  (defret vars-of-<fn>
    (implies (not (member-equal v (tac-ruleres-branchlist-vars x)))
             (not (member-equal v (termlistlist-vars results))))
    :hints(("Goal" :in-theory (enable termlistlist-vars
                                      cmr::termlist-vars
                                      cmr::term-vars
                                      tac-ruleres-branch-vars
                                      tac-ruleres-branchlist-vars)))))

(define apply-a-rewrite-to-positive-assum ((x pseudo-termp))
  ;; We want to either rewrite x with toplevel rewrite rules, which can replace
  ;; x with a conjunction of terms (which will actually cause a case split
  ;; since x is negated), or rewrite with negative contextual rewrites -- which
  ;; can return either a disjunction or a conjunction (but, we'll check, not a
  ;; disjunction of conjunctions). We'll synthesize both of these into a
  ;; conjunction of disjunctions, which (since x is negated) will be then
  ;; treated as a disjunction of conjunctions.
  :returns (mv ok
               (results pseudo-term-list-listp))
  (pseudo-term-case x
    :fncall (if (eq x.fn 'pred-nonempty)
                (b* ((set (first x.args))
                     ((mv ok results & &)
                      (tac-apply-rule-in-context set nil nil (tac-positive-normalize-rules) nil))
                     ((unless ok) (mv nil nil)))
                  (mv t (interpret-ruleres-branchlist-positive results)))
              (mv nil nil))
    :otherwise (mv nil nil))
  ///
  (defret eval-of-<fn>
    (implies (and ok
                  (tac-typed-env-p env ctx)
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (equal (tac-term-type x ctx) :pred))
             (iff (tac-ev-disj-of-conjunctions results env)
                  (tac-ev x env)))
    :hints (("goal" :expand ((cmr::term-vars x)
                             (cmr::termlist-vars (pseudo-term-call->args x))
                             (tac-ev-cube nil env))
             :in-theory (enable acl2::prefixp))))

  (defret type-of-<fn>
    (implies (and ok
                  (equal (tac-term-type x ctx) :pred)
                  (not (member-equal 'tac-w (cmr::term-vars x))))
             (tac-termlistlist-typed results :pred ctx))
    :hints(("Goal" :in-theory (enable acl2::prefixp)
            :expand ((tac-termlist-types (pseudo-term-call->args x) ctx)
                     (cmr::term-vars x)
                     (cmr::termlist-vars (pseudo-term-call->args x))))))

  (defret vars-of-<fn>
    (implies (and (not (member-equal v (cmr::term-vars x))))
             (not (member-equal v (termlistlist-vars results))))
    :hints(("Goal"
            :expand ((cmr::term-vars x)
                     (cmr::termlist-vars (pseudo-term-call->args x)))))))
  


(define apply-a-rewrite-to-assum ((x pseudo-termp)
                                  (assums1 pseudo-term-listp)
                                  (assums2 pseudo-term-listp)
                                  (substmap used-subst-map-p))
  :returns (mv ok
               (results pseudo-term-list-listp)
               (new-substmap used-subst-map-p))
  (b* ((is-neg (is-negated-lit x))
       (atm (unnegated-lit x)))
    (if is-neg
        (b* (((mv ok results substmap) (apply-a-rewrite-to-negative-assum atm assums1 assums2 substmap))
             ((unless ok) (mv nil nil substmap)))
          (mv t (termlistlist-negate results) substmap))
      (b* (((mv ok results) (apply-a-rewrite-to-positive-assum atm))
           ((unless ok) (mv nil nil (used-subst-map-fix substmap))))
        (mv t results (used-subst-map-fix substmap)))))
  ///
  (defret eval-of-<fn>
    (implies (and ok
                  (tac-typed-env-p env ctx)
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums1)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums2)))
                  (equal (tac-term-type x ctx) :pred)
                  (subsetp-equal (tac-termlist-types assums1 ctx) '(:pred))
                  (subsetp-equal (tac-termlist-types assums2 ctx) '(:pred))
                  (tac-ev-cube assums1 env)
                  (tac-ev-cube assums2 env))
             (iff (tac-ev-disj-of-conjunctions results env)
                  (tac-ev x env)))
    :hints (("goal" :expand ((cmr::term-vars x)
                             (cmr::termlist-vars (pseudo-term-call->args x))
                             (tac-ev-cube nil env))
             :in-theory (enable acl2::prefixp))))

  (defret type-of-<fn>
    (implies (and ok
                  (equal (tac-term-type x ctx) :pred)
                  (subsetp-equal (tac-termlist-types assums1 ctx) '(:pred))
                  (subsetp-equal (tac-termlist-types assums2 ctx) '(:pred))
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums1)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums2))))
             (tac-termlistlist-typed results :pred ctx))
    :hints(("Goal" :in-theory (enable acl2::prefixp)
            :expand ((tac-termlist-types (pseudo-term-call->args x) ctx)
                     (cmr::term-vars x)
                     (cmr::termlist-vars (pseudo-term-call->args x))))))

  (defret vars-of-<fn>
    (implies (and (not (member-equal v (cmr::term-vars x)))
                  (not (member-equal v (cmr::termlist-vars assums1)))
                  (not (member-equal v (cmr::termlist-vars assums2))))
             (not (member-equal v (termlistlist-vars results))))
    :hints(("Goal"
            :expand ((cmr::term-vars x)
                     (cmr::termlist-vars (pseudo-term-call->args x)))))))

(local (defthm pseudo-term-listp-of-rev
         (implies (pseudo-term-listp x)
                  (pseudo-term-listp (acl2::rev x)))
         :hints(("Goal" :in-theory (enable acl2::rev)))))

(local (defthm tac-ev-cube-of-rev
         (iff (tac-ev-cube (acl2::rev x) env)
              (tac-ev-cube x env))
         :hints(("Goal" :in-theory (enable acl2::rev
                                           tac-ev-cube)))))

(local (defthm pseudo-term-list-fix-of-append
         (equal (pseudo-term-list-fix (append x y))
                (append (pseudo-term-list-fix x) (pseudo-term-list-fix y)))))

(local (defthm pseudo-term-list-fix-of-rev
         (equal (pseudo-term-list-fix (acl2::rev x))
                (acl2::rev (pseudo-term-list-fix x)))
         :hints(("Goal" :in-theory (enable acl2::rev)))))

(local (in-theory (disable pseudo-term-listp pseudo-termp)))

(local (defthm termlist-vars-of-rev
         (acl2::set-equiv (cmr::termlist-vars (acl2::rev x))
                          (cmr::termlist-vars x))
         :hints(("Goal" :in-theory (enable acl2::rev cmr::termlist-vars)))))

(local (defthm tac-termlist-types-of-rev
         (equal (tac-termlist-types (acl2::rev x) ctx)
                (acl2::rev (tac-termlist-types x ctx)))
         :hints(("Goal" :in-theory (enable acl2::rev tac-termlist-types)))))

(define add-assums-to-branches ((tail pseudo-term-listp)
                                (rev-head pseudo-term-listp)
                                (result pseudo-term-list-listp))
  :returns (new-res pseudo-term-list-listp
                    :hints(("Goal" :in-theory (enable pseudo-term-list-listp))))
  :guard-hints (("goal" :in-theory (enable pseudo-term-list-listp)))
  (if (atom result)
      nil
    (cons (pseudo-term-list-fix (revappend rev-head (append (car result) tail)))
          (add-assums-to-branches tail rev-head (cdr result))))
  ///
  (defret eval-of-<fn>
    (iff (tac-ev-disj-of-conjunctions new-res env)
         (and (tac-ev-cube tail env)
              (tac-ev-cube rev-head env)
              (tac-ev-disj-of-conjunctions result env)))
    :hints(("Goal" :in-theory (enable tac-ev-disj-of-conjunctions))))

  (defret vars-of-<fn>
    (implies (and (not (member-equal v (cmr::termlist-vars tail)))
                  (not (member-equal v (cmr::termlist-vars rev-head)))
                  (not (member-equal v (termlistlist-vars result))))
             (not (member-equal v (termlistlist-vars new-res))))
    :hints(("Goal" :in-theory (enable termlistlist-vars))))

  (defret type-of-<fn>
    (implies (and (subsetp-equal (tac-termlist-types tail ctx) '(:pred))
                  (subsetp-equal (tac-termlist-types rev-head ctx) '(:pred))
                  (tac-termlistlist-typed result :pred ctx))
             (tac-termlistlist-typed new-res :pred ctx))
    :hints(("Goal" :in-theory (enable tac-termlistlist-typed))))
             

  (local (in-theory (enable pseudo-term-list-fix))))


(define apply-a-rewrite-to-assums1 ((tail pseudo-term-listp)
                                    (rev-head pseudo-term-listp)
                                    (substmap used-subst-map-p))
  :returns (mv ok
               (results pseudo-term-list-listp)
               (new-substmap used-subst-map-p))
  (b* (((when (atom tail)) (mv nil
                               (list (revappend (pseudo-term-list-fix rev-head) nil))
                               (used-subst-map-fix substmap)))
       ((mv ok results substmap)
        (apply-a-rewrite-to-assum (car tail)
                                  (cdr tail) rev-head
                                  substmap))
       ((when ok)
        (mv t (add-assums-to-branches (cdr tail) rev-head results) substmap)))
    (apply-a-rewrite-to-assums1 (cdr tail)
                                (cons (pseudo-term-fix (car tail))
                                      rev-head)
                                substmap))
  ///
  (defret eval-of-<fn>
    (implies (and (tac-typed-env-p env ctx)
                  (not (member-equal 'tac-w (cmr::termlist-vars tail)))
                  (not (member-equal 'tac-w (cmr::termlist-vars rev-head)))
                  (subsetp-equal (tac-termlist-types tail ctx) '(:pred))
                  (subsetp-equal (tac-termlist-types rev-head ctx) '(:pred)))
             (iff (tac-ev-disj-of-conjunctions results env)
                  (and (tac-ev-cube tail env)
                       (tac-ev-cube rev-head env))))
    :hints (("goal" :in-theory (enable tac-termlist-types
                                       cmr::termlist-vars
                                       tac-ev-disj-of-conjunctions
                                       tac-ev-cube))))

  (defret type-of-<fn>
    (implies (and ok
                  (not (member-equal 'tac-w (cmr::termlist-vars tail)))
                  (not (member-equal 'tac-w (cmr::termlist-vars rev-head)))
                  (subsetp-equal (tac-termlist-types tail ctx) '(:pred))
                  (subsetp-equal (tac-termlist-types rev-head ctx) '(:pred)))
             (tac-termlistlist-typed results :pred ctx))
    :hints(("Goal" :in-theory (enable tac-termlist-types
                                       cmr::termlist-vars))))

  (defret vars-of-<fn>
    (implies (and (not (member-equal v (cmr::termlist-vars tail)))
                  (not (member-equal v (cmr::termlist-vars rev-head))))
             (not (member-equal v (termlistlist-vars results))))
    :hints(("Goal" :in-theory (enable cmr::termlist-vars
                                      termlistlist-vars)))))

(define apply-a-rewrite-to-assums ((assums pseudo-term-listp)
                                   (substmap used-subst-map-p))
  :returns (mv ok
               (results pseudo-term-list-listp)
               (new-substmap used-subst-map-p))
  (apply-a-rewrite-to-assums1 assums nil substmap)
  ///
  (defret eval-of-<fn>
    (implies (and (tac-typed-env-p env ctx)
                  (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred)))
             (iff (tac-ev-disj-of-conjunctions results env)
                  (tac-ev-cube assums env)))
    :hints(("Goal" :in-theory (enable tac-ev-cube))))

  (defret type-of-<fn>
    (implies (and ok
                  (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred)))
             (tac-termlistlist-typed results :pred ctx)))

  (defret vars-of-<fn>
    (implies (and (not (member-equal v (cmr::termlist-vars assums))))
             (not (member-equal v (termlistlist-vars results))))
    :hints(("Goal" :in-theory (enable cmr::termlist-vars
                                      termlistlist-vars)))))



       
                                  
