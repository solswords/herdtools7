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

(include-book "intro-rules")
(include-book "ruleresults")
(include-book "std/basic/two-nats-measure" :dir :system)
(local (include-book "common-thms"))
(local (include-book "std/lists/sets" :dir :system))
(local (std::add-default-post-define-hook :fix))



(define tac-fvi-check-hyps ((subst cmr::pseudo-term-subst-p)
                            (hyps pseudo-term-listp))
  (declare (ignorable subst))
  ;; FIXME check the base-rel/base-set hyps
  :returns (ok)
  (if (atom hyps)
      t
    (and (b* ((hyp (car hyps)))
           (pseudo-term-case hyp
             :fncall (or (eq hyp.fn 'base-rel-p)
                         (eq hyp.fn 'base-set-p))
             :otherwise nil))
         (tac-fvi-check-hyps subst (cdr hyps))))
  ///
  (defretd tac-ev-cube-of-hyps-when-<fn>
    (implies ok
             (tac-ev-cube hyps (tac-ev-alist subst env)))
    :hints(("Goal" :in-theory (enable tac-ev-cube)))))

(define tac-fvi-check-target ((target pseudo-termp)
                              (rule cmr::rewrite-p))
  :guard (tac-var-intro-rule-wellformed rule)
  :returns (mv ok (subst cmr::pseudo-term-subst-p))
  :guard-hints (("goal" :in-theory (enable tac-var-intro-rule-wellformed)))
  (b* (((cmr::rewrite rule))
       ((pseudo-term-fncall rule.lhs))
       (pat (second rule.lhs.args))
       ((mv ok subst)
        (cmr::term-unify-strict pat target nil))
       ((unless (tac-fvi-check-hyps subst rule.hyps)) (mv nil nil)))
    (mv ok subst)))


(local (defthmd tac-ev-of-pattern-by-alist
         (implies (cmr::term-unify-strict-ok pat arg alist)
                  (equal (tac-ev pat (tac-ev-alist (mv-nth 1 (cmr::term-unify-strict pat arg alist)) env))
                         (tac-ev arg env)))
         :hints(("Goal" :in-theory (e/d ()
                                        (tac-ev-of-term-subst-strict))
                 :use ((:instance CMR::TERM-UNIFY-STRICT-REVERSIBLE-IFF-RW
                        (pat pat) (x arg) (alist alist))
                       (:instance tac-ev-of-term-subst-strict
                        (x pat) (a (mv-nth 1 (cmr::term-unify-strict pat arg alist)))))))))




(local ;; also in pos-neg-apply-rule
 (defthm-tac-term-type-flag
   (defthm tac-term-type-of-cons-non-var
     (implies (not (member-equal v (cmr::term-vars x)))
              (equal (tac-term-type x (cons (cons v type) ctx))
                     (tac-term-type x ctx)))
     :hints ('(:expand ((cmr::term-vars x)
                        (:free (ctx) (tac-term-type x ctx)))))
     :flag tac-term-type)
   (defthm tac-termlist-types-of-cons-non-var
     (implies (not (member-equal v (cmr::termlist-vars x)))
              (equal (tac-termlist-types x (cons (cons v type) ctx))
                     (tac-termlist-types x ctx)))
     :hints ('(:expand ((cmr::termlist-vars x)
                        (:free (ctx) (tac-termlist-types x ctx)))))
     :flag tac-termlist-types)))


(local (defthm assoc-is-hons-assoc-equal
         (implies k
                  (equal (assoc k x)
                         (hons-assoc-equal k x)))))

(local (defthm prefixp-of-cons
         (equal (acl2::prefixp (cons a b) c)
                (And (consp c)
                     (equal (car c) a)
                     (acl2::prefixp b (cdr c))))
         :hints(("Goal" :in-theory (enable acl2::prefixp)))))


(local (defthmd tac-term-type-of-pattern-by-alist
         (implies (cmr::term-unify-strict-ok pat arg alist)
                  (equal (tac-term-type pat (tac-subst-ctx (mv-nth 1 (cmr::term-unify-strict pat arg alist)) ctx))
                         (tac-term-type arg ctx)))
         :hints(("Goal" :in-theory (e/d ()
                                        (tac-term-type-of-term-subst-strict))
                 :use ((:instance CMR::TERM-UNIFY-STRICT-REVERSIBLE-IFF-RW
                        (pat pat) (x arg) (alist alist))
                       (:instance tac-term-type-of-term-subst-strict
                        (x pat) (subst (mv-nth 1 (cmr::term-unify-strict pat arg alist)))))))))

(define tac-fvi-apply-rule ((rule cmr::rewrite-p)
                            (subst cmr::pseudo-term-subst-p)
                            (freevar pseudo-var-p))
  :guard (tac-var-intro-rule-wellformed rule)
  :returns (new-assum pseudo-termp)
  :prepwork ((local (in-theory (enable tac-var-intro-rule-wellformed))))
  (b* (((cmr::rewrite rule))
       ((pseudo-term-fncall rule.lhs))
       (subst (cons (cons (pseudo-term-var->name (first rule.lhs.args))
                          (pseudo-term-var freevar))
                    (cmr::pseudo-term-subst-fix subst))))
    (cmr::term-subst-strict rule.rhs subst))
  ///
  (defret <fn>-correct
    :pre-bind (((mv ok subst) (tac-fvi-check-target target rule)))
    (implies (and ok
                  (tac-var-intro-rule-wellformed rule)
                  (tac-ev-theoremp* (cmr::rewrite-term rule)))
             (iff (tac-ev new-assum env)
                  (pred-in-set (cdr (assoc (pseudo-var-fix freevar) env))
                               (tac-ev target env))))
    :hints(("Goal" :in-theory (e/d (tac-fvi-check-target
                                    tac-var-intro-rule-wellformed
                                    cmr::rewrite-term
                                    tac-ev-alist
                                    tac-ev-of-pattern-by-alist
                                    tac-ev-cube-of-hyps-when-tac-fvi-check-hyps)
                                   (tac-ev-theoremp*-implies))
            :use ((:instance tac-ev-theoremp*-implies
                   (x (cmr::rewrite-term rule))
                   (a (tac-ev-alist
                       (cons (cons (pseudo-term-var->name
                                    (first (pseudo-term-call->args
                                            (cmr::rewrite->lhs rule))))
                                   (pseudo-term-var freevar))
                             (mv-nth 1 (tac-fvi-check-target target rule)))
                       env)))))))

  (local (defthm term-unify-strict-ok-of-nil
           (iff (cmr::term-unify-strict-ok nil x alist)
                (pseudo-term-case x :null))
           :hints(("Goal" :in-theory (e/d (cmr::term-unify-strict-ok
                                           cmr::term-unify-strict)
                                          (cmr::term-unify-strict-reversible-iff-rw))))))
  (defret <fn>-typed
    :pre-bind (((mv ok subst) (tac-fvi-check-target target rule)))
    (implies (and ok
                  (tac-var-intro-rule-wellformed rule)
                  (tac-var-intro-rule-typed rule)
                  (equal (tac-term-type target ctx) :set)
                  (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar)
                                                (type-ctx-fix ctx)))
                         :event))
             (equal (tac-term-type new-assum ctx) :pred))
    :hints(("Goal" :in-theory (e/d (tac-fvi-check-target
                                    tac-var-intro-rule-wellformed
                                    tac-subst-ctx
                                    tac-var-intro-rule-typed
                                    acl2::prefixp
                                    tac-term-type-of-pattern-by-alist))
            :use ((:instance tac-var-intro-rule-typed-necc
                   (ctx (cons (cons (pseudo-term-var->name
                                      (first (pseudo-term-call->args
                                              (cmr::rewrite->lhs rule))))
                                    :event)
                              (tac-subst-ctx
                               (mv-nth 1 (tac-fvi-check-target target rule))
                               ctx))))))))

  (defret <fn>-vars
    :pre-bind (((mv ?ok subst) (tac-fvi-check-target target rule)))
    (implies (and (not (member v (cmr::term-vars target)))
                  (not (equal v (pseudo-var-fix freevar))))
             (not (member v (cmr::term-vars new-assum))))
    :hints(("Goal" :in-theory (e/d (tac-fvi-check-target
                                    cmr::term-subst-vars
                                    cmr::term-vars))))))

(define tac-fvi-try-rules ((rules tac-rewritelist-p)
                           (target pseudo-termp)
                           (freevar pseudo-var-p))
  :guard (tac-var-intro-rules-wellformed rules)
  :guard-hints (("goal" :in-theory (enable tac-var-intro-rules-wellformed)))
  :returns (mv ok (new-assum pseudo-termp))
  (b* (((when (atom rules)) (mv nil nil))
       ((unless (mbt (consp (car rules))))
        (tac-fvi-try-rules (cdr rules) target freevar))
       (rule (cdar rules))
       ((mv ok subst) (tac-fvi-check-target target rule))
       ((unless ok)
        (tac-fvi-try-rules (cdr rules) target freevar)))
    (mv t (tac-fvi-apply-rule rule subst freevar)))
  ///
  (defret <fn>-correct
    (implies (and ok
                  (tac-var-intro-rules-wellformed rules)
                  (tac-ev-theoremlist-p (tac-rewritelist-terms rules)))
             (iff (tac-ev new-assum env)
                  (pred-in-set (cdr (assoc (pseudo-var-fix freevar) env))
                               (tac-ev target env))))
    :hints(("Goal" :in-theory (enable tac-var-intro-rules-wellformed
                                      tac-ev-theoremlist-p
                                      tac-rewritelist-terms))))

  (defret <fn>-typed
    (implies (and ok
                  (tac-var-intro-rules-wellformed rules)
                  (tac-var-intro-rules-typed rules)
                  (equal (tac-term-type target ctx) :set)
                  (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar)
                                                (type-ctx-fix ctx)))
                         :event))
             (equal (tac-term-type new-assum ctx) :pred))
    :hints(("Goal" :in-theory (enable tac-var-intro-rules-typed
                                      tac-var-intro-rules-wellformed))))

  (defret <fn>-vars
    (implies (and (not (member v (cmr::term-vars target)))
                  (not (equal v (pseudo-var-fix freevar))))
             (not (member v (cmr::term-vars new-assum)))))

  (local (in-theory (enable tac-rewritelist-fix))))


(local (defthm pseudo-term-count-of-nth-lte-list
         (<= (pseudo-term-count (nth n x))
             (pseudo-term-list-count x))
         :hints (("goal" :induct (nth n x)
                  :expand ((pseudo-term-list-count x))))
         :rule-classes :linear))

(local (defthm pseudo-term-count-of-nth-when-fncall
         (implies (pseudo-term-case x :fncall)
                  (< (pseudo-term-count (nth n (pseudo-term-call->args x)))
                     (pseudo-term-count x)))
         :hints (("goal" :expand ((pseudo-term-count x))))
         :rule-classes :linear))

(local (defthm pseudo-termp-of-nth
         (implies (pseudo-term-listp x)
                  (pseudo-termp (nth n x)))))




(cmr::defthm-term-vars-flag
  (defthm tac-term-type-of-cons-same
    (implies (tac-type-equiv typ (cdr (hons-assoc-equal v ctx)))
             (equal (tac-term-type x (cons (cons v typ) ctx))
                    (tac-term-type x ctx)))
    :hints ('(:expand ((cmr::term-vars x)
                       (:free (ctx) (tac-term-type x ctx)))))
    :flag cmr::term-vars)
  (defthm tac-termlist-types-of-cons-same
    (implies (tac-type-equiv typ (cdr (hons-assoc-equal v ctx)))
             (equal (tac-termlist-types x (cons (cons v typ) ctx))
                    (tac-termlist-types x ctx)))
    :hints ('(:expand ((cmr::termlist-vars x)
                       (:free (ctx) (tac-termlist-types x ctx)))))
    :flag cmr::termlist-vars))


(local (defthm tac-term-type-of-tac-subst-ctx-unify
         (b* (((mv ok subst) (cmr::term-unify-strict pat target nil)))
           (implies ok
                    (equal (tac-term-type pat (tac-subst-ctx subst ctx))
                           (tac-term-type target ctx))))
         :hints (("goal" :use ((:instance tac-term-type-of-term-subst-strict
                                (x pat)
                                (subst (mv-nth 1 (cmr::term-unify-strict pat target nil)))))
                  :in-theory (disable tac-term-type-of-term-subst-strict)))))

(local (defthm member-var-name-nth
         (implies (< (nfix n) (len lst))
                  (member-equal (pseudo-term-var->name (nth n lst))
                                (cmr::pseudo-term-var-list->names lst)))
         :hints(("Goal" :in-theory (enable nth cmr::pseudo-term-var-list->names)))))


(local (defthm TAC-INTERSECT-PROPAGATE-RULE->TARGET-FN-when-unify
         (implies (and (cmr::term-unify-strict-ok
                        (tac-intersect-propagate-rule->target-pattern rule)
                        target nil)
                       (pseudo-term-case (tac-intersect-propagate-rule->target-pattern rule) :fncall))
                  (equal (tac-intersect-propagate-rule->target-fn rule)
                         (pseudo-term-fncall->fn target)))
         :hints(("Goal" :in-theory (e/d (tac-intersect-propagate-rule->target-fn
                                         tac-intersect-propagate-rule->target-pattern
                                         cmr::term-unify-strict-ok)
                                        (cmr::term-unify-strict-reversible-iff-rw))
                 :expand ((:free (pat) (cmr::term-unify-strict pat target nil)))))))

;; (local (defthm lookup-of-tac-subst-ctx
;;          (equal (hons-assoc-equal v (tac-subst-ctx subst ctx))
;;                 (let ((look (hons-assoc-equal v (cmr::pseudo-term-subst-fix subst))))
;;                   (and look
;;                        (cons v (tac-term-type (cdr look) ctx)))))
;;          :hints(("Goal" :in-theory (enable tac-subst-ctx)))))

(local (defthmd tac-function-return-type-when-tac-term-type
         (implies (and (tac-term-type x ctx)
                       (equal (pseudo-term-kind x) :fncall))
                  (equal (tac-function-return-type (pseudo-term-fncall->fn x))
                         (tac-term-type x ctx)))
         :hints(("Goal" :expand ((tac-term-type x ctx))))))

(defines tac-fvi-rewrite
  (define tac-fvi-rewrite ((target pseudo-termp)
                           (type tac-type-p)
                           (freevar pseudo-var-p))
    :verify-guards nil
    :measure (acl2::nat-list-measure (list (pseudo-term-count target) 1 0))
    :returns (mv ok
                 (new-target pseudo-termp)
                 (new-assum pseudo-termp))
    (b* (((mv rw-ok new-assum)
          (if (eq (tac-type-fix type) :set)
              (tac-fvi-try-rules (tac-var-intro-rules) target freevar)
            (mv nil nil)))
         ((when rw-ok)
          (mv t
              (pseudo-term-call 'singleton (list (pseudo-term-var freevar)))
              new-assum))
         ((unless (and (pseudo-term-case target :fncall)
                       (or (eq (tac-type-fix type) :set)
                           (eq (tac-type-fix type) :rel))))
          (mv nil nil nil))
         (prop-rules (cdr (hons-assoc-equal
                           (pseudo-term-fncall->fn target)
                           (tac-intersect-propagate-table))))
         ((unless prop-rules)
          (mv nil nil nil)))
      (tac-fvi-rewrite-propagates prop-rules target freevar)))

  (define tac-fvi-rewrite-propagates ((prop-rules tac-rewritelist-p)
                                      (target pseudo-termp)
                                      (freevar pseudo-var-p))
    :measure (acl2::nat-list-measure (list (pseudo-term-count target) 0 (len prop-rules)))
    :returns (mv ok
                 (new-target pseudo-termp)
                 (new-assum pseudo-termp))
    :guard (tac-intersect-propagate-rules-wellformed prop-rules)
    (b* (((when (atom prop-rules)) (mv nil nil nil))
         ((unless (mbt (consp (car prop-rules))))
          (tac-fvi-rewrite-propagates (cdr prop-rules) target freevar))
         ((mv ok new-target new-assum)
          (tac-fvi-rewrite-propagate (cdar prop-rules) target freevar))
         ((when ok) (mv ok new-target new-assum)))
      (tac-fvi-rewrite-propagates (cdr prop-rules) target freevar)))

  (define tac-fvi-rewrite-propagate ((rule cmr::rewrite-p)
                                      (target pseudo-termp)
                                      (freevar pseudo-var-p))
    :measure (acl2::nat-list-measure (list (pseudo-term-count target) 0 0))
    :returns (mv ok
                 (new-target pseudo-termp)
                 (new-assum pseudo-termp))
    :guard (tac-intersect-propagate-rule-wellformed rule)
    (b* ((pat (tac-intersect-propagate-rule->target-pattern rule))
         ((mv ok subst) (cmr::term-unify-strict pat target nil))
         ((unless ok) (mv nil nil nil))
         ((unless (mbt (pseudo-term-case target :fncall)))
          (mv nil nil nil))
         (desc-pos (tac-intersect-propagate-rule->descent-pos rule))
         (desc-var (pseudo-term-var->name (nth desc-pos (pseudo-term-call->args pat))))
         (desc-term (nth desc-pos (pseudo-term-call->args target)))
         (desc-type (tac-intersect-propagate-rule->result-type rule))
         ((mv ok new-target new-assum)
          (tac-fvi-rewrite desc-term desc-type freevar))
         ((unless ok)
          (mv nil nil nil))
         (full-new-target (cmr::term-subst-strict pat
                                                  (cons (cons desc-var new-target) subst))))
      (mv t full-new-target new-assum)))
  ///
  (verify-guards tac-fvi-rewrite
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (subst)
                             (cmr::term-subst-strict
                              (tac-intersect-propagate-rule->target-pattern rule) subst))
                            (tac-intersect-propagate-rules-wellformed prop-rules))))))

  (local (in-theory (enable tac-rewritelist-fix)))
  (fty::deffixequiv-mutual tac-fvi-rewrite))




(local (defthm tac-ev-of-tac-ev-alist-unify
         (b* (((mv ok subst) (cmr::term-unify-strict pat target nil)))
           (implies ok
                    (equal (tac-ev pat (tac-ev-alist subst env))
                           (tac-ev target env))))
         :hints (("goal" :use ((:instance tac-ev-of-term-subst-strict
                                (x pat)
                                (a (mv-nth 1 (cmr::term-unify-strict pat target nil)))))
                  :in-theory (disable tac-ev-of-term-subst-strict)))))
                

(defines tac-fvi-rewrite*
  (define tac-fvi-rewrite* ((target pseudo-termp)
                            (intersect pseudo-termp)
                            (type tac-type-p)
                            (freevar pseudo-var-p))
    :verify-guards nil
    :measure (acl2::nat-list-measure (list (pseudo-term-count target) 1 0))
    :returns (mv ok
                 (new-target pseudo-termp)
                 (new-assum pseudo-termp)
                 (witness-term pseudo-termp))
    (b* (((mv rw-ok new-assum)
          (if (eq (tac-type-fix type) :set)
              (tac-fvi-try-rules (tac-var-intro-rules) target freevar)
            (mv nil nil)))
         ((when rw-ok)
          (mv t
              (pseudo-term-call 'singleton (list (pseudo-term-var freevar)))
              new-assum
              (pseudo-term-call
               'nonempty-witness
               (list (pseudo-term-call
                      'setintersect (list (pseudo-term-fix intersect)
                                          (pseudo-term-fix target)))))))
         ((unless (and (pseudo-term-case target :fncall)
                       (or (eq (tac-type-fix type) :set)
                           (eq (tac-type-fix type) :rel))))
          (mv nil nil nil nil))
         (prop-rules (cdr (hons-assoc-equal
                           (pseudo-term-fncall->fn target)
                           (tac-intersect-propagate-table))))
         ((unless prop-rules)
          (mv nil nil nil nil)))
      (tac-fvi-rewrite*-propagates prop-rules target intersect type freevar)))

  (define tac-fvi-rewrite*-propagates ((prop-rules tac-rewritelist-p)
                                       (target pseudo-termp)
                                       (intersect pseudo-termp)
                                       (type tac-type-p)
                                       (freevar pseudo-var-p))
    :measure (acl2::nat-list-measure (list (pseudo-term-count target) 0 (len prop-rules)))
    :returns (mv ok
                 (new-target pseudo-termp)
                 (new-assum pseudo-termp)
                 (witness-term pseudo-termp))
    :guard (tac-intersect-propagate-rules-wellformed prop-rules)
    (b* (((when (atom prop-rules)) (mv nil nil nil nil))
         ((unless (mbt (consp (car prop-rules))))
          (tac-fvi-rewrite*-propagates (cdr prop-rules) target intersect type freevar))
         ((mv ok new-target new-assum witness-term)
          (tac-fvi-rewrite*-propagate (cdar prop-rules) target intersect type freevar))
         ((when ok) (mv ok new-target new-assum witness-term)))
      (tac-fvi-rewrite*-propagates (cdr prop-rules) target intersect type freevar)))

  (define tac-fvi-rewrite*-propagate ((rule cmr::rewrite-p)
                                      (target pseudo-termp)
                                      (intersect pseudo-termp)
                                      (type tac-type-p)
                                      (freevar pseudo-var-p))
    :measure (acl2::nat-list-measure (list (pseudo-term-count target) 0 0))
    :returns (mv ok
                 (new-target pseudo-termp)
                 (new-assum pseudo-termp)
                 (witness-term pseudo-termp))
    :guard (tac-intersect-propagate-rule-wellformed rule)
    (declare (ignorable type))
    (b* ((pat (tac-intersect-propagate-rule->target-pattern rule))
         ((mv ok subst) (cmr::term-unify-strict pat target nil))
         ((unless ok) (mv nil nil nil nil))
         ((unless (mbt (pseudo-term-case target :fncall)))
          (mv nil nil nil nil))
         (desc-intersect (cmr::term-subst-strict
                          (tac-intersect-propagate-rule->intersect-term rule)
                          (cons (cons (tac-intersect-propagate-rule->intersect-var rule)
                                      (pseudo-term-fix intersect))
                                subst)))
         (desc-pos (tac-intersect-propagate-rule->descent-pos rule))
         (desc-var (pseudo-term-var->name (nth desc-pos (pseudo-term-call->args pat))))
         (desc-term (nth desc-pos (pseudo-term-call->args target)))
         (desc-type (tac-intersect-propagate-rule->result-type rule))
         ((mv ok new-target new-assum witness-term)
          (tac-fvi-rewrite* desc-term desc-intersect desc-type freevar))
         ((unless ok)
          (mv nil nil nil nil))
         (full-new-target (cmr::term-subst-strict pat
                                                  (cons (cons desc-var new-target) subst))))
      (mv t full-new-target new-assum witness-term)))
  ///
  (verify-guards tac-fvi-rewrite*
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (subst)
                             (cmr::term-subst-strict
                              (tac-intersect-propagate-rule->target-pattern rule) subst))
                            (tac-intersect-propagate-rules-wellformed prop-rules))))))

  (std::defret-mutual tac-fvi-rewrite*-typed
    (defret <fn>-typed
      (implies (and ok
                    (eq (tac-term-type target ctx)
                        (tac-type-fix type)))
               (and (implies (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar)
                                                           (type-ctx-fix ctx)))
                                    :event)
                             (and (equal (tac-term-type new-assum ctx) :pred)
                                  (equal (tac-term-type new-target ctx)
                                         (tac-term-type target ctx))))
                    (implies (equal (tac-term-type intersect ctx) (tac-type-fix type))
                             (equal (tac-term-type witness-term ctx) :event))))
      :hints ('(:expand (<call>)
                :in-theory (enable acl2::prefixp)))
      :fn tac-fvi-rewrite*)
    (defret <fn>-typed
      (implies (and ok
                    (tac-intersect-propagate-rules-wellformed prop-rules)
                    (tac-intersect-propagate-rules-typed prop-rules)
                    (tac-term-type target ctx))
               (and (implies (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar)
                                                           (type-ctx-fix ctx)))
                                    :event)
                             (and (equal (tac-term-type new-assum ctx) :pred)
                                  (equal (tac-term-type new-target ctx)
                                         (tac-term-type target ctx))))
                    (implies (and (equal (tac-term-type intersect ctx) (tac-type-fix type))
                                  (equal (tac-term-type target ctx) (tac-type-fix type)))
                             (equal (tac-term-type witness-term ctx) :event))))
      :hints ('(:expand (<call>)
                :in-theory (enable TAC-INTERSECT-PROPAGATE-RULES-WELLFORMED
                                   TAC-INTERSECT-PROPAGATE-RULES-typed)))
      :fn tac-fvi-rewrite*-propagates)
    (defret <fn>-typed
      (implies (and ok
                    (tac-intersect-propagate-rule-wellformed rule)
                    (tac-intersect-propagate-rule-typed rule)
                    (tac-term-type target ctx))
               (and (implies (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar)
                                                           (type-ctx-fix ctx)))
                                    :event)
                             (and (equal (tac-term-type new-assum ctx) :pred)
                                  (equal (tac-term-type new-target ctx)
                                         (tac-term-type target ctx))))
                    (implies (and (equal (tac-term-type intersect ctx) (tac-type-fix type))
                                  (equal (tac-term-type target ctx) (tac-type-fix type)))
                             (equal (tac-term-type witness-term ctx) :event))))
      :hints ('(:expand (<call>
                         (:free (x y) (tac-subst-ctx (cons x y) ctx)))
                :in-theory (e/d (LOOKUP-OF-NTH-VAR-IN-PATTERN-IN-SUBST)
                                (cmr::pseudo-term-var-list->names-when-pseudo-term-listp
                                 ;; lookup-of-tac-subst-ctx
                                 ))))
      :fn tac-fvi-rewrite*-propagate))

  (local (defthm member-term-vars-of-nth-lst
           (implies (not (member-equal v (cmr::termlist-vars lst)))
                    (not (member-equal v (cmr::term-vars (nth n lst)))))
           :hints(("Goal" :in-theory (enable cmr::termlist-vars nth)))))

  (local (defthm member-term-vars-of-nth-args
           (implies (not (member-equal v (cmr::term-vars x)))
                    (not (member-equal v (cmr::term-vars (nth n (pseudo-term-call->args x))))))
           :hints(("Goal" :expand ((cmr::term-vars x)))
                  (and stable-under-simplificationp
                       '(:in-theory (enable pseudo-term-call->args))))))
  
  

  (std::defret-mutual tac-fvi-rewrite*-vars
    (defret <fn>-vars
      (implies (and (not (member-equal v (cmr::term-vars target)))
                    )
               (and (implies (not (equal v (pseudo-var-fix freevar)))
                             (and (not (member-equal v (cmr::term-vars new-target)))
                                  (not (member-equal v (cmr::term-vars new-assum)))))
                    (implies (not (member-equal v (cmr::term-vars intersect)))
                             (not (member-equal v (cmr::term-vars witness-term))))))
      :hints ('(:expand (<call>
                         (:free (fn args) (cmr::term-vars (pseudo-term-fncall fn args)))
                         (cmr::term-vars (pseudo-term-var freevar))
                         (:free (x y) (cmr::termlist-vars (cons x y))))))
      :fn tac-fvi-rewrite*)
    (defret <fn>-vars
      (implies (not (member-equal v (cmr::term-vars target)))
               (and (implies (not (equal v (pseudo-var-fix freevar)))
                             (and (not (member-equal v (cmr::term-vars new-target)))
                                  (not (member-equal v (cmr::term-vars new-assum)))))
                    (implies (not (member-equal v (cmr::term-vars intersect)))
                             (not (member-equal v (cmr::term-vars witness-term))))))
      :hints ('(:expand (<call>)
                :in-theory (enable TAC-INTERSECT-PROPAGATE-RULES-WELLFORMED
                                   TAC-INTERSECT-PROPAGATE-RULES-typed)))
      :fn tac-fvi-rewrite*-propagates)
    (defret <fn>-vars
      (implies (and (not (member-equal v (cmr::term-vars target))))
               (and (implies (not (equal v (pseudo-var-fix freevar)))
                             (and (not (member-equal v (cmr::term-vars new-target)))
                                  (not (member-equal v (cmr::term-vars new-assum)))))
                    (implies (not (member-equal v (cmr::term-vars intersect)))
                             (not (member-equal v (cmr::term-vars witness-term))))))
      :hints ('(:expand (<call>
                         (:free (x y) (cmr::term-subst-vars (cons x y))))))
      :fn tac-fvi-rewrite*-propagate))

  (local (defthm pred-set-intersects-of-singleton
           (iff (pred-set-intersects x (singleton e))
                (pred-in-set e x))
           :hints(("Goal" :in-theory (e/d (pred-set-intersects
                                           setintersect
                                           emptyp-in-terms-of-nonempty-witness)
                                          (set::never-in-empty))
                   :use ((:instance set::never-in-empty
                          (a (event-fix e))
                          (x (setintersect x (singleton e)))))))))

  (local (defthm not-in-set-when-not-intersects
           (implies (and (not (pred-set-intersects x y))
                         (pred-in-set e y))
                    (not (pred-in-set e x)))
           :hints(("Goal" :in-theory (e/d (pred-set-intersects
                                           pred-in-set)
                                          (set::never-in-empty))
                   :use ((:instance set::never-in-empty
                          (a (event-fix e))
                          (x (setintersect x y))))))))

  (local (defthm pred-in-set-of-nonempty-witness-when-intersects
           (implies (and (equal e (nonempty-witness (setintersect x y)))
                         (pred-set-intersects x y))
                    (and (pred-in-set e x)
                         (pred-in-set e y)))
           :hints(("Goal" :in-theory (enable pred-set-intersects
                                             pred-in-set
                                             emptyp-in-terms-of-nonempty-witness)))))

  (local (in-theory (disable pred-set-intersects
                             pred-rel-intersects
                             member-equal
                             nth
                             hons-assoc-equal
                             tac-ev-of-cons-non-var
                             tac-ev-when-pseudo-term-fncall
                             tac-ev-alist
                             HONS-ASSOC-EQUAL-OF-TYPE-CTX-FIX
                             (:d tac-fvi-rewrite*)
                             (:d tac-fvi-rewrite*-propagate)
                             (:d tac-fvi-rewrite*-propagates))))
  
  (std::defret-mutual tac-fvi-rewrite*-correct
    (defret <fn>-correct
      (implies (and ok
                    (tac-typed-env-p env ctx) 
                    (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar)
                                                  (type-ctx-fix ctx)))
                           :event)
                    (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar) env))
                           (tac-ev witness-term env))
                    (eq (tac-term-type target ctx)
                        (tac-type-fix type)))
               (and (implies (eq (tac-type-fix type) :set)
                             (iff (pred-set-intersects
                                   (tac-ev intersect env)
                                   (tac-ev target env))
                                  (and
                                   (tac-ev new-assum env)
                                   (pred-set-intersects
                                    (tac-ev intersect env)
                                    (tac-ev new-target env)))))
                    (implies (not (eq (tac-type-fix type) :set))
                             (iff (pred-rel-intersects
                                   (tac-ev intersect env)
                                   (tac-ev target env))
                                  (and
                                   (tac-ev new-assum env)
                                   (pred-rel-intersects
                                    (tac-ev intersect env)
                                    (tac-ev new-target env)))))))
      :hints ('(:expand (<call>)
                :in-theory (e/d (acl2::prefixp)
                                (pred-in-set))))
      :fn tac-fvi-rewrite*
      :rule-classes nil)
    (defret <fn>-correct
      (implies (and ok
                    (tac-typed-env-p env ctx)
                    (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar)
                                                  (type-ctx-fix ctx)))
                           :event)
                    (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar) env))
                           (tac-ev witness-term env))                           
                    (tac-intersect-propagate-rules-wellformed prop-rules)
                    (tac-intersect-propagate-rules-typed prop-rules)
                    (tac-ev-theoremlist-p (tac-rewritelist-terms prop-rules))
                    (eq (tac-term-type target ctx)
                        (tac-type-fix type)))
               (and (implies (eq (tac-type-fix type) :set)
                             (iff (pred-set-intersects
                                   (tac-ev intersect env)
                                   (tac-ev target env))
                                  (and
                                   (tac-ev new-assum env)
                                   (pred-set-intersects
                                    (tac-ev intersect env)
                                    (tac-ev new-target env)))))
                    (implies (eq (tac-type-fix type) :rel)
                             (iff (pred-rel-intersects
                                   (tac-ev intersect env)
                                   (tac-ev target env))
                                  (and
                                   (tac-ev new-assum env)
                                   (pred-rel-intersects
                                    (tac-ev intersect env)
                                    (tac-ev new-target env)))))))
      :hints ('(:expand (<call>)
                :in-theory (enable TAC-INTERSECT-PROPAGATE-RULES-WELLFORMED
                                   TAC-INTERSECT-PROPAGATE-RULES-typed
                                   tac-ev-theoremlist-p
                                   tac-rewritelist-terms)))
      :fn tac-fvi-rewrite*-propagates
      :rule-classes nil)
    (defret <fn>-correct
      (implies (and ok
                    (tac-typed-env-p env ctx)
                    (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar)
                                                  (type-ctx-fix ctx)))
                           :event)
                    (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar) env))
                           (tac-ev witness-term env))
                    (tac-intersect-propagate-rule-wellformed rule)
                    (tac-intersect-propagate-rule-typed rule)
                    (tac-ev-theoremp* (cmr::rewrite-term rule))
                    (eq (tac-term-type target ctx)
                        (tac-type-fix type)))
               (and (implies (eq (tac-type-fix type) :set)
                             (iff (pred-set-intersects
                                   (tac-ev intersect env)
                                   (tac-ev target env))
                                  (and
                                   (tac-ev new-assum env)
                                   (pred-set-intersects
                                    (tac-ev intersect env)
                                    (tac-ev new-target env)))))
                    (implies (eq (tac-type-fix type) :rel)
                             (iff (pred-rel-intersects
                                   (tac-ev intersect env)
                                   (tac-ev target env))
                                  (and
                                   (tac-ev new-assum env)
                                   (pred-rel-intersects
                                    (tac-ev intersect env)
                                    (tac-ev new-target env)))))))
      :hints ('(:expand (<call>
                         (:free (x y) (tac-ev-alist (cons x y) env)))
                :in-theory (e/d (tac-function-return-type-when-tac-term-type)
                                (TAC-TERM-TYPE-WHEN-FNCALL-WITH-RETURN-TYPE))
                :use ((:instance tac-intersect-propagate-rule-wellformed-implies-can-rewrite-inner2
                       (rule rule)
                       (arg target)
                       (w (tac-ev intersect env))
                       (desc-new-val
                        (b* ((pat (tac-intersect-propagate-rule->target-pattern rule))
                             ((mv ?ok subst) (cmr::term-unify-strict pat target nil))
                             (desc-intersect (cmr::term-subst-strict
                                              (tac-intersect-propagate-rule->intersect-term rule)
                                              (cons (cons (tac-intersect-propagate-rule->intersect-var rule)
                                                          (pseudo-term-fix intersect))
                                                    subst)))
                             (desc-pos (tac-intersect-propagate-rule->descent-pos rule))
                             (desc-var (pseudo-term-var->name (nth desc-pos (pseudo-term-call->args pat))))
                             (desc-term (nth desc-pos (pseudo-term-call->args target)))
                             (desc-type (tac-intersect-propagate-rule->result-type rule))
                             ((mv ok new-target new-assum witness-term)
                              (tac-fvi-rewrite* desc-term desc-intersect desc-type freevar)))
                          (tac-ev new-target env)))
                       (new-assum
                        (b* ((pat (tac-intersect-propagate-rule->target-pattern rule))
                             ((mv ?ok subst) (cmr::term-unify-strict pat target nil))
                             (desc-intersect (cmr::term-subst-strict
                                              (tac-intersect-propagate-rule->intersect-term rule)
                                              (cons (cons (tac-intersect-propagate-rule->intersect-var rule)
                                                          (pseudo-term-fix intersect))
                                                    subst)))
                             (desc-pos (tac-intersect-propagate-rule->descent-pos rule))
                             (desc-var (pseudo-term-var->name (nth desc-pos (pseudo-term-call->args pat))))
                             (desc-term (nth desc-pos (pseudo-term-call->args target)))
                             (desc-type (tac-intersect-propagate-rule->result-type rule))
                             ((mv ok new-target new-assum witness-term)
                              (tac-fvi-rewrite* desc-term desc-intersect desc-type freevar)))
                          (tac-ev new-assum env)))))
                :do-not-induct t))
      :fn tac-fvi-rewrite*-propagate
      :rule-classes nil))


  (std::defret-mutual tac-fvi-rewrite*-eval-implies-orig
    (defret <fn>-eval-implies-orig
      (implies (and ok
                    (tac-typed-env-p env ctx) 
                    ;; (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar)
                    ;;                               (type-ctx-fix ctx)))
                    ;;        :event)
                    ;; (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar) env))
                    ;;        (tac-ev witness-term env))
                    (eq (tac-term-type target ctx)
                        (tac-type-fix type)))
               (and (implies (eq (tac-type-fix type) :set)
                             (implies (and
                                       (tac-ev new-assum env)
                                       (pred-set-intersects
                                        (tac-ev intersect env)
                                        (tac-ev new-target env)))
                                      (pred-set-intersects
                                       (tac-ev intersect env)
                                       (tac-ev target env))))
                    (implies (not (eq (tac-type-fix type) :set))
                             (implies (and
                                       (tac-ev new-assum env)
                                       (pred-rel-intersects
                                        (tac-ev intersect env)
                                        (tac-ev new-target env)))
                                  (pred-rel-intersects
                                       (tac-ev intersect env)
                                       (tac-ev target env))))))
      :hints ('(:expand (<call>)
                :in-theory (e/d (acl2::prefixp)
                                (pred-in-set))))
      :fn tac-fvi-rewrite*
      :rule-classes nil)
    (defret <fn>-eval-implies-orig
      (implies (and ok
                    (tac-typed-env-p env ctx)
                    ;; (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar)
                    ;;                               (type-ctx-fix ctx)))
                    ;;        :event)
                    ;; (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar) env))
                    ;;        (tac-ev witness-term env))
                    
                    (tac-intersect-propagate-rules-wellformed prop-rules)
                    (tac-intersect-propagate-rules-typed prop-rules)
                    (tac-ev-theoremlist-p (tac-rewritelist-terms prop-rules))
                    (eq (tac-term-type target ctx)
                        (tac-type-fix type)))
               (and (implies (eq (tac-type-fix type) :set)
                             (implies (and
                                       (tac-ev new-assum env)
                                       (pred-set-intersects
                                        (tac-ev intersect env)
                                        (tac-ev new-target env)))
                                      (pred-set-intersects
                                       (tac-ev intersect env)
                                       (tac-ev target env))))
                    (implies (eq (tac-type-fix type) :rel)
                             (implies (and
                                       (tac-ev new-assum env)
                                       (pred-rel-intersects
                                        (tac-ev intersect env)
                                        (tac-ev new-target env)))
                                      (pred-rel-intersects
                                       (tac-ev intersect env)
                                       (tac-ev target env))))))
      :hints ('(:expand (<call>)
                :in-theory (enable TAC-INTERSECT-PROPAGATE-RULES-WELLFORMED
                                   TAC-INTERSECT-PROPAGATE-RULES-typed
                                   tac-ev-theoremlist-p
                                   tac-rewritelist-terms)))
      :fn tac-fvi-rewrite*-propagates
      :rule-classes nil)
    (defret <fn>-eval-implies-orig
      (implies (and ok
                    (tac-typed-env-p env ctx)
                    ;; (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar)
                    ;;                               (type-ctx-fix ctx)))
                    ;;        :event)
                    (tac-intersect-propagate-rule-wellformed rule)
                    (tac-intersect-propagate-rule-typed rule)
                    (tac-ev-theoremp* (cmr::rewrite-term rule))
                    (eq (tac-term-type target ctx)
                        (tac-type-fix type)))
               (and (implies (eq (tac-type-fix type) :set)
                             (implies (and
                                       (tac-ev new-assum env)
                                       (pred-set-intersects
                                        (tac-ev intersect env)
                                        (tac-ev new-target env)))
                                      (pred-set-intersects
                                       (tac-ev intersect env)
                                       (tac-ev target env))))
                    (implies (eq (tac-type-fix type) :rel)
                             (implies (and
                                       (tac-ev new-assum env)
                                       (pred-rel-intersects
                                        (tac-ev intersect env)
                                        (tac-ev new-target env)))
                                      (pred-rel-intersects
                                       (tac-ev intersect env)
                                       (tac-ev target env))))))
      :hints ('(:expand (<call>
                         (:free (v x y) (hons-assoc-equal v (cons x y)))
                         (:free (v) (hons-assoc-equal v nil))
                         (:free (x y) (tac-ev-alist (cons x y) env)))
                :in-theory (e/d (tac-function-return-type-when-tac-term-type
                                 tac-ev-of-cons-non-var
                                 lookup-of-nth-var-in-pattern-in-subst)
                                (TAC-TERM-TYPE-WHEN-FNCALL-WITH-RETURN-TYPE
                                 cmr::pseudo-term-var-list->names-when-pseudo-term-listp))
                :use ((:instance tac-intersect-propagate-rule-wellformed-implies
                       (env 
                        (b* ((pat (tac-intersect-propagate-rule->target-pattern rule))
                             ((mv ?ok subst) (cmr::term-unify-strict pat target nil)))
                          (tac-ev-alist (cons (cons (tac-intersect-propagate-rule->intersect-var rule)
                                                    (pseudo-term-fix intersect))
                                              subst)
                                        env))))
                      (:instance tac-intersect-propagate-rule-wellformed-implies
                       (env 
                        (b* ((pat (tac-intersect-propagate-rule->target-pattern rule))
                             ((mv ?ok subst) (cmr::term-unify-strict pat target nil))
                             (desc-intersect (cmr::term-subst-strict
                                              (tac-intersect-propagate-rule->intersect-term rule)
                                              (cons (cons (tac-intersect-propagate-rule->intersect-var rule)
                                                          (pseudo-term-fix intersect))
                                                    subst)))
                             (desc-pos (tac-intersect-propagate-rule->descent-pos rule))
                             (desc-var (pseudo-term-var->name (nth desc-pos (pseudo-term-call->args pat))))
                             (desc-term (nth desc-pos (pseudo-term-call->args target)))
                             (desc-type (tac-intersect-propagate-rule->result-type rule))
                             ((mv ok new-target new-assum witness-term)
                              (tac-fvi-rewrite* desc-term desc-intersect desc-type freevar)))
                          (tac-ev-alist (list* (cons (tac-intersect-propagate-rule->intersect-var rule)
                                                     (pseudo-term-fix intersect))
                                               (cons desc-var new-target)
                                               subst)
                                        env)))))
                :do-not-induct t))
      :fn tac-fvi-rewrite*-propagate
      :rule-classes nil))

  (std::defret-mutual <fn>-in-terms-of-rewrite
    (defret <fn>-in-terms-of-rewrite
      (b* (((mv ok1 new-target1 new-assum1)
            (tac-fvi-rewrite target type freevar)))
        (and (equal ok ok1)
             (equal new-target new-target1)
             (equal new-assum new-assum1)))
      :hints ('(:expand (<call>
                         (tac-fvi-rewrite target type freevar))))
      :fn tac-fvi-rewrite*)
    (defret <fn>-in-terms-of-rewrite
      (b* (((mv ok1 new-target1 new-assum1)
            (tac-fvi-rewrite-propagates prop-rules target freevar)))
        (and (equal ok ok1)
             (equal new-target new-target1)
             (equal new-assum new-assum1)))
      :hints ('(:expand (<call>
                         (tac-fvi-rewrite-propagates prop-rules target freevar))))
      :fn tac-fvi-rewrite*-propagates)
    (defret <fn>-in-terms-of-rewrite
      (b* (((mv ok1 new-target1 new-assum1)
            (tac-fvi-rewrite-propagate rule target freevar)))
        (and (equal ok ok1)
             (equal new-target new-target1)
             (equal new-assum new-assum1)))
      :hints ('(:expand (<call>
                         (tac-fvi-rewrite-propagate rule target freevar))))
      :fn tac-fvi-rewrite*-propagate))

  (local (in-theory (enable tac-rewritelist-fix)))
  (fty::deffixequiv-mutual tac-fvi-rewrite*))



(local (defthm setintersect-of-universe
         (equal (setintersect (universe) x)
                (event-set-fix x))
         :hints(("Goal" :in-theory (enable setintersect
                                           set::double-containment-no-backchain-limit
                                           pick-a-point-subset-strategy
                                           event-p))
                (set::pick-a-point-subset-hint id clause world stable-under-simplificationp)
                (and stable-under-simplificationp
                     '(:use ((:instance EVENT-SET-P-IMPLIES-NOT-IN-WHEN-NOT-EVENT
                              (x (event-set-fix x))
                              (e set::arbitrary-element))))))))

(define tac-fvi-rewrite-pred ((target pseudo-termp)
                              (freevar pseudo-var-p))
  :returns (mv ok
               (new-pred pseudo-termp)
               (new-assum pseudo-termp))
  (pseudo-term-case target
    :fncall (if (eq target.fn 'pred-nonempty)
                (b* (((mv ok new-arg new-assum)
                      (tac-fvi-rewrite (first target.args) :set freevar))
                     ((unless ok) (mv nil nil nil)))
                  (mv t (pseudo-term-call 'pred-nonempty (list new-arg)) new-assum))
              (mv nil nil nil))
    :otherwise (mv nil nil nil))
  ///
  (defret vars-of-<fn>
    (implies (and (not (member-equal v (cmr::Term-vars target)))
                  (not (equal v (pseudo-var-fix freevar))))
             (and (not (member-equal v (cmr::term-vars new-pred)))
                  (not (member-equal v (cmr::term-vars new-assum)))))
    :hints (("goal" :use ((:instance tac-fvi-rewrite*-vars
                           (target (first (pseudo-term-call->args target)))
                           (type :set) (intersect '(universe))))
             :in-theory (e/d (cmr::term-vars)
                             (tac-fvi-rewrite*-vars))
             :expand ((cmr::term-vars target)
                      (cmr::termlist-vars (pseudo-term-call->args target))
                      (:free (x y) (cmr::termlist-vars (cons x y)))))))

  (defret type-of-<fn>
    (implies (and ok
                    (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar)
                                                  (type-ctx-fix ctx)))
                           :event)
                    (equal (tac-term-type target ctx) :pred))
               (and (equal (tac-term-type new-assum ctx) :pred)
                    (equal (tac-term-type new-pred ctx) :pred)))
    :hints (("goal" :use ((:instance tac-fvi-rewrite*-typed
                           (target (first (pseudo-term-call->args target)))
                           (type :set) (intersect '(universe))))
             :in-theory (e/d (tac-term-type
                              acl2::prefixp)
                             (tac-fvi-rewrite*-typed))
             :expand ((tac-term-type target ctx)
                      (tac-termlist-types (pseudo-term-call->args target) ctx)
                      (:free (x y) (tac-termlist-types (cons x y) ctx))))))

  (defret eval-implies-orig-of-<fn>
    (implies (and ok
                  (tac-typed-env-p env ctx)
                  (not (member-equal (pseudo-var-fix freevar) (cmr::term-vars target)))
                  (equal (tac-term-type target ctx) :pred))
               (implies (and (tac-ev new-assum env)
                             (tac-ev new-pred env))
                        (tac-ev target env)))
    :hints (("goal" :use ((:instance tac-fvi-rewrite*-eval-implies-orig
                           (target (first (pseudo-term-call->args target)))
                           (type :set) (intersect '(universe))))))
    :rule-classes nil))

(define tac-fvi-rewrite-pred-witness ((target pseudo-termp)
                                      (freevar pseudo-var-p))
  :returns (witness pseudo-termp)
  :verify-guards nil
  (b* (((mv ?ok ?new-arg ?new-assum witness-term)
        (tac-fvi-rewrite* (first (pseudo-term-call->args target)) '(universe) :set freevar)))
    witness-term)
  ///
  (local (in-theory (enable tac-fvi-rewrite-pred)))
  
  (local (defthm tac-typed-env-p-aux-of-cons
           (implies (and (tac-typed-env-p-aux vars env ctx)
                         (or (not (pseudo-var-p v))
                             (tac-typed-val-p val type)))
                    (tac-typed-env-p-aux vars (cons (cons v val) env)
                                         (cons (cons v type) ctx)))
           :hints(("Goal" 
                   :induct (len vars)
                   :expand ((:free (env ctx)
                             (tac-typed-env-p-aux vars env ctx)))))))

  (local (defthm tac-typed-env-p-of-cons
           (implies (tac-typed-env-p env ctx)
                    (iff (tac-typed-env-p (cons (cons v val) env)
                                          (cons (cons v type) ctx))
                         (or (not (pseudo-var-p v))
                             (tac-typed-val-p val type))))
           :hints(("Goal" :in-theory (enable tac-typed-env-p
                                             acl2::alist-keys
                                             tac-typed-env-p-aux)))))

  (local (defthm tac-typed-val-p-of-ev-bind
           (implies (and (bind-free '((ctx . ctx)) (ctx))
                         (tac-typed-env-p env ctx)
                         (equal (tac-term-type x ctx) type))
                    (tac-typed-val-p (tac-ev x env) type))))

  (local (defthm tac-fvi-rewrite*-witness-typed
           (b* (((mv ok & & witness) (tac-fvi-rewrite* target intersect type freevar)))
             (implies (and ok
                           (not (member-equal (pseudo-var-fix freevar) (cmr::term-vars target)))
                           (not (member-equal (pseudo-var-fix freevar) (cmr::term-vars intersect)))
                           (equal (tac-term-type target ctx) (tac-type-fix type))
                           (equal (tac-term-type intersect ctx) (tac-type-fix type)))
                      (equal (tac-term-type witness ctx) :event)))
           :hints (("goal" :use ((:instance tac-fvi-rewrite*-typed
                                  (ctx (cons (cons (pseudo-var-fix freevar) :event) ctx))))
                    :in-theory (disable tac-fvi-rewrite*-typed)))))
  
  (defret <fn>-correct
    :fn tac-fvi-rewrite-pred
    (implies (and ok
                  (tac-typed-env-p env ctx)
                  (not (member-equal (pseudo-var-fix freevar) (cmr::term-vars target)))
                  (equal (tac-term-type target ctx) :pred))
             (let ((new-env (cons (cons (pseudo-var-fix freevar)
                                        (tac-ev (tac-fvi-rewrite-pred-witness target freevar) env))
                                  env)))
               (iff (and (tac-ev new-assum new-env)
                         (tac-ev new-pred new-env))
                    (tac-ev target env))))
    :hints (("goal" :use ((:instance tac-fvi-rewrite*-correct
                           (target (first (pseudo-term-call->args target)))
                           (type :set) (intersect '(universe))
                           (env (cons (cons (pseudo-var-fix freevar)
                                            (tac-ev (tac-fvi-rewrite-pred-witness target freevar) env))
                                      env))
                           (ctx (cons (cons (pseudo-var-fix freevar) :event) ctx))))
             :in-theory (e/d (tac-term-type
                              acl2::prefixp)
                             ())
             :expand ((tac-term-type target ctx)
                      (cmr::term-vars target)
                      (tac-termlist-types (pseudo-term-call->args target) ctx)
                      (cmr::termlist-vars (pseudo-term-call->args target))
                      (:free (x y) (tac-termlist-types (cons x y) ctx))
                      (:free (x y) (cmr::termlist-vars (cons x y))))))
    :rule-classes nil)

  (defret <fn>-witness-type
    :fn tac-fvi-rewrite-pred
    (implies (and ok
                  (equal (tac-term-type target ctx) :pred))
             (equal (tac-term-type (tac-fvi-rewrite-pred-witness target freevar) ctx) :event))
    :hints (("goal"
             :expand ((tac-term-type target ctx)
                      (cmr::term-vars target)
                      (tac-termlist-types (pseudo-term-call->args target) ctx)
                      (cmr::termlist-vars (pseudo-term-call->args target))
                      (:free (x y) (tac-termlist-types (cons x y) ctx))
                      (:free (x y) (cmr::termlist-vars (cons x y))))
             :in-theory (enable acl2::prefixp))))

  (defret <fn>-witness-vars
    :fn tac-fvi-rewrite-pred
    (implies (and ok
                  (not (member-equal v (cmr::term-vars target))))
             (not (member-equal v (cmr::term-vars (tac-fvi-rewrite-pred-witness target freevar)))))
    :hints (("goal"
             :expand ((cmr::term-vars target)
                      (cmr::termlist-vars (pseudo-term-call->args target))
                      (:free (x y) (cmr::termlist-vars (cons x y))))))))
                  
                  

(define tac-fvi-rewrite-assums ((assums pseudo-term-listp)
                                (freevar pseudo-var-p))
  :returns (mv successp
               (new-assums pseudo-term-listp))
  (b* (((when (atom assums)) (mv nil nil))
       ((mv ok assum1 assum2)
        (tac-fvi-rewrite-pred (car assums) freevar))
       ((when ok)
        (mv t (list* assum1 assum2 (pseudo-term-list-fix (cdr assums)))))
       ((mv ok rest)
        (tac-fvi-rewrite-assums (cdr assums) freevar))
       ((unless ok) (mv nil nil)))
    (mv t (cons (pseudo-term-fix (car assums)) rest)))
  ///
  (defret vars-of-<fn>
    (implies (and (not (member-equal v (cmr::Termlist-vars assums)))
                  (not (equal v (pseudo-var-fix freevar))))
             (not (member-equal v (cmr::termlist-vars new-assums))))
    :hints(("Goal" :in-theory (enable cmr::termlist-vars))))

  (defret type-of-<fn>
    (implies (and (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  (equal (cdr (hons-assoc-equal (pseudo-var-fix freevar)
                                                (type-ctx-fix ctx)))
                         :event))
             (subsetp-equal (tac-termlist-types new-assums ctx) '(:pred)))
    :hints(("Goal" :in-theory (enable tac-termlist-types)
            :induct <call>)))
  
  (defret eval-implies-orig-of-<fn>
    :fn tac-fvi-rewrite-assums
    (implies (and successp
                  (tac-typed-env-p env ctx)
                  (not (member-equal (pseudo-var-fix freevar) (cmr::termlist-vars assums)))
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred)))
               (implies (tac-ev-cube new-assums env)
                        (tac-ev-cube assums env)))
    :hints(("Goal" :in-theory (enable tac-ev-cube
                                      cmr::termlist-vars
                                      tac-termlist-types)
            :induct <call>
            :expand (<call>))
           (and stable-under-simplificationp
                '(:use ((:instance eval-implies-orig-of-tac-fvi-rewrite-pred
                         (target (car assums)))))))
    :rule-classes nil))

(define tac-fvi-rewrite-assums-witness ((assums pseudo-term-listp)
                                        (freevar pseudo-var-p))
  :returns (witness pseudo-termp)
  :verify-guards nil
  (b* (((when (atom assums)) nil)
       ((mv ok ?assum1 ?assum2)
        (tac-fvi-rewrite-pred (car assums) freevar))
       ((when ok)
        (tac-fvi-rewrite-pred-witness (car assums) freevar)))
    (tac-fvi-rewrite-assums-witness (cdr assums) freevar))
  ///
  (local (in-theory (enable tac-fvi-rewrite-assums)))
  (defret <fn>-correct
    :fn tac-fvi-rewrite-assums
    (implies (and successp
                  (tac-typed-env-p env ctx)
                  (not (member-equal (pseudo-var-fix freevar) (cmr::termlist-vars assums)))
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred)))
             (let ((new-env (cons (cons (pseudo-var-fix freevar)
                                        (tac-ev (tac-fvi-rewrite-assums-witness assums freevar) env))
                                  env)))
               (iff (tac-ev-cube new-assums new-env)
                    (tac-ev-cube assums env))))
    :hints(("Goal" :in-theory (enable tac-ev-cube
                                      cmr::termlist-vars
                                      tac-termlist-types)
            :induct <call>
            :expand (<call>
                     (tac-fvi-rewrite-assums-witness assums freevar)))
           (and stable-under-simplificationp
                '(:use ((:instance tac-fvi-rewrite-pred-correct
                         (target (car assums)))))))
    :rule-classes nil)

  (defret <fn>-witness-type
    :fn tac-fvi-rewrite-assums
    (implies (and successp
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred)))
             (equal (tac-term-type (tac-fvi-rewrite-assums-witness assums freevar) ctx) :event))
    :hints(("Goal" :in-theory (enable tac-termlist-types)
            :induct <call>
            :expand (<call>
                     (tac-fvi-rewrite-assums-witness assums freevar)))))

  (defret <fn>-witness-vars
    :fn tac-fvi-rewrite-assums
    (implies (and successp
                  (not (member-equal v (cmr::termlist-vars assums))))
             (not (member-equal v (cmr::term-vars (tac-fvi-rewrite-assums-witness assums freevar)))))
    :hints (("goal" :in-theory (enable cmr::termlist-vars)))))










               
                          
         







