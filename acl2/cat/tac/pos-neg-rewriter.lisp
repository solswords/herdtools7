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

(include-book "pos-neg-apply-rule")
(include-book "basic-rewriter")
(include-book "centaur/fty/baselists" :dir :system)
(local (include-book "common-thms"))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :System))
(local (std::add-default-post-define-hook :fix))


(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (not (consp x)))))

(define remove-entries-with-nil ((x true-list-listp))
  (if (atom x)
      nil
    (if (member-equal nil (car x))
        (remove-entries-with-nil (cdr x))
      (cons (acl2::true-list-fix (car x))
            (remove-entries-with-nil (cdr x)))))
  ///
  (defthm remove-entries-with-nil-of-append
    (equal (remove-entries-with-nil (append x y))
           (append (remove-entries-with-nil x)
                   (remove-entries-with-nil y))))
  (local (in-theory (enable acl2::true-list-list-fix))))

(define tac-typed-vallistlist-p ((x true-list-listp)
                                 (types tac-typelist-p))
  (if (atom x)
      t
    (and (tac-typed-vallist-p (car x) types)
         (tac-typed-vallistlist-p (cdr x) types)))
  ///
  (defthm tac-typed-vallistlist-p-of-append
    (implies (and (tac-typed-vallistlist-p x types)
                  (tac-typed-vallistlist-p y types))
             (tac-typed-vallistlist-p (append x y) types))))



(define lists-have-lengths ((n natp) x)
  (if (atom x)
      t
    (and (equal (len (car x)) (lnfix n))
         (lists-have-lengths n (cdr x))))
  ///
  (defthm lists-have-lengths-of-append
    (iff (lists-have-lengths n (append x y))
         (and (lists-have-lengths n x)
              (lists-have-lengths n y)))))

(define cons-to-each (x (y true-list-listp))
  :returns (new-y true-list-listp)
  (if (atom y)
      nil
    (cons (cons x (true-list-fix (car y)))
          (cons-to-each x (cdr y))))
  ///
  (defthm tac-typed-vallistlist-p-of-cons-to-each
    (implies (and (tac-typed-val-p x (car types))
                  (tac-typed-vallistlist-p y (cdr types)))
             (tac-typed-vallistlist-p (cons-to-each x y) types))
    :hints(("Goal" :in-theory (enable tac-typed-vallistlist-p
                                      tac-typed-vallist-p))))

  (defthm cons-to-each-of-append
    (equal (cons-to-each x (append y z))
           (append (cons-to-each x y)
                   (cons-to-each x z))))

  (defret lists-have-lengths-of-<fn>
    (implies (and (posp n)
                  (lists-have-lengths (1- n) y))
             (lists-have-lengths n new-y))
    :hints(("Goal" :in-theory (enable lists-have-lengths)))))

(local (defthm true-list-listp-of-append
         (implies (and (true-list-listp x)
                       (true-list-listp y))
                  (true-list-listp (append x y)))))

(define cons-product ((x true-listp)
                      (y true-list-listp))
  :returns (prod true-list-listp)
  (if (atom x)
      nil
    (append (cons-to-each (car x) y)
            (cons-product (cdr x) y)))
  ///
  (defthm tac-typed-vallistlist-p-of-cons-product
    (implies (and (tac-1typed-vallist-p x (car types))
                  (tac-typed-vallistlist-p y (cdr types)))
             (tac-typed-vallistlist-p (cons-product x y) types))
    :hints(("Goal" :in-theory (enable tac-typed-vallistlist-p
                                      tac-1typed-vallist-p))))

  (defret lists-have-lengths-of-<fn>
    (implies (and (posp n)
                  (lists-have-lengths (1- n) y))
             (lists-have-lengths n prod))
    :hints(("Goal" :in-theory (enable lists-have-lengths)))))


(define arglist-product ((x true-list-listp))
  :returns (product)
  (if (atom x)
      (list nil)
    (cons-product (car x) (arglist-product (cdr x))))
  ///
  (defthm tac-typed-vallistlist-p-of-arglist
    (implies (and (tac-typed-multiarglist-p x types)
                  (equal (len types) (len x)))
             (tac-typed-vallistlist-p (arglist-product x) types))
    :hints(("Goal" :in-theory (enable tac-typed-multiarglist-p
                                      tac-typed-vallistlist-p
                                      tac-typed-vallist-p))))

  (defret lists-have-lengths-of-<fn>-lemma
    (lists-have-lengths (len x) product))

  (defret lists-have-lengths-of-<fn>
    (implies (equal (len x) (nfix n))
             (lists-have-lengths n product))
    :hints(("Goal" :in-theory (enable lists-have-lengths)))))

(fty::deffixcong pseudo-fnsym-equiv equal (tac-ev-apply fn args) fn
  :hints(("Goal" :in-theory (enable tac-ev-apply pseudo-fnsym-fix))))


(fty::deffixcong acl2::list-equiv equal (tac-ev-apply fn args) args
  :hints(("Goal" :in-theory (enable tac-ev-apply))))

(define tac-ev-apply-to-arglists ((fn pseudo-fnsym-p)
                                  (args true-list-listp))
  :verify-guards nil
  (if (atom args)
      nil
    (cons (tac-ev-apply fn (car args))
          (tac-ev-apply-to-arglists fn (cdr args))))
  ///
  (defthm tac-ev-apply-to-arglists-of-append
    (equal (tac-ev-apply-to-arglists fn (append x y))
           (append (tac-ev-apply-to-arglists fn x)
                   (tac-ev-apply-to-arglists fn y)))))



(define tac-ruleres-branch-argslist-have-lengths ((n natp) (x tac-ruleres-branch-argslist-p))
  (if (atom x)
      t
    (and (equal (lnfix n) (len (tac-ruleres-branch-args->ctx-result-args (car x))))
         (tac-ruleres-branch-argslist-have-lengths n (cdr x))))
  ///
  (defthm tac-ruleres-branch-argslist-have-lengths-of-append
    (implies (and (tac-ruleres-branch-argslist-have-lengths n x)
                  (tac-ruleres-branch-argslist-have-lengths n y))
             (tac-ruleres-branch-argslist-have-lengths n (append x y)))))


(define tac-ruleres-branch-argslist-no-assums-without-args ((x tac-ruleres-branch-argslist-p))
  (if (atom x)
      t
    (and (b* (((tac-ruleres-branch-args x1) (car x)))
           (implies (not (consp x1.ctx-result-args))
                    (not (consp x1.assums))))
         (tac-ruleres-branch-argslist-no-assums-without-args (cdr x))))
  ///
  (defthm tac-ruleres-branch-argslist-no-assums-without-args-of-append
    (implies (and (tac-ruleres-branch-argslist-no-assums-without-args x)
                  (tac-ruleres-branch-argslist-no-assums-without-args y))
             (tac-ruleres-branch-argslist-no-assums-without-args (append x y)))))


(define tac-ruleres-branch-product-with-branch-argslist ((x tac-ruleres-branch-p)
                                                                      (y tac-ruleres-branch-argslist-p))
  :returns (new-y tac-ruleres-branch-argslist-p)
  (if (atom y)
      nil
    (cons (b* (((tac-ruleres-branch x))
               ((tac-ruleres-branch-args y1) (car y)))
            (tac-ruleres-branch-args (append x.assums y1.assums)
                                                  (cons x.ctx-result y1.ctx-result-args)))
          (tac-ruleres-branch-product-with-branch-argslist x (cdr y))))
  ///
  (defret vars-of-<fn>
    (implies (and (not (member v (tac-ruleres-branch-vars x)))
                  (not (member v (tac-ruleres-branch-argslist-vars y))))
             (not (member v (tac-ruleres-branch-argslist-vars new-y))))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-vars
                                      tac-ruleres-branch-argslist-vars
                                      tac-ruleres-branch-args-vars
                                      cmr::termlist-vars))))
  
  (local (defthm remove-entries-with-nil-of-cons-to-each-nil
           (equal (remove-entries-with-nil (cons-to-each nil x)) nil)
           :hints(("Goal" :in-theory (enable remove-entries-with-nil cons-to-each)))))
  (defret lengths-of-<fn>
    (implies (and (tac-ruleres-branch-argslist-have-lengths (1- n) y)
                  (posp n))
             (tac-ruleres-branch-argslist-have-lengths n new-y))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-argslist-have-lengths
                                      nfix))))
     
  (defret eval-of-<fn>
    (implies (tac-ruleres-branch-argslist-no-assums-without-args y)
             (equal (remove-entries-with-nil (tac-eval-ruleres-branch-argslist new-y env))
                    (remove-entries-with-nil
                     (cons-to-each (tac-eval-ruleres-branch x env)
                                   (tac-eval-ruleres-branch-argslist y env)))))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch-argslist
                                      tac-eval-ruleres-branch
                                      tac-eval-ruleres-branch-args
                                      tac-ruleres-branch-argslist-no-assums-without-args
                                      remove-entries-with-nil
                                      tac-ev-cube
                                      cons-to-each))))

  (defret tac-ruleres-branch-argslist-no-assums-without-args-of-<fn>
    (tac-ruleres-branch-argslist-no-assums-without-args new-y)
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-argslist-no-assums-without-args))))

  (defret types-of-<fn>
    (implies (and (tac-ruleres-branch-typed x (car types) Ctx)
                  (tac-ruleres-branch-argslist-typed y (cdr types) ctx)
                  (not (member-equal nil (tac-typelist-fix types))))
             (tac-ruleres-branch-argslist-typed new-y types ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-typed
                                      tac-ruleres-branch-argslist-typed
                                      tac-ruleres-branch-args-typed
                                      tac-termlist-types acl2::prefixp tac-typelist-fix)
            :induct <call>))))


(local (defthm member-tac-ruleres-branch-arslist-vars-of-append
         (iff (member v (tac-ruleres-branch-argslist-vars (append a b)))
              (or (member v (tac-ruleres-branch-argslist-vars a))
                  (member v (tac-ruleres-branch-argslist-vars b))))
         :hints(("Goal" :in-theory (enable tac-ruleres-branch-argslist-vars)))))

(define tac-ruleres-branchlist-product-with-branch-argslist ((x tac-ruleres-branchlist-p)
                                                                          (y tac-ruleres-branch-argslist-p))
  :Returns (new-y tac-ruleres-branch-argslist-p)
  (if (atom x)
      nil
    (append (tac-ruleres-branch-product-with-branch-argslist (car x) y)
            (tac-ruleres-branchlist-product-with-branch-argslist (cdr x) y)))
  ///
  (defret vars-of-<fn>
    (implies (and (not (member v (tac-ruleres-branchlist-vars x)))
                  (not (member v (tac-ruleres-branch-argslist-vars y))))
             (not (member v (tac-ruleres-branch-argslist-vars new-y))))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-vars
                                      tac-ruleres-branch-argslist-vars
                                      tac-ruleres-branch-args-vars))))
  (defret eval-of-<fn>
    (implies (tac-ruleres-branch-argslist-no-assums-without-args y)
             (equal (remove-entries-with-nil
                     (tac-eval-ruleres-branch-argslist new-y env))
                    (remove-entries-with-nil
                     (cons-product (tac-eval-ruleres-branchlist x env)
                                   (tac-eval-ruleres-branch-argslist y env)))))
    :hints(("Goal" :in-theory (enable cons-product
                                      tac-eval-ruleres-branchlist
                                      tac-eval-ruleres-branch-argslist))))

  (defret lengths-of-<fn>
    (implies (and (tac-ruleres-branch-argslist-have-lengths (1- n) y)
                  (posp n))
             (tac-ruleres-branch-argslist-have-lengths n new-y))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-argslist-have-lengths
                                      nfix))))

  (defret tac-ruleres-branch-argslist-no-assums-without-args-of-<fn>
    (tac-ruleres-branch-argslist-no-assums-without-args new-y)
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-argslist-no-assums-without-args))))

  (defret types-of-<fn>
    (implies (and (tac-ruleres-branchlist-typed x (car types) Ctx)
                  (tac-ruleres-branch-argslist-typed y (cdr types) ctx)
                  (not (member-equal nil (tac-typelist-fix types))))
             (tac-ruleres-branch-argslist-typed new-y types ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-typed
                                      tac-ruleres-branch-argslist-typed)
            :induct <call>))))

(defthm remove-entries-with-nil-of-cons-to-each
  (equal (remove-entries-with-nil (cons-to-each x y))
         (and x
              (cons-to-each x (remove-entries-with-nil y))))
  :hints(("Goal" :in-theory (enable cons-to-each remove-entries-with-nil))))

(defthm remove-entries-with-nil-of-cons-product
  (equal (remove-entries-with-nil (cons-product x y))
         (cons-product (remove nil x) (remove-entries-with-nil y)))
  :hints(("Goal" :in-theory (enable cons-product remove-entries-with-nil))))





(define tac-ruleres-branchlistlist-to-branch-argslist ((x tac-ruleres-branchlistlist-p))
  :returns (arglist tac-ruleres-branch-argslist-p)
  (if (atom x)
      (list (tac-ruleres-branch-args nil nil))
    (tac-ruleres-branchlist-product-with-branch-argslist
     (car x) (tac-ruleres-branchlistlist-to-branch-argslist (cdr x))))
  ///
  (defret tac-ruleres-branch-argslist-no-assums-without-args-of-<fn>
    (tac-ruleres-branch-argslist-no-assums-without-args arglist))

  (defret eval-of-<fn>
    (equal (remove-entries-with-nil
            (tac-eval-ruleres-branch-argslist arglist env))
           (remove-entries-with-nil
            (arglist-product (tac-eval-ruleres-branchlistlist x env))))
    :hints(("Goal" :in-theory (enable arglist-product
                                      TAC-EVAL-RULERES-BRANCHLISTLIST
                                      tac-eval-ruleres-branchlist
                                      tac-eval-ruleres-branch-argslist)
            :induct <call>)
           (And stable-under-simplificationp
                '(:in-theory (enable remove-entries-with-nil
                                     tac-eval-ruleres-branch-args)))))

  (defret lengths-of-<fn>-lemma
    (tac-ruleres-branch-argslist-have-lengths (len x) arglist))

  (defret lengths-of-<fn>
    (implies (equal (nfix n) (len x))
             (tac-ruleres-branch-argslist-have-lengths n arglist)))

  (defret types-of-<fn>
    (implies (and (tac-ruleres-branchlistlist-typed x types ctx)
                  (equal (len types) (len x))
                  (not (member-equal nil (tac-typelist-fix types))))
             (tac-ruleres-branch-argslist-typed arglist types ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlistlist-typed
                                      tac-ruleres-branch-argslist-typed)
            ;; :expand ((tac-ruleres-branchlistlist-typed x types ctx))
            :induct (tac-ruleres-branchlistlist-typed x types ctx)
            :expand (<call>))
           (and stable-under-simplificationp
                '(:in-theory (enable tac-ruleres-branch-args-typed
                                     tac-termlist-types acl2::prefixp)))))

  (defret vars-of-<fn>
    (implies (not (member v (tac-ruleres-branchlistlist-vars x)))
             (not (member v (tac-ruleres-branch-argslist-vars arglist))))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlistlist-vars
                                      tac-ruleres-branch-argslist-vars
                                      tac-ruleres-branch-args-vars)))))

(local (defthm equal-pseudo-fnsym-fix-forward
         (implies (equal (pseudo-fnsym-fix x) y)
                  (pseudo-fnsym-equiv x y))
         :rule-classes :forward-chaining))

(define union-multiarglists ((x true-list-listp))
  :verify-guards nil
  :returns (args true-listp)
  (if (atom x)
      nil
    (cons (union-list (car x))
          (union-multiarglists (cdr x))))
  ///
  (defthm tac-typed-vallist-p-of-union-multiarglist
    (implies (and (tac-typed-multiarglist-p x types)
                  (subsetp-equal types '(:set :rel)))
             (tac-typed-vallist-p (union-multiarglists x) types))
    :hints(("Goal" :in-theory (enable tac-typed-vallist-p
                                      tac-typed-multiarglist-p))))
  (local (in-theory (enable acl2::true-list-list-fix))))


(define tac-context-fn-p ((x pseudo-fnsym-p))
  (and (member-eq (pseudo-fnsym-fix x) '(setimage setpreimage setintersect
                                                  relidentity relcompose relinverse relprod relintersect))
       t)
  ///
  (defthm tac-function-return-type-when-tac-context-fn-p
    (implies (tac-context-fn-p x)
             (tac-function-return-type x)))

  (defthm tac-ev-apply-nil-when-tac-context-fn-p
    (implies (tac-context-fn-p fn)
             (equal (tac-ev-apply fn nil) nil))
    :hints(("Goal" :in-theory (enable tac-ev-apply
                                      tac-context-fn-p))))

  (local (in-theory (enable set::union-symmetric set::union-commutative)))

  (local (include-book "propagation"))
  (local (defthm tac-typed-val-p-of-rel
           (implies (tac-typed-val-p x :rel)
                    (relation-p x))
           :hints(("Goal" :in-theory (enable tac-typed-val-p)))))
  ;; (local (defthm setpreimage-of-union-1
  ;;          (implies (relation-p z)
  ;;                   (equal (setpreimage (union x y) z)
  ;;                          (union (setpreimage x z)
  ;;                                 (setpreimage y z))))
  ;;          :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
  ;;                                             pick-a-point-subset-strategy
  ;;                                             in-of-setpreimage-rw)))))

  ;; (local (defthm setpreimage-of-union-2
  ;;          (implies (and (relation-p y)
  ;;                        (relation-p z))
  ;;                   (equal (setpreimage x (union y z))
  ;;                          (union (setpreimage x y)
  ;;                                 (setpreimage x z))))
  ;;          :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
  ;;                                             pick-a-point-subset-strategy
  ;;                                             in-of-setpreimage-rw)))))

  (local (defund empty-set () nil))
  (local (defthm setp-empty-set
           (setp (empty-set))))

  ;; (local (defthm setpreimage-of-nil-3
  ;;          ;; (and (equal (setpreimage x nil) nil)
  ;;          (equal (setpreimage nil x) nil)
  ;;          :hints(("Goal" :in-theory (enable setpreimage)))))
  
  (defthm tac-context-fn-apply-when-member-nil
    (implies (and (tac-context-fn-p fn)
                  (member nil (take (len (tac-function-argument-types fn)) args)))
             (equal (tac-ev-apply fn args) nil))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable tac-ev-apply)))))
    
  
  (defthm union-of-tac-ev-apply-to-arglists-of-cons-to-each-union
    (implies (and (tac-context-fn-p fn)
                  (tac-typed-val-p x (car (tac-function-argument-types fn)))
                  (tac-typed-val-p y (car (tac-function-argument-types fn)))
                  (tac-typed-vallistlist-p z (cdr (tac-function-argument-types fn))))
             (equal (union-list (tac-ev-apply-to-arglists fn (cons-to-each (union x y) z)))
                    (union (union-list (tac-ev-apply-to-arglists fn (cons-to-each x z)))
                           (union-list (tac-ev-apply-to-arglists fn (cons-to-each y z))))))
    :hints (("goal" :in-theory (enable union-list cons-to-each
                                       tac-ev-apply-to-arglists
                                       tac-typed-vallistlist-p
                                       tac-ev-apply))))

  (defthm union-of-tac-ev-apply-to-arglists-of-cons-to-each-union-2
    (implies (and (tac-context-fn-p fn)
                  (< 1 (len (tac-function-argument-types fn)))
                  (tac-typed-val-p x (cadr (tac-function-argument-types fn)))
                  (tac-typed-val-p y (cadr (tac-function-argument-types fn)))
                  (tac-typed-vallistlist-p z (cddr (tac-function-argument-types fn))))
             (equal (union-list (tac-ev-apply-to-arglists fn (cons-to-each x1 (cons-to-each (union x y) z))))
                    (union (union-list (tac-ev-apply-to-arglists fn (cons-to-each x1 (cons-to-each x z))))
                           (union-list (tac-ev-apply-to-arglists fn (cons-to-each x1 (cons-to-each y z)))))))
    :hints (("goal"
             :induct (len z)
             :in-theory (enable cons-to-each
                                tac-ev-apply-to-arglists
                                tac-typed-vallistlist-p
                                union-list))
            (and stable-under-simplificationp
                 '(:in-theory (enable tac-ev-apply)))))
  
           
  (defthm union-of-tac-ev-apply-to-arglists-of-cons-to-each-nil
    (implies (and (tac-context-fn-p fn)
                  (tac-typed-vallistlist-p z (cdr (tac-function-argument-types fn))))
             (equal (union-list (tac-ev-apply-to-arglists fn (cons-to-each nil z)))
                    nil))
    :hints (("goal" :in-theory (enable union-list cons-to-each
                                       tac-ev-apply-to-arglists
                                       tac-typed-vallistlist-p
                                       tac-ev-apply))))

  (defthm union-of-tac-ev-apply-to-arglists-of-cons-to-each-nil-2
    (implies (and (tac-context-fn-p fn)
                  (< 1 (len (tac-function-argument-types fn)))
                  (tac-typed-vallistlist-p z (cddr (tac-function-argument-types fn))))
             (equal (union-list (tac-ev-apply-to-arglists fn (cons-to-each x (cons-to-each nil z))))
                    nil))
    :hints (("goal" :in-theory (enable union-list cons-to-each
                                       tac-ev-apply-to-arglists
                                       tac-typed-vallistlist-p
                                       tac-ev-apply)
             :induct (len z))))

  (defthm function-argument-types-when-tac-context-fn-p
    (implies (tac-context-fn-p fn)
             (subsetp-equal (tac-function-argument-types fn) '(:set :rel))))

  (defthm function-argument-types-when-tac-context-fn-p-2
    (implies (tac-context-fn-p fn)
             (member-equal (car (tac-function-argument-types fn)) '(:set :rel))))
  
  (defthm union-of-tac-ev-apply-to-arglists-of-cons-product
    (implies (and (tac-context-fn-p fn)
                  (tac-1typed-vallist-p x (car (tac-function-argument-types fn)))
                  (tac-typed-vallistlist-p y (cdr (tac-function-argument-types fn))))
             (equal (union-list (tac-ev-apply-to-arglists fn (cons-product x y)))
                    (union-list (tac-ev-apply-to-arglists fn (cons-to-each (union-list x) y)))))
    :hints (("goal" :in-theory (e/d (cons-product union-list cons-to-each
                                                  tac-1typed-vallist-p)
                                    (tac-context-fn-p))
             :induct (len x)
             :expand ((tac-ev-apply-to-arglists fn nil)))))

  (defthm union-of-tac-ev-apply-to-arglists-of-cons-product-2
    (implies (and (tac-context-fn-p fn)
                  (< 1 (len (tac-function-argument-types fn)))
                  (tac-1typed-vallist-p x (cadr (tac-function-argument-types fn)))
                  (tac-typed-vallistlist-p y (cddr (tac-function-argument-types fn))))
             (equal (union-list (tac-ev-apply-to-arglists fn (cons-to-each x1 (cons-product x y))))
                    (union-list (tac-ev-apply-to-arglists fn (cons-to-each x1 (cons-to-each (union-list x) y))))))
    :hints (("goal" :in-theory (e/d (cons-product union-list cons-to-each
                                                  tac-1typed-vallist-p)
                                    (tac-context-fn-p))
             :induct (len x)
             :expand ((tac-ev-apply-to-arglists fn nil)))))

  (defthm tac-ev-apply-of-union-lists-when-tac-context-fn-p
    (implies (and (tac-context-fn-p fn)
                  (tac-typed-multiarglist-p x (tac-function-argument-types fn))
                  (equal (len x) (len (tac-function-argument-types fn))))
             (equal (union-list (tac-ev-apply-to-arglists fn (arglist-product x)))
                    (tac-ev-apply fn (union-multiarglists x))))
    :hints (("goal" :expand ((arglist-product x)
                             (arglist-product (cdr x))
                             (arglist-product (cddr x))
                             (union-multiarglists x)
                             (union-multiarglists (cdr x))
                             (union-multiarglists (cddr x))
                             (:free (x a b) (cons-to-each x (cons a b)))
                             (:free (x) (cons-to-each x nil))
                             (:free (a b) (union-list (cons a b)))
                             (:free (fn a b) (tac-ev-apply-to-arglists fn (cons a b)))
                             (:free (fn a b) (tac-ev-apply-to-arglists fn nil))
                             (:free (x a b) (tac-typed-multiarglist-p x (cons a b))))
             :do-not-induct t
             :in-theory (disable (tac-ev-apply-to-arglists)))
            (and stable-under-simplificationp
                 '(:in-theory (enable tac-ev-apply)))))

  (defthm tac-ev-apply-to-arglists-of-remove-entries-with-nil-when-tac-context-fn-p
    (implies (and (tac-context-fn-p fn)
                  (lists-have-lengths (len (tac-function-argument-types fn)) x))
             (equal (union-list (tac-ev-apply-to-arglists fn (remove-entries-with-nil x)))
                    (union-list (tac-ev-apply-to-arglists fn x))))
    :hints(("Goal" :in-theory (enable remove-entries-with-nil
                                      lists-have-lengths
                                      tac-ev-apply-to-arglists)
            :induct (len x))
           (and stable-under-simplificationp
                '(:in-theory (enable tac-ev-apply
                                     union-list)))))

  (local (defthm lists-have-lengths-of-remove-entries-with-nil
           (implies (lists-have-lengths n x)
                    (lists-have-lengths n (remove-entries-with-nil x)))
           :hints(("Goal" :in-theory (enable lists-have-lengths remove-entries-with-nil)))))
  
  (defthm rewrite-tac-ev-apply-to-arglists-under-remove-entries-with-nil
    (implies (and (tac-context-fn-p fn)
                  (lists-have-lengths (len (tac-function-argument-types fn)) x)
                  (equal x1 (remove-entries-with-nil x))
                  (bind-free
                   (case-match x1
                     (('remove-entries-with-nil x2) `((x2 . ,x2) (flag . 't)))
                     (& `((x2 . ,x1) (flag . 'nil))))
                   (x2 flag))
                  ;; (syntaxp ((lambda (mfc state)
                  ;;             (declare (ignore state))
                  ;;             (progn$ (cw "unify subst: ~x0~%" (mfc-unify-subst mfc))
                  ;;                     t))
                  ;;           mfc state))
                  (syntaxp (not (equal x2 x)))
                  (equal x1 (if flag (remove-entries-with-nil x2) x2))
                  (lists-have-lengths (len (tac-function-argument-types fn)) x2))
             (equal (union-list (tac-ev-apply-to-arglists fn x))
                    (union-list (tac-ev-apply-to-arglists fn x2))))
    :hints(("Goal" :in-theory (disable tac-context-fn-p
                                       tac-ev-apply-to-arglists-of-remove-entries-with-nil-when-tac-context-fn-p)
            :use ((:instance tac-ev-apply-to-arglists-of-remove-entries-with-nil-when-tac-context-fn-p (x x))
                  (:instance tac-ev-apply-to-arglists-of-remove-entries-with-nil-when-tac-context-fn-p (x x2)))))
    ))


(define apply-fn-to-result-branches ((fn pseudo-fnsym-p)
                                     (results tac-ruleres-branch-argslist-p))
  :returns (apps tac-ruleres-branchlist-p)
  (if (atom results)
      nil
    (cons (b* (((tac-ruleres-branch-args x) (car results)))
            (tac-ruleres-branch x.assums
                                             (pseudo-term-fncall fn x.ctx-result-args)))
          (apply-fn-to-result-branches fn (cdr results))))
  ///
  (defthm len-args-when-tac-context-fn-p
    (implies (tac-context-fn-p fn)
             (< 0 (len (tac-function-argument-types fn))))
    :hints(("Goal" :in-theory (enable tac-context-fn-p)))
    :rule-classes (:linear :type-prescription))
  
  (defret eval-of-<fn>
    (implies (and (tac-context-fn-p fn)
                  (tac-ruleres-branch-argslist-have-lengths
                   (len (tac-function-argument-types fn)) results))
             (equal (tac-eval-ruleres-branchlist apps env)
                    (tac-ev-apply-to-arglists fn (tac-eval-ruleres-branch-argslist results env))))
    :hints(("Goal" :in-theory (enable tac-ev-apply-to-arglists
                                      tac-ruleres-branch-argslist-have-lengths
                                      tac-ruleres-branch-argslist-no-assums-without-args
                                      tac-ev-cube
                                      tac-eval-ruleres-branch
                                      tac-eval-ruleres-branch-args
                                      tac-eval-ruleres-branch-argslist
                                      tac-eval-ruleres-branchlist)
            :expand ((:free (args) (tac-ev (cons (pseudo-fnsym-fix fn) args) env))))))
  
  (defret types-of-apply-fn-to-result-branches
    (implies (and (equal rettype (tac-function-return-type fn))
                  rettype
                  (tac-ruleres-branch-argslist-typed
                   results (tac-function-argument-types fn) ctx))
             (tac-ruleres-branchlist-typed apps rettype ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-typed
                                      tac-ruleres-branch-typed
                                      TAC-RULERES-BRANCH-ARGS-TYPED
                                      TAC-RULERES-BRANCH-ARGSLIST-TYPED)
            :induct <call>)
           (And stable-under-simplificationp
                '(:expand ((:free (args) (tac-term-type (pseudo-term-fncall fn args) ctx)))))))

  (defret vars-of-<fn>
    (implies (not (member v (tac-ruleres-branch-argslist-vars results)))
             (not (member v (tac-ruleres-branchlist-vars apps))))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-argslist-vars
                                      tac-ruleres-branch-args-vars
                                      tac-ruleres-branchlist-vars
                                      tac-ruleres-branch-vars
                                      cmr::term-vars)))))




(define tac-try-basic-rewrites ((rules tac-rewritelist-p)
                                (fn pseudo-fnsym-p)
                                (args pseudo-term-listp))
  :returns (mv rewrittenp (result pseudo-termp))
  (if (atom rules)
      (mv nil nil)
    (b* (((unless (mbt (consp (car rules))))
          (tac-try-basic-rewrites (cdr rules) fn args))
         ((mv ok rhs subst) (tac-rewrite-apply-rule (cdar rules) fn args))
         ((when ok) (mv t (cmr::term-subst-strict rhs subst))))
      (tac-try-basic-rewrites (cdr rules) fn args)))
  ///
  (defret <fn>-preserves-vars
    (implies (not (member v (cmr::termlist-vars args)))
             (not (member v (cmr::term-vars result)))))
  
  (defret <fn>-correct
    (implies (and rewrittenp
                  (tac-ev-theoremlist-p (tac-rewritelist-terms rules))
                  (tac-rewrites-hyps-ok rules)
                  (tac-typed-env-p env ctx)
                  (tac-term-type (pseudo-term-fncall fn args) ctx))
             (equal (tac-ev result env)
                    (tac-ev (pseudo-term-fncall fn args) env)))
    :hints(("Goal" :in-theory (enable tac-ev-theoremlist-p
                                      tac-rewritelist-terms
                                      tac-rewrites-hyps-ok))))

  (local (in-theory (disable tac-term-type-of-term-subst-strict)))
  
  (defret <fn>-preserves-type
    (implies (and rewrittenp
                  (tac-rewrites-rhs-preserved rules)
                  (equal type (tac-term-type (pseudo-term-fncall fn args) ctx))
                  type)
             (equal (tac-term-type result ctx) type))
    :hints(("Goal" :in-theory (enable tac-rewrites-rhs-preserved))))

  (local (in-theory (enable tac-rewritelist-fix))))



(define args-to-tac-ruleres-branchlistlist ((x pseudo-term-listp))
  :returns (branch-args tac-ruleres-branchlistlist-p)
  (if (atom x)
      nil
    (cons (list (tac-ruleres-branch nil (car x)))
          (args-to-tac-ruleres-branchlistlist (cdr x))))
  ///
  (local (defun cdr2 (x y)
           (if (atom x)
               y
             (cdr2 (cdr x) (cdr y)))))
  (defret <fn>-typed
    (implies (acl2::prefixp types (tac-termlist-types x ctx))
             (tac-ruleres-branchlistlist-typed
              branch-args types ctx))
    :hints(("Goal" :in-theory (enable tac-termlist-types
                                      acl2::prefixp
                                      tac-ruleres-branchlistlist-typed
                                      tac-ruleres-branchlist-typed
                                      tac-ruleres-branch-typed)
            :induct (cdr2 x types))))

  (defret len-of-<fn>
    (equal (len branch-args) (len x)))

  (defret eval-of-<fn>
    (implies (and (tac-typed-env-p env ctx)
                  (subsetp (tac-termlist-types x ctx) '(:set :rel)))
             (equal (union-multiarglists
                     (tac-eval-ruleres-branchlistlist
                      branch-args env))
                    (tac-ev-lst x env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branchlistlist
                                      tac-eval-ruleres-branchlist
                                      tac-eval-ruleres-branch
                                      union-multiarglists
                                      tac-termlist-types
                                      tac-ev-cube
                                      union-list))))

  (defret vars-of-<fn>
    (implies (not (member v (cmr::termlist-vars x)))
             (not (member v (tac-ruleres-branchlistlist-vars branch-args))))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlistlist-vars
                                      tac-ruleres-branchlist-vars
                                      tac-ruleres-branch-vars
                                      cmr::termlist-vars)))))

(deftypes used-subst-database
  (defprod term-used-subst-database
    ((rule-substs rule-used-substs-p)
     (arg-substs arg-used-subst-database))
    :layout :tree ;; so that nil is valid
    :measure (acl2::two-nats-measure (acl2-count x) 1))
  (fty::defmap arg-used-subst-database :key-type natp :val-type term-used-subst-database
    :true-listp t
    :valp-of-nil t
    :measure (acl2::two-nats-measure (acl2-count x) 0)))


(local
 (defthm lengths-of-tac-eval-ruleres-branch-argslist-when-have-lengths
   (equal (lists-have-lengths n (tac-eval-ruleres-branch-argslist x env))
          (tac-ruleres-branch-argslist-have-lengths n x))
   :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch-argslist
                                     tac-ruleres-branch-argslist-have-lengths
                                     lists-have-lengths
                                     tac-eval-ruleres-branch-args)))))

(local (in-theory (disable subsetp-equal
                           pseudo-termp
                           pseudo-term-listp
                           take
                           hons-assoc-equal
                           member-equal)))

(defines tac-apply-rule-in-context
  (define tac-apply-rule-in-context ((x pseudo-termp)
                                     (assums1 pseudo-term-listp)
                                     (assums2 pseudo-term-listp)
                                     (ruleset tac-rewritelist-p)
                                     (subst-database term-used-subst-database-p))
    ;; Positive rules replace the term in its context, perhaps splitting into
    ;; two cases (with the same context) [e.g., union or star rules] or perhaps
    ;; adding a new assumption [e.g., intersection or product rules].  We
    ;; generalize this slightly and allow both added assumptions and a list
    ;; of contextual cases.
    :returns (mv successp
                 (results tac-ruleres-branchlist-p)
                 (new-subst-database term-used-subst-database-p)
                 (subst-database-updatedp))
    :measure (pseudo-term-count x)
    :verify-guards nil
    (b* (((unless (pseudo-term-case x :fncall))
          (mv nil nil nil nil))
         ((pseudo-term-fncall x))
         (rettype (tac-function-return-type x.fn))
         ((unless (member-eq rettype '(:set :rel)))
          (mv nil nil nil nil))
         ((mv rewrittenp result)
          (pseudo-term-case x
            :fncall
            (tac-try-basic-rewrites (tac-rewrites) x.fn x.args)
            :otherwise (mv nil nil)))
         ((when rewrittenp)
          (mv t (list (tac-ruleres-branch nil result)) nil nil))
         ((term-used-subst-database subst-database))
         ((mv rewrittenp result new-rule-substs rule-substs-updatedp)
          (if (eq rettype :set)
              ;; note: important that x not contain variable tac-w
              (tac-rewrite-pred-try-rules ruleset x assums1 assums2 subst-database.rule-substs)
            (mv nil nil nil nil)))
         ((when rewrittenp)
          (mv t result
              (and rule-substs-updatedp
                   (change-term-used-subst-database subst-database :rule-substs new-rule-substs))
              rule-substs-updatedp))
         ((unless (tac-context-fn-p x.fn))
          (mv nil nil nil nil))
         ((mv successp results-args new-arg-substs arg-substs-updatedp)
          (tac-apply-rule-in-context-args
           0 (tac-function-argument-types x.fn) x.args assums1 assums2 ruleset subst-database.arg-substs))
         ((when successp)
          (mv t (apply-fn-to-result-branches
                 x.fn
                 (tac-ruleres-branchlistlist-to-branch-argslist results-args))
              (and arg-substs-updatedp
                   (change-term-used-subst-database subst-database :arg-substs new-arg-substs))
              arg-substs-updatedp)))
      (mv nil nil nil nil)))

  (define tac-apply-rule-in-context-args ((n natp)
                                          (types tac-typelist-p)
                                          (x pseudo-term-listp)
                                          (assums1 pseudo-term-listp)
                                          (assums2 pseudo-term-listp)
                                          (ruleset tac-rewritelist-p)
                                          (arg-substs arg-used-subst-database-p))
    :measure (pseudo-term-list-count x)
    :returns (mv successp
                 (results tac-ruleres-branchlistlist-p)
                 (new-arg-substs arg-used-subst-database-p)
                 (arg-substs-updatedp))
    (b* (((when (or (atom types)
                    (atom x)))
          (mv nil nil nil nil))
         (arg-substs (arg-used-subst-database-fix arg-substs))
         (term-substs (cdr (hons-assoc-equal (lnfix n) arg-substs)))
         ((mv successp results new-term-substs term-substs-updatedp)
          (tac-apply-rule-in-context (car x) assums1 assums2 ruleset term-substs))
         ((when successp)
          (mv t
              (cons results
                    (args-to-tac-ruleres-branchlistlist (take (1- (len types)) (cdr x))))
              (and term-substs-updatedp
                   (cons (cons (lnfix n) new-term-substs) arg-substs))
              term-substs-updatedp))
         ((mv successp results new-arg-substs arg-substs-updatedp)
          (tac-apply-rule-in-context-args (+ 1 (lnfix n)) (cdr types) (cdr x) assums1 assums2 ruleset arg-substs))
         ((when successp)
          (mv t (cons (list (tac-ruleres-branch nil (car x))) results)
              new-arg-substs arg-substs-updatedp)))
      (mv nil nil nil nil)))
  ///
  (local (in-theory (disable tac-apply-rule-in-context-args
                             tac-apply-rule-in-context)))
  (verify-guards tac-apply-rule-in-context)

  (local (defthm tac-ruleres-branchlist-typed-of-single
           (equal (tac-ruleres-branchlist-typed
                   (list (tac-ruleres-branch nil x))
                   type ctx)
                  (or (not (tac-type-fix type))
                      (equal (tac-term-type x ctx)
                             (tac-type-fix type))))
           :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-typed
                                             tac-ruleres-branch-typed)
                   :do-not-induct t))))
  
  (std::defret-mutual len-of-tac-apply-rule-in-context-args
    (defret len-of-<fn>
      (implies successp
               (equal (len results)
                      (len types)))
      :hints ('(:expand (<call>
                         (len types))))
      :fn tac-apply-rule-in-context-args)
    :skip-others t)

  (local (defthm tac-termlist-types-of-take
           (equal (tac-termlist-types (take n x) ctx)
                  (take n (tac-termlist-types x ctx)))
           :hints(("Goal" :in-theory (enable tac-termlist-types take)))))

  (local (defthm prefixp-of-take
           (implies (and (<= (len x) (nfix n))
                         (not (member-equal nil x)))
                    (iff (acl2::prefixp x (take n y))
                         (acl2::prefixp x y)))
           :hints(("Goal" :in-theory (enable acl2::prefixp take)))))

  
  (std::defret-mutual <fn>-preserves-type-lemma
    (defret <fn>-preserves-type-lemma
      (implies (and (tac-pred-rewrites-rhs-typed ruleset)
                    (tac-pred-rewrites-parse-ok ruleset)
                    (tac-term-type x ctx)
                    (subsetp-equal (tac-termlist-types assums1 ctx) '(:pred))
                    (subsetp-equal (tac-termlist-types assums2 ctx) '(:pred))
                    (not (member-equal 'tac-w (cmr::term-vars x)))
                    (not (member-equal 'tac-w (cmr::termlist-vars assums1)))
                    (not (member-equal 'tac-w (cmr::termlist-vars assums2)))
                    successp)
               (tac-ruleres-branchlist-typed results (tac-term-type x ctx) ctx))
      :hints ('(:expand (<call>
                         (cmr::term-vars x))
                :in-theory (enable tac-ruleres-branchlist-typed
                                   TAC-RULERES-BRANCH-TYPED
                                   tac-termlist-types)))
      :fn tac-apply-rule-in-context)
    (defret <fn>-preserves-type
      (implies (and (tac-pred-rewrites-rhs-typed ruleset)
                    (tac-pred-rewrites-parse-ok ruleset)
                    (tac-typelist-p types)
                    (not (member-equal nil types))
                    (acl2::prefixp types (tac-termlist-types x ctx))
                    (subsetp-equal (tac-termlist-types assums1 ctx) '(:pred))
                    (subsetp-equal (tac-termlist-types assums2 ctx) '(:pred))
                    (not (member-equal 'tac-w (cmr::termlist-vars x)))
                    (not (member-equal 'tac-w (cmr::termlist-vars assums1)))
                    (not (member-equal 'tac-w (cmr::termlist-vars assums2)))
                    successp)
               (tac-ruleres-branchlistlist-typed
                results types ctx))
      :hints ('(:expand (<call>
                         (:free (a b c) (acl2::prefixp a (cons b c)))
                         (cmr::termlist-vars x)
                         (:free (a b)
                          (tac-ruleres-branchlistlist-typed
                           (cons a b) types ctx)))
                :in-theory (enable tac-ruleres-branch-argslist-typed
                                   tac-termlist-types
                                   acl2::prefixp))
              ;; (and stable-under-simplificationp
              ;;      `(:expand (,(car (last clause))
              ;;                 (:free (a b c) (acl2::prefixp a (cons b c))))))
              )
      :fn tac-apply-rule-in-context-args))


  (defret <fn>-preserves-type
    (implies (and (tac-pred-rewrites-rhs-typed ruleset)
                  (tac-pred-rewrites-parse-ok ruleset)
                  (equal type (tac-term-type x ctx))
                  type
                  (subsetp-equal (tac-termlist-types assums1 ctx) '(:pred))
                  (subsetp-equal (tac-termlist-types assums2 ctx) '(:pred))
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums1)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums2)))
                  successp)
             (tac-ruleres-branchlist-typed results type ctx))
    :fn tac-apply-rule-in-context)

  (defret not-set-or-rel-type-implies-not-successp-<fn>
    (implies (and (not (equal (tac-function-return-type
                               (pseudo-term-fncall->fn x))
                              :set))
                  (not (equal (tac-function-return-type
                               (pseudo-term-fncall->fn x))
                              :rel)))
             (not successp))
    :hints(("Goal" :in-theory (enable tac-apply-rule-in-context)))
    :fn tac-apply-rule-in-context)

  (local (defthm tac-eval-ruleres-branchlist-singleton
           (implies (and (tac-typed-env-p env ctx)
                         (member-equal (tac-term-type x ctx) '(:set :rel)))
                    (equal (union-list
                            (tac-eval-ruleres-branchlist
                             (list (tac-ruleres-branch nil x))
                             env))
                           (tac-ev x env)))
           :hints(("Goal" :in-theory (enable tac-eval-ruleres-branchlist
                                             tac-eval-ruleres-branch
                                             tac-ev-cube
                                             union-list)))))

  (local (defthm take-when-prefixp
           (implies (acl2::prefixp x y)
                    (acl2::list-equiv (take (len x) y) x))
           :hints(("Goal" :in-theory (enable acl2::prefixp
                                             acl2::list-equiv)))))

  (local (defthm tac-ev-lst-of-take
           (equal (tac-ev-lst (take n x) a)
                  (take n (tac-ev-lst x a)))
           :hints(("Goal" :in-theory (enable take tac-ev-lst)))))

  (defthm tac-ev-apply-of-take-arg-types
    (implies (tac-function-return-type fn)
             (equal (tac-ev-apply fn (take (len (tac-function-argument-types fn)) args))
                    (tac-ev-apply fn args)))
    :hints(("Goal" :in-theory (enable tac-function-return-type))
           (and stable-under-simplificationp
                '(:in-theory (enable tac-ev-apply)))))
  
  (std::defret-mutual <fn>-eval
    (defret <fn>-eval-correct
      (implies (and ;; (member-equal (tac-term-type x ctx) '(:set :rel))
                    (tac-typed-env-p env ctx)
                    (tac-ev-theoremlist-p (tac-rewritelist-terms ruleset))
                    (tac-pred-rewrites-hyps-ok ruleset)
                    (tac-pred-rewrites-rhs-typed ruleset)
                    (tac-pred-rewrites-parse-ok ruleset)
                    (not (member-equal 'tac-w (cmr::term-vars x)))
                    (not (member-equal 'tac-w (cmr::termlist-vars assums1)))
                    (not (member-equal 'tac-w (cmr::termlist-vars assums2)))
                    (tac-term-type x ctx)
                    (subsetp-equal (tac-termlist-types assums1 ctx) '(:pred))
                    (subsetp-equal (tac-termlist-types assums2 ctx) '(:pred))
                    (tac-ev-cube assums1 env)
                    (tac-ev-cube assums2 env)
                    successp)
               (equal (union-list
                       (tac-eval-ruleres-branchlist results env))
                      (tac-ev x env)))
      :hints ('(:expand (<call>
                         (cmr::term-vars x))
                :do-not-induct t)
              (and stable-under-simplificationp
                   '(:expand ((tac-ev (cons (pseudo-term-fncall->fn x)
                                            (pseudo-term-call->args x))
                                      env)))))
      :fn tac-apply-rule-in-context)

    (defret <fn>-eval-correct
      (implies (and (tac-typed-env-p env ctx)
                    (tac-ev-theoremlist-p (tac-rewritelist-terms ruleset))
                    (tac-pred-rewrites-hyps-ok ruleset)
                    (tac-pred-rewrites-rhs-typed ruleset)
                    (tac-pred-rewrites-parse-ok ruleset)
                    (subsetp-equal types '(:set :rel))
                    (acl2::prefixp types (tac-termlist-types x ctx))
                    (subsetp-equal (tac-termlist-types assums1 ctx) '(:pred))
                    (subsetp-equal (tac-termlist-types assums2 ctx) '(:pred))
                    (not (member-equal 'tac-w (cmr::termlist-vars x)))
                    (not (member-equal 'tac-w (cmr::termlist-vars assums1)))
                    (not (member-equal 'tac-w (cmr::termlist-vars assums2)))
                    (tac-ev-cube assums1 env)
                    (tac-ev-cube assums2 env)
                    successp)
               (equal (union-multiarglists
                       (tac-eval-ruleres-branchlistlist results env))
                      (take (len types) (tac-ev-lst x env))))
      :hints ((and stable-under-simplificationp
                   '(:expand (<call>
                              (:free (a b) (union-multiarglists (cons a b)))
                              (subsetp-equal types '(:set :rel))
                              (:free (a b)
                               (tac-eval-ruleres-branchlistlist
                                (cons a b) env))
                              (cmr::termlist-vars x)
                              (tac-termlist-types x ctx)
                              (:free (a b) (acl2::prefixp types (cons a b))))
                     :do-not-induct t)))
      :fn tac-apply-rule-in-context-args))

  (local (defthm termlist-vars-of-take
           (implies (not (member-equal v (cmr::termlist-vars x)))
                    (not (member-equal v (cmr::termlist-vars (take n x)))))
           :hints(("Goal" :in-theory (enable cmr::termlist-vars take)))))

  (std::defret-mutual <fn>-preserves-vars
    (defret <fn>-preserves-vars
      (implies (and successp
                    (tac-pred-rewrites-parse-ok ruleset)
                    (not (member-equal v (cmr::term-vars x)))
                    (not (member-equal v (cmr::termlist-vars assums1)))
                    (not (member-equal v (cmr::termlist-vars assums2))))
               (not (member-equal v (tac-ruleres-branchlist-vars results))))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:expand ((cmr::term-vars x)
                              (:free (a b) (tac-ruleres-branchlist-vars (cons a b)))
                              (:free (a b) (tac-ruleres-branch-vars (tac-ruleres-branch a b)))))))
      :fn tac-apply-rule-in-context)
    (defret <fn>-preserves-vars
      (implies (and successp
                    (tac-pred-rewrites-parse-ok ruleset)
                    (not (member-equal v (cmr::termlist-vars x)))
                    (not (member-equal v (cmr::termlist-vars assums1)))
                    (not (member-equal v (cmr::termlist-vars assums2))))
               (not (member-equal v (tac-ruleres-branchlistlist-vars results))))
      :hints ('(:expand (<call>
                         (cmr::termlist-vars x)
                         (:free (a b) (tac-ruleres-branchlistlist-vars (cons a b)))
                         (:free (a b) (tac-ruleres-branchlist-vars (cons a b)))
                         (:free (a b) (tac-ruleres-branch-vars (tac-ruleres-branch a b))))))
      :fn tac-apply-rule-in-context-args))

  (fty::deffixequiv-mutual tac-apply-rule-in-context))
