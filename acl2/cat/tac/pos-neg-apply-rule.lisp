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

(include-book "pos-neg-rules")
(local (include-book "std/alists/hons-remove-assoc" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/alists/alist-equiv" :dir :system))
(local (std::add-default-post-define-hook :fix))

(local (defthm assoc-equal-is-hons-assoc-equal
         (implies k
                  (equal (assoc-equal k x)
                         (hons-assoc-equal k x)))))

(local (defthm prefixp-reflexive
         (acl2::prefixp x x)
         :hints(("Goal" :in-theory (enable acl2::prefixp)))))

(defsection hons-remove-assoc-of-unify

  #!cmr (flag::make-flag term-unify-strict :local t)
  (local (in-theory (disable cmr::term-unify-strict-reversible-iff-rw
                             cmr::termlist-unify-strict-reversible-iff-rw)))

  (local (defthm hons-remove-assoc-of-pseudo-term-subst-fix
           (equal (cmr::pseudo-term-subst-fix (acl2::hons-remove-assoc v alist))
                  (acl2::hons-remove-assoc v (cmr::pseudo-term-subst-fix alist)))
           :hints(("Goal" :in-theory (enable acl2::hons-remove-assoc
                                             cmr::pseudo-term-subst-fix)))))
  #!cmr
  (cmr::defthm-flag-term-unify-strict
    (defthm term-unify-strict-of-hons-remove-assoc
      (b* (((mv ok subst) (term-unify-strict pat x alist))
           ((mv ok1 subst1) (term-unify-strict pat x (acl2::hons-remove-assoc v alist))))
        (implies (and (not (member-equal v (term-vars pat)))
                      ok)
                 (and ok1
                      (equal (acl2::hons-remove-assoc v subst)
                             subst1))))
      :hints ('(:expand ((:free (alist) (term-unify-strict pat x alist))
                         (term-vars pat))))
      :flag term-unify-strict)
    (defthm termlist-unify-strict-of-hons-remove-assoc
      (b* (((mv ok subst) (termlist-unify-strict pat x alist))
           ((mv ok1 subst1) (termlist-unify-strict pat x (acl2::hons-remove-assoc v alist))))
        (implies (and (not (member-equal v (termlist-vars pat)))
                      ok)
                 (and ok1
                      (equal (acl2::hons-remove-assoc v subst)
                             subst1))))
      :hints ('(:expand ((:free (alist) (termlist-unify-strict pat x alist))
                         (termlist-vars pat))))
      :flag termlist-unify-strict)))


(defsection tac-ev-when-preserves-vars
  
  

  (local (defthm member-alist-keys
           (iff (member-equal v (acl2::alist-keys x))
                (hons-assoc-equal v x))
           :hints(("Goal" :in-theory (enable acl2::alist-keys)))))
  
  (cmr::defthm-term-vars-flag
    (defthm tac-ev-when-sub-alistp
      (implies (and (acl2::sub-alistp sub super)
                    (subsetp-equal (cmr::term-vars x)
                                   (acl2::alist-keys sub)))
               (equal (tac-ev x super)
                      (tac-ev x sub)))
      :hints ('(:expand ((cmr::term-vars x))
                :in-theory (enable tac-ev-of-fncall-args
                                   tac-ev-when-pseudo-term-call
                                   acl2::sub-alistp-hons-assoc-equal)))
      :flag cmr::term-vars)

    (defthm tac-ev-lst-when-sub-alistp
      (implies (and (acl2::sub-alistp sub super)
                    (subsetp-equal (cmr::termlist-vars x)
                                   (acl2::alist-keys sub)))
               (equal (tac-ev-lst x super)
                      (tac-ev-lst x sub)))
      :hints ('(:expand ((cmr::termlist-vars x))))
      :flag cmr::termlist-vars))

  (cmr::defthm-term-vars-flag
    (defthm term-subst-strict-when-sub-alistp
      (implies (and (acl2::sub-alistp (cmr::pseudo-term-subst-fix sub)
                                      (cmr::pseudo-term-subst-fix super))
                    (subsetp-equal (cmr::term-vars x)
                                   (acl2::alist-keys
                                    (cmr::pseudo-term-subst-fix sub))))
               (equal (cmr::term-subst-strict x super)
                      (cmr::term-subst-strict x sub)))
      :hints ('(:expand ((cmr::term-vars x)
                         (:free (s) (cmr::term-subst-strict x s)))
                :in-theory (enable acl2::sub-alistp-hons-assoc-equal)))
      :flag cmr::term-vars)

    (defthm termlist-subst-strict-when-sub-alistp
      (implies (and (acl2::sub-alistp (cmr::pseudo-term-subst-fix sub)
                                      (cmr::pseudo-term-subst-fix super))
                    (subsetp-equal (cmr::termlist-vars x)
                                   (acl2::alist-keys
                                    (cmr::pseudo-term-subst-fix sub))))
               (equal (cmr::termlist-subst-strict x super)
                      (cmr::termlist-subst-strict x sub)))
      :hints ('(:expand ((cmr::termlist-vars x)
                         (:free (s) (cmr::termlist-subst-strict x s)))))
      :flag cmr::termlist-vars))

  (local (defthm lookup-under-iff-when-sub-alistp
           (implies (and (acl2::sub-alistp (cmr::pseudo-term-subst-fix sub)
                                           (cmr::pseudo-term-subst-fix super))
                         (hons-assoc-equal var sub)
                         (pseudo-var-p var))
                    (hons-assoc-equal var super))
           :hints (("goal" :use ((:instance acl2::sub-alistp-hons-assoc-equal
                                  (x var) (a (cmr::pseudo-term-subst-fix sub))
                                  (b (cmr::pseudo-term-subst-fix super))))))))
  
  (local (defthm cdr-lookup-under-pseudo-term-equiv-when-sub-alistp
           (implies (and (acl2::sub-alistp (cmr::pseudo-term-subst-fix sub)
                                           (cmr::pseudo-term-subst-fix super))
                         (hons-assoc-equal var sub)
                         (pseudo-var-p var))
                    (pseudo-term-equiv (cdr (hons-assoc-equal var super))
                                       (cdr (hons-assoc-equal var sub))))
           :hints (("goal" :use ((:instance acl2::sub-alistp-hons-assoc-equal
                                  (x var) (a (cmr::pseudo-term-subst-fix sub))
                                  (b (cmr::pseudo-term-subst-fix super))))))))

  (defthm sub-alistp-of-tac-ev-alist
    (implies (acl2::sub-alistp (cmr::pseudo-term-subst-fix sub)
                               (cmr::pseudo-term-subst-fix super))
             (acl2::sub-alistp (tac-ev-alist sub a) (tac-ev-alist super a)))
    :hints(("goal" :in-theory (enable acl2::sub-alistp-iff-witness
                                      acl2::sub-alistp-hons-assoc-equal)
            :restrict ((acl2::sub-alistp-iff-witness
                        ((acl2::a (tac-ev-alist sub a))))))))

  (defthm sub-alistp-of-tac-ev-alist-no-fix
    (implies (and (acl2::sub-alistp (cmr::pseudo-term-subst-fix sub) super)
                  (cmr::pseudo-term-subst-p super))
             (acl2::sub-alistp (tac-ev-alist sub a) (tac-ev-alist super a)))
    :hints(("goal" :use ((:instance sub-alistp-of-tac-ev-alist))
            :in-theory (disable sub-alistp-of-tac-ev-alist))))

  (in-theory (disable tac-ev-when-sub-alistp
                      tac-ev-lst-when-sub-alistp)))


(fty::deflist pseudo-term-substlist :elt-type cmr::pseudo-term-subst :true-listp t)


(define tac-rewrite-pred-find-subst ((assums pseudo-term-listp)
                                     (hyp pseudo-termp)
                                     (unify-subst cmr::pseudo-term-subst-p)
                                     (used-unify-substs pseudo-term-substlist-p))
  ;; The hyp has some free variables and also potentially some variables bound
  ;; in unify-subst.  Find an assumption that unifies with hyp with the
  ;; starting unify-subst, and that isn't already used in used-unify-substs.
  :returns (new-subst cmr::pseudo-term-subst-p)
  (b* (((When (atom assums)) nil)
       ((mv ok subst) (cmr::term-unify-strict hyp (car assums) unify-subst))
       ((when (and ok
                   (not (member-equal subst (pseudo-term-substlist-fix used-unify-substs)))))
        subst))
    (tac-rewrite-pred-find-subst (cdr assums) hyp unify-subst used-unify-substs))
  ///
  (defret <fn>-preserves-bound-vars
    (implies (and new-subst
                  (hons-assoc-equal var unify-subst)
                  (pseudo-var-p var))
             (and (equal (hons-assoc-equal var new-subst)
                         (hons-assoc-equal var (cmr::pseudo-term-subst-fix unify-subst)))
                  (hons-assoc-equal var new-subst))))

  (defret sub-alistp-of-<fn>
    (implies new-subst
             (acl2::sub-alistp (cmr::pseudo-term-subst-fix unify-subst) new-subst))
    :hints(("Goal" :in-theory (enable acl2::sub-alistp-iff-witness))))

  (defret <fn>-correct
    (implies new-subst
             (member-equal (cmr::term-subst-strict hyp new-subst)
                           (pseudo-term-list-fix assums))))

  (local (defthm equal-of-pseudo-term-fix
           (implies (equal x (pseudo-term-fix y))
                    (acl2::pseudo-term-equiv x y))
           :rule-classes :forward-chaining))
  
  (local (defthm tac-term-type-of-tac-subst-ctx
           (equal (Tac-term-type x (tac-subst-ctx subst ctx))
                  (tac-term-type (cmr::term-subst-strict x subst) ctx))))
  (local (in-theory (disable tac-term-type-of-term-subst-strict)))
  
  (defret <fn>-type
    (implies (and new-subst
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred)))
             (equal (tac-term-type hyp (tac-subst-ctx new-subst ctx)) :pred))
    :hints(("Goal" :induct t
            :expand ((tac-termlist-types assums ctx)))))

  (defret <fn>-type-subst
    (implies (and new-subst
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred)))
             (equal (tac-term-type (cmr::term-subst-strict hyp new-subst) ctx) :pred))
    :hints (("goal" :use <fn>-type
             :in-theory (disable <fn> <fn>-type))))

  (defret tac-ev-of-tac-rewrite-pred-find-subst
    (implies (and (subsetp-equal (cmr::term-vars x)
                                 (acl2::alist-keys (cmr::pseudo-term-subst-fix unify-subst)))
                  new-subst)
             (equal (tac-ev x (tac-ev-alist new-subst env))
                    (tac-ev x (tac-ev-alist unify-subst env))))
    :hints(("Goal" :in-theory (e/d ()
                                   (<fn>))
            :use ((:instance tac-ev-when-sub-alistp
                   (x x)
                   (sub (tac-ev-alist unify-subst env))
                   (super (tac-ev-alist
                           (tac-rewrite-pred-find-subst
                            assums hyp unify-subst used-unify-substs)
                           env)))))))

  (defret tac-ev-lst-of-tac-rewrite-pred-find-subst
    (implies (and (subsetp-equal (cmr::termlist-vars x)
                                 (acl2::alist-keys (cmr::pseudo-term-subst-fix unify-subst)))
                  new-subst)
             (equal (tac-ev-lst x (tac-ev-alist new-subst env))
                    (tac-ev-lst x (tac-ev-alist unify-subst env))))
    :hints(("Goal" :in-theory (e/d ()
                                   (<fn>))
            :use ((:instance tac-ev-lst-when-sub-alistp
                   (x x)
                   (sub (tac-ev-alist unify-subst env))
                   (super (tac-ev-alist
                           (tac-rewrite-pred-find-subst
                            assums hyp unify-subst used-unify-substs)
                           env)))))))

  (defret termlist-subst-strict-of-tac-rewrite-pred-find-subst
    (implies (and (subsetp-equal (cmr::termlist-vars x)
                                 (acl2::alist-keys (cmr::pseudo-term-subst-fix unify-subst)))
                  new-subst)
             (equal (cmr::termlist-subst-strict x new-subst)
                    (cmr::termlist-subst-strict x unify-subst)))
    :hints(("Goal" :in-theory (e/d ()
                                   (<fn>))
            :use ((:instance termlist-subst-strict-when-sub-alistp
                   (x x)
                   (sub unify-subst)
                   (super (tac-rewrite-pred-find-subst
                           assums hyp unify-subst used-unify-substs)))))))
  

  (defret vars-of-<fn>
    (implies (and (not (member v (cmr::term-subst-vars unify-subst)))
                  (not (member v (cmr::termlist-vars assums))))
             (not (member v (cmr::term-subst-vars new-subst))))
    :hints (("goal" :induct <call>
             :expand ((cmr::termlist-vars assums)))))

  (defret tac-w-not-present-of-<fn>
    (implies (and (not (member 'tac-w (cmr::term-subst-vars
                                       (acl2::hons-remove-assoc 'w unify-subst))))
                  (not (member 'tac-w (cmr::termlist-vars assums)))
                  (not (member 'w (cmr::term-vars hyp))))
             (not (member 'tac-w (cmr::term-subst-vars
                                  (acl2::hons-remove-assoc 'w new-subst)))))
    :hints (("goal" :induct <call>
             :expand ((cmr::termlist-vars assums))))))



(define tac-rewrite-pred-subst ((rule cmr::rewrite-p)
                                (fn pseudo-fnsym-p)
                                (args pseudo-term-listp)
                                (assums pseudo-term-listp)
                                (used-unify-substs pseudo-term-substlist-p))
  :returns (mv ok (subst cmr::pseudo-term-subst-p))
  (b* (((cmr::rewrite rule))
       ((unless (pseudo-term-case rule.lhs
                  :fncall (eq rule.lhs.fn (pseudo-fnsym-fix fn))
                  :otherwise nil))
        (mv nil nil))
       ((mv ok subst1) (cmr::termlist-unify-strict (pseudo-term-call->args rule.lhs)
                                                   args nil))
       ((unless ok) (mv nil nil))
       ((unless (is-special-instantiation-rule rule))
        (mv t subst1))
       (hyp (special-instantiation-rule-binding-hyp rule))
       (new-subst (tac-rewrite-pred-find-subst assums hyp subst1 used-unify-substs))
       ((unless new-subst)
        (mv nil nil)))
    (mv t new-subst))
  ///
  (defret <fn>-lhs-subst
    (implies ok
             (equal (cmr::term-subst-strict
                     (cmr::rewrite->lhs rule) subst)
                    (pseudo-term-fncall fn args)))
    :hints (("goal" :expand ((:free (subst)
                              (cmr::term-subst-strict (cmr::rewrite->lhs rule) subst))))))

  (defret <fn>-lhs-eval
    (implies ok
             (equal (tac-ev (cmr::rewrite->lhs rule)
                            (tac-ev-alist subst env))
                    (tac-ev (pseudo-term-fncall fn args) env)))
    :hints (("goal" :use ((:instance tac-ev-of-term-subst-strict
                           (a (mv-nth 1 (tac-rewrite-pred-subst rule fn args assums used-unify-substs)))
                           (x (cmr::rewrite->lhs rule))))
             :in-theory (disable tac-ev-of-term-subst-strict
                                 <fn>))))

  (defret <fn>-hyp-member
    (implies (and (is-special-instantiation-rule rule)
                  ok)
             (member-equal (cmr::term-subst-strict
                            (special-instantiation-rule-binding-hyp rule) subst)
                           (pseudo-term-list-fix assums))))

  (local (defthm tac-ev-when-member-cube
           (implies (and (tac-ev-cube assums env)
                         (member-equal hyp (pseudo-term-list-fix assums)))
                    (tac-ev hyp env))
           :hints(("Goal" :in-theory (enable tac-ev-cube pseudo-term-list-fix)))))
  
  (defret <fn>-hyp-satisfied
    (implies (and (is-special-instantiation-rule rule)
                  (tac-ev-cube assums env)
                  ok)
             (tac-ev (special-instantiation-rule-binding-hyp rule)
                     (tac-ev-alist subst env)))
    :hints (("goal" :use ((:instance tac-ev-of-term-subst-strict
                           (a (mv-nth 1 (tac-rewrite-pred-subst rule fn args assums used-unify-substs)))
                           (x (special-instantiation-rule-binding-hyp rule))))
             :in-theory (disable tac-ev-of-term-subst-strict
                                 <fn>))))

  (local (defthm tac-term-type-of-term-subst-strict-inverse
           (equal (tac-term-type x (tac-subst-ctx y z))
                  (tac-term-type (cmr::term-subst-strict x y) z))))
  (local (in-theory (disable tac-term-type-of-term-subst-strict)))

  (local (defthm tac-term-type-when-member-and-subsetp-singleton
           (implies (and (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                         (member-equal hyp (pseudo-term-list-fix assums)))
                    (equal (tac-term-type hyp ctx) :pred))
           :hints(("Goal" 
                   :induct (len assums)
                   :expand ((pseudo-term-list-fix assums)
                            (tac-termlist-types assums ctx))))))
  
  (defret <fn>-typed
    (implies (and ok
                  (equal (tac-termlist-types args ctx)
                         (tac-function-argument-types fn)))
             (and (equal (tac-term-type (cmr::rewrite->lhs rule)
                                        (tac-subst-ctx subst ctx))
                         (tac-function-return-type fn))
                  (implies (and (is-special-instantiation-rule rule)
                                (subsetp-equal (tac-termlist-types assums ctx) '(:pred)))
                           (equal (tac-term-type (special-instantiation-rule-binding-hyp rule)
                                                 (tac-subst-ctx subst ctx))
                                  :pred))))
    :hints(("Goal" :in-theory (e/d ()
                                   (<fn>))
            :expand ((tac-term-type (pseudo-term-fncall fn args) ctx)))))

  (defret <fn>-implies-is-pred-in-set
    :pre-bind ((fn 'pred-in-set))
    (implies ok
             (is-pred-in-set (cmr::rewrite->lhs rule)))
    :hints(("Goal" :in-theory (enable is-pred-in-set)))
    :rule-classes :forward-chaining)

  (defret <fn>-binds-w-when-tac-pred-rewrite-parse-ok
    :pre-bind ((fn 'pred-in-set))
    (implies (And (tac-pred-rewrite-parse-ok rule)
                  ok)
             (hons-assoc-equal 'w subst))
    :hints(("Goal" :in-theory (enable tac-pred-rewrite-parse-ok
                                      is-pred-in-set
                                      is-pred-in-set-w)
            :expand ((CMR::TERMLIST-VARS (PSEUDO-TERM-CALL->ARGS (CMR::REWRITE->LHS RULE)))))))

  (defret <fn>-lookup-of-w-when-tac-pred-rewrite-parse-ok
    :pre-bind ((fn 'pred-in-set)
               (args (list 'tac-w x)))
    (implies (And (tac-pred-rewrite-parse-ok rule)
                  ok)
             (equal (cdr (hons-assoc-equal 'w subst))
                    'tac-w))
    :hints(("Goal" :in-theory (enable tac-pred-rewrite-parse-ok
                                      is-pred-in-set
                                      is-pred-in-set-w)
            :expand ((CMR::TERMLIST-VARS (PSEUDO-TERM-CALL->ARGS (CMR::REWRITE->LHS RULE)))
                     (:free (subst) (cmr::term-subst-strict 'w subst))
                     (:free (subst)
                      (cmr::termlist-subst-strict
                       (PSEUDO-TERM-CALL->ARGS (CMR::REWRITE->LHS RULE))
                       subst))))))
  (local (defthm hons-remove-assoc-when-not-present
           (implies (and (not (hons-assoc-equal v x))
                         (cmr::pseudo-term-subst-p x))
                    (equal (acl2::hons-remove-assoc v x) x))
           :hints(("Goal" :in-theory (enable acl2::hons-remove-assoc)))))
                    

  (defret tac-w-not-present-of-<fn>
    :pre-bind ((fn 'pred-in-set)
               (args (list 'tac-w x)))
    (implies (and (tac-pred-rewrite-parse-ok rule)
                  (not (member 'tac-w (cmr::term-vars x)))
                  (not (member 'tac-w (cmr::termlist-vars assums))))
             (not (member 'tac-w (cmr::term-subst-vars
                                  (acl2::hons-remove-assoc 'w subst)))))
    :hints (("goal" :in-theory (enable tac-pred-rewrite-parse-ok
                                       IS-PRED-IN-SET-W
                                       is-pred-in-set)
             :expand ((:free (args a b subst)
                       (cmr::termlist-unify-strict args (cons a b) subst))
                      (:free (args subst)
                       (cmr::termlist-unify-strict args nil subst))))))

  (defret vars-of-<fn>
    (implies (and (not (member v (cmr::termlist-vars args)))
                  (not (member v (cmr::termlist-vars assums))))
             (not (member v (cmr::term-subst-vars subst))))))
               
    


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
    :flag tac-termlist-types))



(define tac-rewrite-pred-apply-rule ((rule cmr::rewrite-p)
                                     (x pseudo-termp)
                                     (assums pseudo-term-listp)
                                     (used-unify-substs pseudo-term-substlist-p))
  :returns (mv ok
               (result tac-ruleres-branchlist-p)
               (subst cmr::pseudo-term-subst-p))
  (b* (((cmr::rewrite rule))
       ((unless (and (or (eq rule.equiv 'equal)
                         (eq rule.equiv 'iff))))
        (mv nil nil nil))
       ((mv ok subst) (tac-rewrite-pred-subst rule 'pred-in-set (list 'tac-w x)
                                              assums used-unify-substs))
       ((unless ok) (mv nil nil nil))
       ((mv ok res-pattern) (tac-parse-ruleres rule.rhs))
       ((unless ok) (mv nil nil nil))
       (res (tac-subst-ruleres-branchlist res-pattern subst)))
    (mv t res subst))
  ///
  (local (in-theory (enable tac-ev-of-fncall-args)))
  
  (local (defthm hons-assoc-equal-when-cdr-hons-assoc-equal
           (implies (cdr (hons-assoc-equal k x))
                    (hons-assoc-equal k x))
           :rule-classes :forward-chaining))
  
  (defret <fn>-correct-lemma
    (implies (and ok
                  (tac-ev-theoremp* (cmr::rewrite-term rule))
                  (tac-pred-rewrite-hyps-ok rule)
                  (tac-typed-env-p env ctx)
                  (tac-ev-cube assums env)
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  ;; (equal (tac-termlist-types args ctx)
                  ;;        (tac-function-argument-types fn))
                  ;; (equal (tac-function-return-type fn) :pred)
                  (equal (tac-term-type x ctx) :set)
                  (equal (cdr (hons-assoc-equal 'tac-w ctx)) :event)
                  (tac-pred-rewrite-parse-ok rule))
             (iff (in (cdr (assoc 'tac-w env))
                      (union-list
                       (tac-eval-ruleres-branchlist result env)))
                  (in (cdr (assoc 'tac-w env))
                      (tac-ev x env))))
    :hints (("goal" :use ((:instance tac-parse-ruleres-correct
                           (x (cmr::rewrite->rhs rule))
                           (env
                            (tac-ev-alist
                             (mv-nth 1 (tac-rewrite-pred-subst rule 'pred-in-set (list 'tac-w x)
                                                               assums used-unify-substs))
                             env)))
                          (:instance tac-ev-theoremp*-implies
                           (x (cmr::rewrite-term rule))
                           (a (tac-ev-alist
                               (mv-nth 1 (tac-rewrite-pred-subst rule 'pred-in-set (list 'tac-w x)
                                                                 assums used-unify-substs))
                               env)))
                          (:instance tac-pred-rewrite-hyps-ok-necc
                           (env (tac-ev-alist
                                   (mv-nth 1 (tac-rewrite-pred-subst rule 'pred-in-set (list 'tac-w x)
                                                                     assums used-unify-substs))
                                   env))
                           (ctx (tac-subst-ctx
                                 (mv-nth 1 (tac-rewrite-pred-subst rule 'pred-in-set (list 'tac-w x)
                                                                   assums used-unify-substs))
                                 ctx)))
                          )
             :expand ((:free (a b) (tac-termlist-types (cons a b) ctx))
                      (tac-termlist-types nil ctx))
             :in-theory (enable cmr::rewrite-term))))

  (local (DEFTHM TAC-PRED-REWRITE-RHS-TYPED-NECC-force
           (IMPLIES
            (TAC-PRED-REWRITE-RHS-TYPED RULE)
            (B* (((CMR::REWRITE RULE))
                 (LHS-TYPE (TAC-TERM-TYPE RULE.LHS CTX))
                 ((MV OK RHS-PARSED)
                  (TAC-PARSE-RULERES RULE.RHS)))
              (IMPLIES
               (AND
                LHS-TYPE (IS-PRED-IN-SET RULE.LHS)
                (case-split (LET*
                             ((BINDING-HYP
                               (AND (IS-SPECIAL-INSTANTIATION-RULE RULE)
                                    (SPECIAL-INSTANTIATION-RULE-BINDING-HYP RULE))))
                             (OR (NOT BINDING-HYP)
                                 (TAC-TERM-TYPE BINDING-HYP CTX)))))
               (AND OK
                    (TAC-RULERES-BRANCHLIST-TYPED RHS-PARSED
                                                  :SET CTX)))))))
  
  (defret <fn>-type-lemma
    (implies (and ok
                  (tac-pred-rewrite-rhs-typed rule)
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  (equal (tac-term-type x ctx) :set)
                  (equal (cdr (hons-assoc-equal 'tac-w ctx)) :event))
             (tac-ruleres-branchlist-typed result :set ctx))
    :hints (("goal" 
             :expand ((:free (a b) (tac-termlist-types (cons a b) ctx))
                      (tac-termlist-types nil ctx)))))

  (local (defthm member-term-subst-vars-of-hons-remove-assoc
           (implies (not (member v (cmr::term-subst-vars x)))
                    (not (member v (cmr::term-subst-vars (acl2::hons-remove-assoc v1 x)))))
           :hints(("Goal" :in-theory (enable cmr::term-subst-vars
                                             acl2::hons-remove-assoc)))))
  
  (defret <fn>-does-not-introduce-vars
    (implies (and ok
                  (tac-pred-rewrite-parse-ok rule)
                  (not (member-equal v (cmr::term-vars x)))
                  (not (member-equal v (cmr::termlist-vars assums))))
             (not (member-equal v (tac-ruleres-branchlist-vars result))))
    :hints(("Goal" :in-theory (e/d (tac-pred-rewrite-parse-ok-implies)
                                   (;; tac-subst-ruleres-branchlist-of-remove-unused
                                    vars-of-tac-subst-ruleres-branchlist))
            :cases ((equal v 'tac-w))
            :expand ((:free (a b) (cmr::termlist-vars (cons a b))))
            :use ((:instance vars-of-tac-subst-ruleres-branchlist
                   (x (mv-nth 1 (tac-parse-ruleres (cmr::rewrite->rhs rule))))
                   (subst (acl2::hons-remove-assoc
                           'w
                           (mv-nth 1 (tac-rewrite-pred-subst
                                      rule 'pred-in-set (list 'tac-w x)
                                      assums used-unify-substs)))))))))
    
                  
  
  (defret <fn>-type
    (implies (and ok
                  (tac-pred-rewrite-rhs-typed rule)
                  (tac-pred-rewrite-parse-ok rule)
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  (equal (tac-term-type x ctx) :set)
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums))))
             (tac-ruleres-branchlist-typed result :set ctx))
    :hints (("goal" :use ((:instance <fn>-type-lemma
                           (ctx (cons (cons 'tac-w :event) ctx))))
             :in-theory (disable <fn> <fn>-type-lemma))))
                  

  
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

  (local (defthm non-event-in-typed-val
           (implies (and (tac-typed-val-p x :set)
                         (not (tac-typed-val-p e :event)))
                    (not (in e x)))
           :hints(("Goal" :in-theory (enable tac-typed-val-p)))))
  
  (defret <fn>-correct
    (implies (and ok
                  (tac-ev-theoremp* (cmr::rewrite-term rule))
                  (tac-pred-rewrite-hyps-ok rule)
                  (tac-typed-env-p env ctx)
                  (tac-ev-cube assums env)
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  ;; (equal (tac-termlist-types args ctx)
                  ;;        (tac-function-argument-types fn))
                  ;; (equal (tac-function-return-type fn) :pred)
                  (equal (tac-term-type x ctx) :set)
                  (tac-pred-rewrite-parse-ok rule)
                  (tac-pred-rewrite-rhs-typed rule)
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums))))
             (equal (union-list
                     (tac-eval-ruleres-branchlist result env))
                    (tac-ev x env)))
    :hints (("goal" :in-theory (e/d (set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy)
                                    (<fn> <fn>-correct-lemma)))
            (set::pick-a-point-subset-hint id clause world stable-under-simplificationp)
            (and stable-under-simplificationp
                 '(:use ((:instance <fn>-correct-lemma
                          (env (cons (cons 'tac-w set::arbitrary-element) env))
                          (ctx (cons (cons 'tac-w :event) ctx)))))))))

(fty::defmap rule-used-substs :key-type symbolp :val-type pseudo-term-substlist-p :true-listp t)

(define tac-rewrite-pred-try-rules ((rules tac-rewritelist-p)
                                    (x pseudo-termp)
                                    (assums pseudo-term-listp)
                                    (rule-used-substs rule-used-substs-p))
  :returns (mv ok
               (result tac-ruleres-branchlist-p)
               (new-rule-used-substs rule-used-substs-p)
               (rule-used-substs-updatedp))
  (b* (((when (atom rules)) (mv nil nil nil nil))
       ((unless (mbt (consp (car rules))))
        (tac-rewrite-pred-try-rules (cdr rules) x assums rule-used-substs))
       ((cons name rule) (car rules))
       (name (mbe :logic (acl2::symbol-fix name) :exec name))
       (rule-used-substs (rule-used-substs-fix rule-used-substs))
       (used-substs (cdr (hons-assoc-equal name rule-used-substs)))
       ((mv ok result subst) (tac-rewrite-pred-apply-rule rule x assums used-substs))
       ((unless ok) (tac-rewrite-pred-try-rules (cdr rules) x assums rule-used-substs)))
    (if (is-special-instantiation-rule rule)
        (mv t result (cons (cons name (cons subst used-substs)) rule-used-substs) t)
      (mv t result nil nil)))
  ///

  (defret <fn>-does-not-introduce-vars
    (implies (and ok
                  (tac-pred-rewrites-parse-ok rules)
                  (not (member-equal v (cmr::term-vars x)))
                  (not (member-equal v (cmr::termlist-vars assums))))
             (not (member-equal v (tac-ruleres-branchlist-vars result))))
    :hints(("Goal" :in-theory (enable tac-pred-rewrites-parse-ok))))
    
                  
  
  (defret <fn>-type
    (implies (and ok
                  (tac-pred-rewrites-rhs-typed rules)
                  (tac-pred-rewrites-parse-ok rules)
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  (equal (tac-term-type x ctx) :set)
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums))))
             (tac-ruleres-branchlist-typed result :set ctx))
    :hints (("goal" :in-theory (enable tac-pred-rewrites-rhs-typed
                                       tac-pred-rewrites-parse-ok))))
                  

  
  (defret <fn>-correct
    (implies (and ok
                  (tac-ev-theoremlist-p (tac-rewritelist-terms rules))
                  (tac-pred-rewrites-hyps-ok rules)
                  (tac-typed-env-p env ctx)
                  (tac-ev-cube assums env)
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  ;; (equal (tac-termlist-types args ctx)
                  ;;        (tac-function-argument-types fn))
                  ;; (equal (tac-function-return-type fn) :pred)
                  (equal (tac-term-type x ctx) :set)
                  (tac-pred-rewrites-parse-ok rules)
                  (tac-pred-rewrites-rhs-typed rules)
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums))))
             (equal (union-list
                     (tac-eval-ruleres-branchlist result env))
                    (tac-ev x env)))
    :hints (("goal" :in-theory (enable tac-ev-theoremlist-p
                                       tac-rewritelist-terms
                                       tac-pred-rewrites-hyps-ok
                                       tac-pred-rewrites-parse-ok
                                       tac-pred-rewrites-rhs-typed))))

  (local (in-theory (enable tac-rewritelist-fix))))
