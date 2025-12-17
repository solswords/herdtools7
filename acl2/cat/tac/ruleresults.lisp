;;****************************************************************************;;
;;                                ASLRef                                      ;;
;;****************************************************************************;;
;;
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
(include-book "terms")
(include-book "centaur/meta/subst-vars" :dir :system)
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defprod tac-ruleres-branch
  ((assums pseudo-term-listp)
   (ctx-result pseudo-termp)))

;; all disjoined
(deflist tac-ruleres-branchlist :elt-type tac-ruleres-branch :true-listp t)

;; list of disjoined branches for arguments
(deflist tac-ruleres-branchlistlist :elt-type tac-ruleres-branchlist :true-listp t)

(defprod tac-ruleres-branch-args
  ((assums pseudo-term-listp)
   (ctx-result-args pseudo-term-listp)))

(deflist tac-ruleres-branch-argslist :elt-type tac-ruleres-branch-args :true-listp t)


;; ------------- Types of tac-ruleres objects


(define tac-ruleres-branch-typed ((x tac-ruleres-branch-p)
                                               (type tac-type-p)
                                               (ctx type-ctx-p))
  (b* (((tac-ruleres-branch x)))
    (and (subsetp (tac-termlist-types x.assums ctx) '(:pred))
         (let ((type (tac-type-fix type)))
           (or (not type)
               (equal (tac-term-type x.ctx-result ctx) type)))))
  ///
  (defthm tac-ruleres-branch-typed-when-nil
    (implies (tac-ruleres-branch-typed x type ctx)
             (tac-ruleres-branch-typed x nil ctx))))

(define tac-ruleres-branchlist-typed ((x tac-ruleres-branchlist-p)
                                                   (type tac-type-p)
                                                   (ctx type-ctx-p))
  (if (atom x)
      t
    (and (tac-ruleres-branch-typed (car x) type ctx)
         (tac-ruleres-branchlist-typed (cdr x) type ctx)))
  ///
  (defthm tac-ruleres-branchlist-typed-of-append
    (iff (tac-ruleres-branchlist-typed (append x y) type ctx)
         (and (tac-ruleres-branchlist-typed x type ctx)
              (tac-ruleres-branchlist-typed y type ctx))))
  
  (defthm tac-ruleres-branchlist-typed-when-nil
    (implies (tac-ruleres-branchlist-typed x type ctx)
             (tac-ruleres-branchlist-typed x nil ctx))))

(define tac-ruleres-branchlistlist-typed ((x tac-ruleres-branchlistlist-p)
                                                       (types tac-typelist-p)
                                                       (ctx type-ctx-p))
  (if (atom types)
      t
    (and (consp x)
         (tac-ruleres-branchlist-typed (car x) (car types) ctx)
         (tac-ruleres-branchlistlist-typed (cdr x) (cdr types) ctx))))

(define tac-ruleres-branch-args-typed ((x tac-ruleres-branch-args-p)
                                                    (types tac-typelist-p)
                                                    (ctx type-ctx-p))
  (b* (((tac-ruleres-branch-args x)))
    (and (subsetp (tac-termlist-types x.assums ctx) '(:pred))
         (acl2::prefixp (tac-typelist-fix types) (tac-termlist-types x.ctx-result-args ctx))))
  ///
  (defthm tac-ruleres-branch-args-typed-of-nil
    (implies (tac-ruleres-branch-args-typed x types ctx)
             (tac-ruleres-branch-args-typed x nil ctx))
    :hints(("Goal" :in-theory (enable acl2::prefixp)))))

(define tac-ruleres-branch-argslist-typed ((x tac-ruleres-branch-argslist-p)
                                                        (types tac-typelist-p)
                                                        (ctx type-ctx-p))
  (if (atom x)
      t
    (and (tac-ruleres-branch-args-typed (car x) types ctx)
         (tac-ruleres-branch-argslist-typed (cdr x) types ctx)))
  ///
  (defthm tac-ruleres-branch-argslist-typed-of-nil
    (implies (tac-ruleres-branch-argslist-typed x types ctx)
             (tac-ruleres-branch-argslist-typed x nil ctx)))

  (defthm tac-ruleres-branch-argslist-typed-of-append
    (implies (and (tac-ruleres-branch-argslist-typed x types ctx)
                  (tac-ruleres-branch-argslist-typed y types ctx))
             (tac-ruleres-branch-argslist-typed (append x y) types ctx))))

;; ------------- Evaluation of of tac-ruleres objects

(define tac-eval-ruleres-branch ((x tac-ruleres-branch-p)
                                              env)
  :verify-guards nil
  (b* (((tac-ruleres-branch x)))
    (and (tac-ev-cube x.assums env)
         (tac-ev x.ctx-result env)))
  ///
  (defthm relation-p-of-tac-eval-ruleres-branch-by-type
    (implies (and (tac-ruleres-branch-typed x :rel ctx)
                  (tac-typed-env-p env ctx))
             (relation-p (tac-eval-ruleres-branch x env)))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-typed))))

  (defthm tac-typed-val-p-of-tac-eval-ruleres-branch-by-type
    (implies (and (tac-ruleres-branch-typed x type ctx)
                  (member-equal type '(:set :rel))
                  (tac-typed-env-p env ctx))
             (tac-typed-val-p (tac-eval-ruleres-branch x env) type))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-typed
                                      tac-typed-val-p)))))



(define tac-eval-ruleres-branchlist ((x tac-ruleres-branchlist-p)
                                                  env)
  :verify-guards nil
  :returns (vals true-listp :rule-classes :type-prescription)
  (if (atom x)
      nil
    (cons (tac-eval-ruleres-branch (car x) env)
          (tac-eval-ruleres-branchlist (cdr x) env)))
  ///
  (defthm tac-eval-ruleres-branchlist-of-append
    (equal (tac-eval-ruleres-branchlist (append x y) env)
           (append (tac-eval-ruleres-branchlist x env)
                   (tac-eval-ruleres-branchlist y env))))
  

  (defthm tac-1typed-vallist-p-of-tac-eval-ruleres-branch-by-type
    (implies (and (tac-typed-env-p env ctx)
                  (tac-ruleres-branchlist-typed x type ctx)
                  (member-equal type '(:set :rel)))
             (tac-1typed-vallist-p (tac-eval-ruleres-branchlist x env) type))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-typed
                                      tac-1typed-vallist-p)))))

(define tac-typed-multiarglist-p ((x true-list-listp) (types tac-typelist-p))
  :measure (len types)
  (if (atom types)
      t
    (and (tac-1typed-vallist-p (car x) (car types))
         (tac-typed-multiarglist-p (cdr x) (cdr types)))))

(define tac-eval-ruleres-branchlistlist ((x tac-ruleres-branchlistlist-p)
                                                      env)
  :verify-guards nil
  :returns (vals true-list-listp)
  (if (atom x)
      nil
    (cons (tac-eval-ruleres-branchlist (car x) env)
          (tac-eval-ruleres-branchlistlist (cdr x) env)))
  ///
  (defthm tac-eval-ruleres-branchlistli-of-append
    (equal (tac-eval-ruleres-branchlistlist (append x y) env)
           (append (tac-eval-ruleres-branchlistlist x env)
                   (tac-eval-ruleres-branchlistlist y env))))

  (defthm tac-typed-multiarglist-p-of-tac-eval-ruleres-branchlistlist
    (implies (and (tac-typed-env-p env ctx)
                  (tac-ruleres-branchlistlist-typed x types ctx)
                  (subsetp-equal types '(:set :rel)))
             (tac-typed-multiarglist-p (tac-eval-ruleres-branchlistlist x env) types))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlistlist-typed
                                      tac-typed-multiarglist-p
                                      subsetp-equal))))

  (defret len-of-<fn>
    (equal (len vals) (len x))))



(local (include-book "std/lists/repeat" :dir :system))

(define tac-eval-ruleres-branch-args ((x tac-ruleres-branch-args-p)
                                                   env)
  :verify-guards nil
  (b* (((tac-ruleres-branch-args x)))
    (if (tac-ev-cube x.assums env)
        (tac-ev-lst x.ctx-result-args env)
      (make-list (len x.ctx-result-args) :initial-element nil)))
  ///
  (local (include-book "std/lists/repeat" :dir :system))
  (local (defthm tac-typed-vallist-p-repeat-nil
           (implies (and (subsetp-equal types '(:set :rel)))
                    (tac-typed-vallist-p (acl2::repeat n nil) types))
           :hints(("Goal" :in-theory (enable tac-typed-vallist-p
                                             acl2::repeat)
                   :induct (nthcdr n types)))))

  (local (defthmd prefixp-implies-len
           (implies (acl2::prefixp x y)
                    (<= (len x) (len y)))
           :hints(("Goal" :in-theory (enable acl2::prefixp)))))

  (local (defun cdr-cdr-ind (x y)
           (if (atom x)
               y
             (cdr-cdr-ind (cdr x) (cdr y)))))

  ;; (local (defthm equal-tac-type-fix-forward
  ;;          (implies (equal (tac-type-fix x) y)
  ;;                   (tac-type-equiv x y))
  ;;          :rule-classes :forward-chaining))

  (defthm len-of-tac-termlist-types
    (equal (len (tac-termlist-types x ctx))
           (len x))
    :hints(("Goal" :in-theory (enable tac-termlist-types))))
  
  (defthm tac-typed-vallist-p-when-prefixp-types
    (implies (and (acl2::prefixp (tac-typelist-fix types) (tac-termlist-types x ctx))
                  (tac-typed-env-p env ctx))
             (tac-typed-vallist-p (tac-ev-lst x env) types))
    :hints(("Goal" :induct (cdr-cdr-ind types x)
            :in-theory (enable acl2::prefixp tac-termlist-types tac-typed-vallist-p
                               tac-typelist-fix))
           (and stable-under-simplificationp
                '(:use ((:instance tac-typed-val-p-when-term-type
                         (x (car x))))
                  :in-theory (disable tac-typed-val-p-when-term-type)))))

  
  (defthm tac-typed-vallist-p-of-tac-eval-ruleres-branch-args
    (implies (and (tac-ruleres-branch-args-typed x types ctx)
                  (tac-typed-env-p env ctx)
                  (subsetp-equal types '(:set :rel)))
             (tac-typed-vallist-p (tac-eval-ruleres-branch-args x env) types))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-args-typed)
            :use ((:instance prefixp-implies-len
                   (x (tac-typelist-fix types))
                   (y (tac-termlist-types (tac-ruleres-branch-args->ctx-result-args x) ctx))))))))

(define tac-eval-ruleres-branch-argslist ((x tac-ruleres-branch-argslist-p)
                                                       env)
  :verify-guards nil
  (if (atom x)
      nil
    (cons (tac-eval-ruleres-branch-args (car x) env)
          (tac-eval-ruleres-branch-argslist (cdr x) env)))
  ///
  (defthm tac-eval-ruleres-branch-argslist-of-append
    (equal (tac-eval-ruleres-branch-argslist (append x y) env)
           (append (tac-eval-ruleres-branch-argslist x env)
                   (tac-eval-ruleres-branch-argslist y env)))))



;; ------------ Variables of tac-ruleres objects
(local (Defthm union-of-pseudo-var-list
         (implies (and (cmr::pseudo-var-list-p x)
                       (cmr::pseudo-var-list-p y))
                  (cmr::pseudo-var-list-p (union-equal x y)))))

(local (defthm symbol-listp-when-pseudo-var-list-p
         (implies (cmr::pseudo-var-list-p x)
                  (symbol-listp x))))

(cmr::defthm-term-vars-flag
  (defthm tac-ev-of-cons-non-var
    (implies (not (member-equal v (cmr::term-vars x)))
             (equal (tac-ev x (cons (cons v val) env))
                    (tac-ev x env)))
    :hints ('(:expand ((cmr::term-vars x))
              :in-theory (enable tac-ev-when-pseudo-term-call)))
    :flag cmr::term-vars)
  (defthm tac-ev-lst-of-cons-non-var
    (implies (not (member-equal v (cmr::termlist-vars x)))
             (equal (tac-ev-lst x (cons (cons v val) env))
                    (tac-ev-lst x env)))
    :hints ('(:expand ((cmr::termlist-vars x))))
    :flag cmr::termlist-vars))

(defthm eval-cons-non-var-of-cube
  (implies (not (member-equal v (cmr::termlist-vars cube)))
           (equal (tac-ev-cube cube (cons (cons v val) env))
                  (tac-ev-cube cube env)))
  :hints(("Goal" :in-theory (enable tac-ev-cube cmr::termlist-vars))))

(define tac-ruleres-branch-vars ((x tac-ruleres-branch-p))
  :returns (vars cmr::pseudo-var-list-p)
  (b* (((tac-ruleres-branch x)))
    (union-eq (cmr::termlist-vars x.assums)
              (cmr::term-vars x.ctx-result)))
  ///
  (defret eval-cons-non-var-of-<fn>
    (implies (not (member-equal v vars))
             (equal (tac-eval-ruleres-branch x (cons (cons v val) env))
                    (tac-eval-ruleres-branch x env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch))))

  (defthm tac-ruleres-branch-typed-of-add-unused-var
    (implies (not (member-equal v (tac-ruleres-branch-vars x)))
             (equal (tac-ruleres-branch-typed x type (cons (cons v vtype) ctx))
                    (tac-ruleres-branch-typed x type ctx)))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-typed
                                      tac-ruleres-branch-vars)))))


(define tac-ruleres-branchlist-vars ((x tac-ruleres-branchlist-p))
  :returns (vars cmr::pseudo-var-list-p)
  (if (atom x)
      nil
    (union-eq (tac-ruleres-branch-vars (car x))
              (tac-ruleres-branchlist-vars (cdr x))))
  ///
  (defret eval-cons-non-var-of-<fn>
    (implies (not (member-equal v vars))
             (equal (tac-eval-ruleres-branchlist x (cons (cons v val) env))
                    (tac-eval-ruleres-branchlist x env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branchlist))))

  (defthm tac-ruleres-branchlist-typed-of-add-unused-var
    (implies (not (member-equal v (tac-ruleres-branchlist-vars x)))
             (equal (tac-ruleres-branchlist-typed x type (cons (cons v vtype) ctx))
                    (tac-ruleres-branchlist-typed x type ctx)))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-typed
                                      tac-ruleres-branchlist-vars)))))

(define tac-ruleres-branchlistlist-vars ((x tac-ruleres-branchlistlist-p))
  :returns (vars cmr::pseudo-var-list-p)
  (if (atom x)
      nil
    (union-eq (tac-ruleres-branchlist-vars (car x))
              (tac-ruleres-branchlistlist-vars (cdr x)))))


(define tac-ruleres-branch-args-vars ((x tac-ruleres-branch-args-p))
  :returns (vars cmr::pseudo-var-list-p)
  (b* (((tac-ruleres-branch-args x)))
    (union-eq (cmr::termlist-vars x.assums)
              (cmr::termlist-vars x.ctx-result-args))))

(define tac-ruleres-branch-argslist-vars ((x tac-ruleres-branch-argslist-p))
  :returns (vars cmr::pseudo-var-list-p)
  (if (atom x)
      nil
    (union-eq (tac-ruleres-branch-args-vars (car x))
              (tac-ruleres-branch-argslist-vars (cdr x)))))


;; Interlude for reasoning about removing a variable from a substitution
(local (include-book "std/alists/hons-remove-assoc" :dir :system))

(defsection hons-remove-assoc-lemmas
  
  
  (local (defthm assoc-equal-is-hons-assoc-equal
           (implies k
                    (equal (assoc-equal k x)
                           (hons-assoc-equal k x)))))


  
  (cmr::defthm-term-vars-flag
    (defthm term-subst-strict-of-remove-non-term-var
      (implies (not (member-equal v (cmr::term-vars x)))
               (equal (cmr::term-subst-strict x (acl2::hons-remove-assoc v subst))
                      (cmr::term-subst-strict x subst)))
      :hints ('(:expand ((cmr::term-vars x)
                         (:free (Subst) (cmr::term-subst-strict x subst)))))
      :flag cmr::term-vars)
    (defthm termlist-subst-strict-of-remove-non-term-var
      (implies (not (member-equal v (cmr::termlist-vars x)))
               (equal (cmr::termlist-subst-strict x (acl2::hons-remove-assoc v subst))
                      (cmr::termlist-subst-strict x subst)))
      :hints ('(:expand ((cmr::termlist-vars x)
                         (:free (Subst) (cmr::termlist-subst-strict x subst)))))
      :flag cmr::termlist-vars)))

;; ------------- Substitution into tac-ruleres objects

(define tac-subst-ruleres-branch ((x tac-ruleres-branch-p)
                                  (subst cmr::pseudo-term-subst-p))
  :returns (new-x tac-ruleres-branch-p)
  (b* (((tac-ruleres-branch x)))
    (tac-ruleres-branch
     (cmr::termlist-subst-strict x.assums subst)
     (cmr::term-subst-strict x.ctx-result subst)))
  ///
  (defret eval-of-<fn>
    (equal (tac-eval-ruleres-branch new-x env)
           (tac-eval-ruleres-branch x (tac-ev-alist subst env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch))))

  (defret tac-ruleres-branch-typed-of-<fn>
    (implies (tac-ruleres-branch-typed x type (tac-subst-ctx subst ctx))
             (tac-ruleres-branch-typed new-x type ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-typed))))

  (defret vars-of-<fn>
    (implies (not (member-equal v (cmr::term-subst-vars subst)))
             (not (member-equal v (tac-ruleres-branch-vars new-x))))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-vars))))

  (defret <fn>-of-remove-unused
    (implies (not (member-equal v (tac-ruleres-branch-vars x)))
             (equal (tac-subst-ruleres-branch x (acl2::hons-remove-assoc v subst))
                    new-x))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-vars)))))

(define tac-subst-ruleres-branchlist ((x tac-ruleres-branchlist-p)
                                      (subst cmr::pseudo-term-subst-p))
  :returns (new-x tac-ruleres-branchlist-p)
  (if (atom x)
      nil
    (cons (tac-subst-ruleres-branch (car x) subst)
          (tac-subst-ruleres-branchlist (cdr x) subst)))
  ///
  (defthm tac-subst-ruleres-branchlist-of-append
    (equal (tac-subst-ruleres-branchlist (append x y) env)
           (append (tac-subst-ruleres-branchlist x env)
                   (tac-subst-ruleres-branchlist y env))))

  (defret eval-of-<fn>
    (equal (tac-eval-ruleres-branchlist new-x env)
           (tac-eval-ruleres-branchlist x (tac-ev-alist subst env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branchlist))))
  

  (defret tac-ruleres-branchlist-typed-of-<fn>
    (implies (tac-ruleres-branchlist-typed x type (tac-subst-ctx subst ctx))
             (tac-ruleres-branchlist-typed new-x type ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-typed))))

  (defret len-of-<fn>
    (equal (len new-x) (len x)))

  (defret vars-of-<fn>
    (implies (not (member-equal v (cmr::term-subst-vars subst)))
             (not (member-equal v (tac-ruleres-branchlist-vars new-x))))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-vars))))

  (defret <fn>-of-remove-unused
    (implies (not (member-equal v (tac-ruleres-branchlist-vars x)))
             (equal (tac-subst-ruleres-branchlist x (acl2::hons-remove-assoc v subst))
                    new-x))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-vars)))))

(define tac-subst-ruleres-branchlistlist ((x tac-ruleres-branchlistlist-p)
                                          (subst cmr::pseudo-term-subst-p))
  :returns (new-x tac-ruleres-branchlistlist-p)
  (if (atom x)
      nil
    (cons (tac-subst-ruleres-branchlist (car x) subst)
          (tac-subst-ruleres-branchlistlist (cdr x) subst)))
  ///
  (defthm tac-subst-ruleres-branchlistlist-of-append
    (equal (tac-subst-ruleres-branchlistlist (append x y) env)
           (append (tac-subst-ruleres-branchlistlist x env)
                   (tac-subst-ruleres-branchlistlist y env))))

  (defret eval-of-<fn>
    (equal (tac-eval-ruleres-branchlistlist new-x env)
           (tac-eval-ruleres-branchlistlist x (tac-ev-alist subst env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branchlistlist))))

  (defret tac-ruleres-branchlistlist-typed-of-<fn>
    (implies (tac-ruleres-branchlistlist-typed x types (tac-subst-ctx subst ctx))
             (tac-ruleres-branchlistlist-typed new-x types ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlistlist-typed))))

  (defret len-of-<fn>
    (equal (len new-x) (len x))))

(define tac-subst-ruleres-branch-args ((x tac-ruleres-branch-args-p)
                                       (subst cmr::pseudo-term-subst-p))
  :returns (new-x tac-ruleres-branch-args-p)
  (b* (((tac-ruleres-branch-args x)))
    (tac-ruleres-branch-args
     (cmr::termlist-subst-strict x.assums subst)
     (cmr::termlist-subst-strict x.ctx-result-args subst)))
  ///

  (defret eval-of-<fn>
    (Equal (tac-eval-ruleres-branch-args new-x env)
           (tac-eval-ruleres-branch-args x (tac-ev-alist subst env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch-args))))

  (defret tac-ruleres-branch-args-typed-of-<fn>
    (implies (tac-ruleres-branch-args-typed x types (tac-subst-ctx subst ctx))
             (tac-ruleres-branch-args-typed new-x types ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-args-typed)))))


(define tac-subst-ruleres-branch-argslist ((x tac-ruleres-branch-argslist-p)
                                          (subst cmr::pseudo-term-subst-p))
  :returns (new-x tac-ruleres-branch-argslist-p)
  (if (atom x)
      nil
    (cons (tac-subst-ruleres-branch-args (car x) subst)
          (tac-subst-ruleres-branch-argslist (cdr x) subst)))
  ///
  (defthm tac-subst-ruleres-branch-argslist-of-append
    (equal (tac-subst-ruleres-branch-argslist (append x y) env)
           (append (tac-subst-ruleres-branch-argslist x env)
                   (tac-subst-ruleres-branch-argslist y env))))

  (defret len-of-<fn>
    (equal (len new-x) (len x)))

  (defret eval-of-<fn>
    (equal (tac-eval-ruleres-branch-argslist new-x env)
           (tac-eval-ruleres-branch-argslist x (tac-ev-alist subst env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch-argslist)))))





;; ------------- Parsing of of tac-ruleres objects


(local (defthm assoc-is-hons-assoc
         (implies k
                  (equal (assoc-equal k x)
                         (hons-assoc-equal k x)))))

(define tac-parse-ruleres-base ((x pseudo-termp))
  :returns (mv ok (ctx-res pseudo-termp))
  (pseudo-term-case x
    :fncall (if (and (eq x.fn 'pred-in-set)
                     (eq (first x.args) 'w))
                (mv t (second x.args))
              (mv nil nil))
    :otherwise (mv nil nil))
  ///
  (defret <fn>-correct
    (implies ok
             (equal (in (cdr (hons-assoc-equal 'w env))
                        (tac-ev ctx-res env))
                    (tac-ev x env))))

  ;; (defret <fn>-typed
  ;;   (implies (and ok
  ;;                 (subsetp (tac-termlist-types (collect-if-branches x) ctx) '(:pred)))
  ;;            (equal (tac-term-type ctx-res ctx) :set))
  ;;   :hints(("Goal" :in-theory (enable collect-if-branches
  ;;                                     tac-termlist-types))))
  )

                
(local (in-theory (disable acl2::pseudo-termp-opener)))

(defthm tac-ev-cube-of-append
  (equal (tac-ev-cube (append x y) a)
         (and (tac-ev-cube x a)
              (tac-ev-cube y a)))
  :hints(("Goal" :in-theory (enable tac-ev-cube))))


(define tac-parse-ruleres-conj ((x pseudo-termp))
  :returns (mv (ok)
               (has-ctx)
               (assums pseudo-term-listp)
               (ctx-result pseudo-termp))
  :measure (pseudo-term-count x)
  :verify-guards nil
  (pseudo-term-case x
    :fncall (if (eq x.fn 'if)
                (b* (((list a b c) x.args))
                  (cond ((equal c ''nil)
                         (b* (((mv ok has-ctx1 assums1 ctx-result1) (tac-parse-ruleres-conj a))
                              ((unless ok) (mv nil nil nil nil))
                              ((mv ok has-ctx2 assums2 ctx-result2) (tac-parse-ruleres-conj b))
                              ((unless ok) (mv nil nil nil nil))
                              ((when (and has-ctx1 has-ctx2)) (mv nil nil nil nil)))
                           (mv t
                               (or has-ctx1 has-ctx2)
                               (append assums1 assums2)
                               (if has-ctx1 ctx-result1 ctx-result2))))
                        (t (mv nil nil nil nil))))
              (b* (((mv ok ctx-res) (tac-parse-ruleres-base x))
                   ((when ok) (mv t t nil ctx-res)))
                (mv t nil (list (pseudo-term-fix x)) nil)))
    :const (if x.val
               (mv t nil nil nil)
             (mv nil nil nil nil))
    :otherwise (mv nil nil nil nil))
  ///
  (verify-guards tac-parse-ruleres-conj)
  (local (in-theory (disable pred-in-set)))
  (defret <fn>-correct
    (implies ok
             (iff (tac-ev x env)
                  (and (tac-ev-cube assums env)
                       (or (not has-ctx)
                           (in (cdr (assoc 'w env))
                               (tac-ev ctx-result env))))))
    :hints(("Goal" :in-theory (enable tac-ev-cube)
            :induct <call>))
    :rule-classes nil)

  (defret <fn>-correct-rw
    (implies ok
             (and (implies has-ctx
                           (iff (in (cdr (hons-assoc-equal 'w env))
                                    (tac-eval-ruleres-branch
                                     (tac-ruleres-branch assums ctx-result)
                                     env))
                                (tac-ev x env)))
                  (implies (not has-ctx)
                           (iff (tac-ev-cube assums env)
                                (tac-ev x env)))))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch)
            :use <fn>-correct)))

  ;; (defret <fn>-typed
  ;;   (implies (subsetp (tac-termlist-types (collect-if-branches x) ctx) '(:pred))
  ;;            (and (subsetp (tac-termlist-types assums ctx) '(:pred))
  ;;                 (implies has-ctx
  ;;                          (equal (tac-term-type ctx-result ctx) :set))))
  ;;   :hints(("Goal" :in-theory (enable tac-termlist-types
  ;;                                     collect-if-branches))))
  )

;; (local (defcong set::sequiv equal (in a b) 2
;;          :hints(("Goal" :in-theory (enable in)))))

(define union-list (x)
  :verify-guards nil
  :returns (union setp)
  (if (atom x)
      nil
    (union (car x)
           (union-list (cdr x))))
  ///
  (defthm union-list-of-append
    (equal (union-list (append x y))
           (union (union-list x) (union-list y))))

  (defthm tac-typed-val-p-of-union-list
    (implies (and (tac-1typed-vallist-p x type)
                  (member-equal type '(:set :rel)))
             (tac-typed-val-p (union-list x) type))
    :hints(("Goal" :in-theory (enable tac-typed-val-p
                                      tac-1typed-vallist-p))))

  (fty::deffixcong acl2::list-equiv equal (union-list x) x))

(define tac-parse-ruleres ((x pseudo-termp))
  :returns (mv (ok)
               (results tac-ruleres-branchlist-p))
  :measure (pseudo-term-count x)
  :verify-guards nil
  (cond ((pseudo-term-case x
           :fncall (and (eq x.fn 'if)
                        (equal (first x.args) (second x.args)))
           :otherwise nil)
         (b* (((list a & c) (acl2::pseudo-term-fncall->args x))
              ((mv ok results1) (tac-parse-ruleres a))
              ((unless ok) (mv nil nil))
              ((mv ok results2) (tac-parse-ruleres c))
              ((unless ok) (mv nil nil)))
           (mv t (append results1 results2))))
        ((pseudo-term-case x
           :const (eq x.val nil)
           :otherwise nil)
         (mv t nil))
        (t (b* (((mv ok has-ctx assums ctx-result) (tac-parse-ruleres-conj x))
                ((unless (and ok has-ctx)) (mv nil nil)))
             (mv ok (list (tac-ruleres-branch assums ctx-result))))))
  ///
  (verify-guards tac-parse-ruleres)
  (defret <fn>-correct
    (implies ok
             (iff (in (cdr (hons-assoc-equal 'w env))
                      (union-list
                       (tac-eval-ruleres-branchlist results env)))
                  (tac-ev x env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branchlist
                                      union-list))))
)
 
