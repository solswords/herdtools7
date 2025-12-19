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
(include-book "pos-neg-rewrites")
(include-book "utils")
(include-book "terms")
(local (include-book "centaur/meta/subst-vars" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (std::add-default-post-define-hook :fix))

(encapsulate nil

  (acl2::defconsts *tac-negative-toplevel-normalize-rules*
    (b* (((mv err rewrites)
          (tac-collect-rewrites-aux
           (acl2::get-ruleset 'tac-negative-toplevel-normalize-rules (w state))
           (w state))))
      (if err
          (er hard? '*tac-negative-toplevel-normalize-rules* "~@0" err)
        rewrites)))

  (define tac-negative-toplevel-normalize-rules ()
    :returns (rewrites tac-rewritelist-p)
    *tac-negative-toplevel-normalize-rules*
    ///
    (in-theory (disable (tac-negative-toplevel-normalize-rules)))))

(define collect-conjunction ((x pseudo-termp))
  :measure (pseudo-term-count x)
  :returns (cube pseudo-term-listp)
  (pseudo-term-case x
    :fncall (if (and (eq x.fn 'if)
                     (equal (third x.args) ''nil))
                (append (collect-conjunction (first x.args))
                        (collect-conjunction (second x.args)))
              (list (pseudo-term-fix x)))
    :otherwise (list (pseudo-term-fix x)))
  ///
  (defret eval-of-<fn>
    (iff (tac-ev-cube cube env)
         (tac-ev x env))
    :hints(("Goal" :in-theory (enable tac-ev-cube))))

  (defret vars-of-<fn>
    (implies (not (member v (cmr::term-vars x)))
             (not (member v (cmr::termlist-vars cube))))
    :hints(("Goal" :in-theory (enable cmr::term-vars cmr::termlist-vars)))))
 

(defsection tac-toplevel-rewrite-type-preserved
  (defun-sk tac-toplevel-rewrite-type-preserved (rule)
    (forall (ctx)
            (b* (((cmr::rewrite rule)))
              (implies (equal (tac-term-type rule.lhs ctx) :pred)
                       (subsetp-equal (tac-termlist-types
                                       (collect-conjunction rule.rhs) ctx)
                                      '(:pred)))))
    :rewrite :direct)
  
  (in-theory (disable tac-toplevel-rewrite-type-preserved)))

(local (defthm prefixp-of-cons
         (equal (acl2::prefixp (cons a b) c)
                (And (consp c)
                     (equal (car c) a)
                     (acl2::prefixp b (cdr c))))
         :hints(("Goal" :in-theory (enable acl2::prefixp)))))

(local (defthm prefixp-of-nil
         (acl2::prefixp nil x)
         :hints(("Goal" :in-theory (enable acl2::prefixp)))))

(define tac-toplevel-rewrites-type-preserved (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-toplevel-rewrite-type-preserved (cdar rules)))
         (tac-toplevel-rewrites-type-preserved (cdr rules))))
  ///
  (local (defthm car-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (car x) a))))
  (local (defthm cdr-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (cdr x) b))))

  ;; (local (defthm tac-term-type-of-tac-subst-ctx
  ;;          (equal (Tac-term-type x (tac-subst-ctx subst ctx))
  ;;                 (tac-term-type (cmr::term-subst-strict x subst) ctx))))
  ;; (local (in-theory (disable tac-term-type-of-term-subst-strict)))
  
  (defthm tac-toplevel-rewrites-type-preserved-of-tac-negative-toplevel-normalize-rules
    (tac-toplevel-rewrites-type-preserved (tac-negative-toplevel-normalize-rules))
    :hints (("goal" :expand ((:free (x) (tac-toplevel-rewrite-type-preserved x))
                             (:free (a b) (tac-toplevel-rewrites-type-preserved (cons a b)))
                             (:free (a b ctx) (tac-termlist-types (cons a b) ctx)))
             :in-theory (e/d (;; cmr::term-subst-strict
                              ;; cmr::termlist-subst-strict
                              cmr::equal-of-pseudo-term-fncall
                              (tac-negative-toplevel-normalize-rules))
                             (tac-toplevel-rewrite-type-preserved-necc))))))



;; (defsection tac-toplevel-rewrite-hyps-ok
;;   (defun-sk tac-toplevel-rewrite-hyps-ok (rule)
;;     (forall (ctx env)
;;             (b* (((cmr::rewrite rule)))
;;               (implies (and (tac-typed-env-p env ctx)
;;                             (tac-term-type rule.lhs ctx))
;;                        (tac-ev-cube rule.hyps env))))
;;     :rewrite :direct)

;;   (in-theory (disable tac-toplevel-rewrite-hyps-ok)))

;; (define tac-toplevel-rewrites-hyps-ok (rules)
;;   :verify-guards nil
;;   (if (atom rules)
;;       t
;;     (and (or (not (mbt (consp (car rules))))
;;              (tac-toplevel-rewrite-hyps-ok (cdar rules)))
;;          (tac-toplevel-rewrites-hyps-ok (cdr rules))))
;;   ///
;;   (local (defthm car-when-equal-cons
;;            (implies (equal x (cons a b))
;;                     (equal (car x) a))))
;;   (local (defthm cdr-when-equal-cons
;;            (implies (equal x (cons a b))
;;                     (equal (cdr x) b))))
  
;;   (defthm tac-toplevel-rewrites-hyps-ok-of-tac-negative-toplevel-normalize-rules
;;     (tac-toplevel-rewrites-hyps-ok (tac-negative-toplevel-normalize-rules))
;;     :hints (("goal" :expand ((:free (x) (tac-toplevel-rewrite-hyps-ok x))
;;                              (:free (a b) (tac-toplevel-rewrites-hyps-ok (cons a b))))
;;              :in-theory (e/d (cmr::equal-of-pseudo-term-fncall
;;                               tac-ev-cube
;;                               (tac-negative-toplevel-normalize-rules))
;;                              (tac-toplevel-rewrite-hyps-ok-necc))))))

(defthm tac-ev-theoremlist-p-of-tac-negative-toplevel-normalize-rules
  (tac-ev-theoremlist-p (tac-rewritelist-terms (tac-negative-toplevel-normalize-rules)))
  :hints(("Goal" :in-theory (acl2::e/d* ((tac-negative-toplevel-normalize-rules)
                                         tac-rewritelist-terms
                                         tac-ev-theoremlist-p
                                         tac-ev-theoremp*-expand)
                                        ((:ruleset tac-functions)
                                         (tac-ev-theoremlist-p)
                                         (emptyset))))))


(define tac-toplevel-rewrite-hyps-ok ((hyps pseudo-term-listp)
                                      (subst cmr::pseudo-term-subst-p))
  (b* (((when (atom hyps)) t)
       (hyp (car hyps)))
    (and (pseudo-term-case hyp
           :fncall (if (eq hyp.fn 'not-singleton-set-p)
                       (b* ((arg (cmr::term-subst-strict (first hyp.args) subst)))
                         (not (pseudo-term-case arg
                                :fncall (eq arg.fn 'singleton)
                                :otherwise nil)))
                     nil)
           :otherwise nil)
         (tac-toplevel-rewrite-hyps-ok (cdr hyps) subst)))
  ///
  (defthmd tac-ev-of-hyps-when-tac-toplevel-rewrite-hyps-ok
    (implies (tac-toplevel-rewrite-hyps-ok hyps subst)
             (tac-ev-cube hyps (tac-ev-alist subst env)))
    :hints(("Goal" :in-theory (enable tac-ev-cube)))))
       
    

(define tac-toplevel-rewrite-apply-rule ((rule cmr::rewrite-p)
                                         (x pseudo-termp))
  :returns (mv ok (result pseudo-term-listp))
  (b* (((cmr::rewrite rule))
       ((unless (or (eq rule.equiv 'equal)
                    (eq rule.equiv 'iff)))
        (mv nil nil))
       ((mv ok subst) (cmr::term-unify-strict rule.lhs x nil))
       ((unless ok) (mv nil nil))
       ((unless (tac-toplevel-rewrite-hyps-ok rule.hyps subst))
        (mv nil nil)))
    (mv t (cmr::termlist-subst-strict (collect-conjunction rule.rhs) subst)))
  ///
  (local (defthm tac-ev-when-equal-term-subst-strict
           (implies (equal (cmr::term-subst-strict pat subst) (pseudo-term-fix x))
                    (equal (tac-ev x a)
                           (tac-ev pat (tac-ev-alist subst a))))
           :hints (("goal" :use ((:instance tac-ev-of-term-subst-strict (x pat) (a subst) (env a)))
                    :in-theory (disable tac-ev-of-term-subst-strict)))))
  (defret eval-of-<fn>
    (implies (and ok
                  (tac-ev-theoremp* (cmr::rewrite-term rule))
                  ;; (tac-typed-env-p env ctx)
                  ;; (tac-term-type (cmr::rewrite->lhs rule) ctx)
                  ;; (tac-toplevel-rewrite-hyps-ok rule)
                  )
             (iff (tac-ev-cube result env)
                  (tac-ev x env)))
    :hints (("goal" :use ((:instance tac-ev-theoremp*-implies
                           (x (cmr::rewrite-term rule))
                           (a (tac-ev-alist
                               (mv-nth 1 (cmr::term-unify-strict (cmr::rewrite->lhs rule) x nil))
                               env))))
             :in-theory (e/d (cmr::rewrite-term
                              tac-ev-of-hyps-when-tac-toplevel-rewrite-hyps-ok)
                             (tac-ev-theoremp*-implies)))))

  (defret vars-of-<fn>
    (implies (not (member v (cmr::term-vars x)))
             (not (member v (cmr::termlist-vars result)))))

  (local (defthm tac-term-type-when-equal-term-subst-strict
           (implies (equal (cmr::term-subst-strict pat subst) (pseudo-term-fix x))
                    (equal (tac-term-type x ctx)
                           (tac-term-type pat (tac-subst-ctx subst ctx))))
           :hints (("goal" :use ((:instance tac-term-type-of-term-subst-strict (x pat) (subst subst) (ctx ctx)))
                    :in-theory (disable tac-term-type-of-term-subst-strict)))))

  (defret type-of-<fn>
    (implies (and ok
                  (tac-toplevel-rewrite-type-preserved rule)
                  (equal (tac-term-type x ctx) :pred))
             (subsetp-equal (tac-termlist-types result ctx) '(:pred)))
    :hints(("Goal" :use ((:instance tac-toplevel-rewrite-type-preserved-necc
                          (ctx (tac-subst-ctx
                                (mv-nth 1 (cmr::term-unify-strict (cmr::rewrite->lhs rule) x nil))
                                ctx))))
            :in-theory (disable tac-toplevel-rewrite-type-preserved-necc)))))

(define tac-toplevel-rewrite-apply-rules ((rules tac-rewritelist-p)
                                          (x pseudo-termp))
  :returns (mv ok (result pseudo-term-listp))
  (b* (((when (atom rules)) (mv nil nil))
       ((unless (mbt (consp (car rules))))
        (tac-toplevel-rewrite-apply-rules (cdr rules) x))
       ((mv ok result) (tac-toplevel-rewrite-apply-rule (cdar rules) x))
       ((when ok) (mv ok result)))
    (tac-toplevel-rewrite-apply-rules (cdr rules) x))
  ///
  (defret eval-of-<fn>
    (implies (and ok
                  (tac-ev-theoremlist-p (tac-rewritelist-terms rules)))
             (iff (tac-ev-cube result env)
                  (tac-ev x env)))
    :hints (("goal" :in-theory (enable tac-ev-theoremlist-p tac-rewritelist-terms))))

  (defret vars-of-<fn>
    (implies (not (member v (cmr::term-vars x)))
             (not (member v (cmr::termlist-vars result)))))

  (defret type-of-<fn>
    (implies (and ok
                  (tac-toplevel-rewrites-type-preserved rules)
                  (equal (tac-term-type x ctx) :pred))
             (subsetp-equal (tac-termlist-types result ctx) '(:pred)))
    :hints(("Goal" :in-theory (enable tac-toplevel-rewrites-type-preserved))))

  (local (in-theory (enable tac-rewritelist-fix))))


    
       
       







