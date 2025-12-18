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
(include-book "ruleresults")
(local (std::add-default-post-define-hook :fix))

(encapsulate nil

  (acl2::defconsts *tac-positive-normalize-rules*
    (b* (((mv err rewrites)
          (tac-collect-rewrites-aux
           (acl2::get-ruleset 'tac-positive-normalize-rules (w state))
           (w state))))
      (if err
          (er hard? '*tac-positive-normalize-rules* "~@0" err)
        rewrites)))

  (define tac-positive-normalize-rules ()
    :returns (rewrites tac-rewritelist-p)
    *tac-positive-normalize-rules*
    ///
    (in-theory (disable (tac-positive-normalize-rules)))))



(encapsulate nil

  (acl2::defconsts *tac-negative-normalize-rules*
    (b* (((mv err rewrites)
          (tac-collect-rewrites-aux
           (acl2::get-ruleset 'tac-negative-normalize-rules (w state))
           (w state))))
      (if err
          (er hard? '*tac-negative-normalize-rules* "~@0" err)
        rewrites)))

  (define tac-negative-normalize-rules ()
    :returns (rewrites tac-rewritelist-p)
    *tac-negative-normalize-rules*
    ///
    (in-theory (disable (tac-negative-normalize-rules)))))


(define is-special-instantiation-rule ((x cmr::rewrite-p))
  (b* (((cmr::rewrite x)))
    (pseudo-term-case x.rhs
      :fncall (and (eq x.rhs.fn 'if)
                   (equal (first x.rhs.args) (second x.rhs.args)) ;; or
                   (equal (first x.rhs.args) x.lhs))
      :otherwise nil)))

(local
 (defthm symbol-listp-when-pseudo-var-list-p
   (implies (cmr::pseudo-var-list-p x)
            (symbol-listp x))))

(define special-instantiation-rule-free-vars ((x cmr::rewrite-p))
  :guard (is-special-instantiation-rule x)
  :guard-hints (("Goal" :in-theory (enable is-special-instantiation-rule)))
  :returns (vars cmr::pseudo-var-list-p)
  :prepwork ((local (defthm pseudo-var-list-p-of-set-diff
                      (implies (cmr::pseudo-var-list-p x)
                               (cmr::pseudo-var-list-p (set-difference-equal x y))))))
  (b* (((cmr::rewrite x))
       ((pseudo-term-fncall x.rhs)))
    (set-difference-eq (cmr::term-vars (third x.rhs.args)) (cmr::term-vars x.lhs))))

(define special-instantiation-rule-binding-hyp ((x cmr::rewrite-p))
  :guard (is-special-instantiation-rule x)
  :guard-hints (("Goal" :in-theory (enable is-special-instantiation-rule)))
  :returns (hyp pseudo-termp)
  :prepwork ((local (defthm pseudo-var-list-p-of-set-diff
                      (implies (cmr::pseudo-var-list-p x)
                               (cmr::pseudo-var-list-p (set-difference-equal x y))))))
  (b* (((cmr::rewrite x))
       (free-vars (special-instantiation-rule-free-vars x)))
    (and (consp x.hyps)
         (intersectp-eq (cmr::term-vars (car x.hyps)) free-vars)
         (car x.hyps))))

(local (defthm prefixp-of-cons
         (equal (acl2::prefixp (cons a b) c)
                (And (consp c)
                     (equal (car c) a)
                     (acl2::prefixp b (cdr c))))
         :hints(("Goal" :in-theory (enable acl2::prefixp)))))

(defsection tac-pred-rewrite-rhs-typed
  (defun-sk tac-pred-rewrite-rhs-typed (rule)
    (forall (ctx)
            (b* (((cmr::rewrite rule))
                 (lhs-type (tac-term-type rule.lhs ctx))
                 ((mv ok rhs-parsed) (tac-parse-ruleres rule.rhs)))
              (implies (and lhs-type
                            (let* ((binding-hyp (and (is-special-instantiation-rule rule)
                                                     (special-instantiation-rule-binding-hyp rule))))
                              (or (not binding-hyp)
                                  (tac-term-type binding-hyp ctx))))
                       (and ok
                            (tac-ruleres-branchlist-typed rhs-parsed :set ctx))
                       ;; (subsetp (tac-termlist-types (collect-if-branches rule.rhs) ctx)
                       ;;          '(:pred))
                       )))
    :rewrite :direct)

  (in-theory (disable tac-pred-rewrite-rhs-typed)))





(define tac-pred-rewrites-rhs-typed (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-pred-rewrite-rhs-typed (cdar rules)))
         (tac-pred-rewrites-rhs-typed (cdr rules))))
  ///
  (local (defthm car-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (car x) a))))
  (local (defthm cdr-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (cdr x) b))))
  
  (defthm tac-pred-rewrites-rhs-typed-of-tac-positive-normalize-rules
    (tac-pred-rewrites-rhs-typed (tac-positive-normalize-rules))
    :hints (("goal" :expand ((:free (a b) (tac-pred-rewrites-rhs-typed (cons a b)))
                             (:free (x) (tac-pred-rewrite-rhs-typed x))
                             (:free (a b) (tac-pred-rewrites-rhs-typed (cons a b)))
                             (:free (a b ctx) (tac-ruleres-branchlist-typed (cons a b) :set ctx))
                             (:free (a b ctx) (tac-ruleres-branchlist-typed nil :set ctx)))
             :in-theory (e/d (cmr::term-subst-strict
                              tac-ruleres-branch-typed
                              tac-termlist-types
                              cmr::termlist-subst-strict
                              cmr::equal-of-pseudo-term-fncall
                              (tac-positive-normalize-rules))
                             (tac-pred-rewrite-rhs-typed-necc)))))

  (defthm tac-pred-rewrites-rhs-typed-of-tac-negative-normalize-rules
    (tac-pred-rewrites-rhs-typed (tac-negative-normalize-rules))
    :hints (("goal" :expand ((:free (a b) (tac-pred-rewrites-rhs-typed (cons a b)))
                             (:free (x) (tac-pred-rewrite-rhs-typed x))
                             (:free (a b) (tac-pred-rewrites-rhs-typed (cons a b)))
                             (:free (a b ctx) (tac-ruleres-branchlist-typed (cons a b) :set ctx))
                             (:free (a b ctx) (tac-ruleres-branchlist-typed nil :set ctx)))
             :in-theory (e/d (cmr::term-subst-strict
                              tac-ruleres-branch-typed
                              tac-termlist-types
                              cmr::termlist-subst-strict
                              cmr::equal-of-pseudo-term-fncall
                              (tac-negative-normalize-rules))
                             (tac-pred-rewrite-rhs-typed-necc)))))
  )

(defsection tac-pred-rewrite-hyps-ok
  (defun-sk tac-pred-rewrite-hyps-ok (rule)
    (forall (ctx env)
            (b* (((cmr::rewrite rule)))
              (implies (and (tac-typed-env-p env ctx)
                            (tac-term-type rule.lhs ctx))
                       (and (implies (and (is-special-instantiation-rule rule)
                                          (tac-term-type (special-instantiation-rule-binding-hyp rule) ctx)
                                          (tac-ev (special-instantiation-rule-binding-hyp rule) env))
                                     (tac-ev-cube rule.hyps env))
                            (implies (not (is-special-instantiation-rule rule))
                                     (tac-ev-cube rule.hyps env))))))
    :rewrite :direct)

  (in-theory (disable tac-pred-rewrite-hyps-ok)))



(define tac-pred-rewrites-hyps-ok (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-pred-rewrite-hyps-ok (cdar rules)))
         (tac-pred-rewrites-hyps-ok (cdr rules))))
  ///
  (local (defthm car-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (car x) a))))
  (local (defthm cdr-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (cdr x) b))))
  
  (defthm tac-pred-rewrites-hyps-ok-of-tac-positive-normalize-rules
    (tac-pred-rewrites-hyps-ok (tac-positive-normalize-rules))
    :hints (("goal" :expand ((:free (x) (tac-pred-rewrite-hyps-ok x))
                             (:free (a b) (tac-pred-rewrites-hyps-ok (cons a b))))
             :in-theory (e/d (cmr::term-subst-strict
                              cmr::termlist-subst-strict
                              cmr::equal-of-pseudo-term-fncall
                              tac-ev-cube
                              (tac-positive-normalize-rules))
                             (tac-pred-rewrite-hyps-ok-necc)))))

  (defthm tac-pred-rewrites-hyps-ok-of-tac-negative-normalize-rules
    (tac-pred-rewrites-hyps-ok (tac-negative-normalize-rules))
    :hints (("goal" :expand ((:free (x) (tac-pred-rewrite-hyps-ok x))
                             (:free (a b) (tac-pred-rewrites-hyps-ok (cons a b))))
             :in-theory (e/d (cmr::term-subst-strict
                              cmr::termlist-subst-strict
                              cmr::equal-of-pseudo-term-fncall
                              tac-ev-cube
                              (tac-negative-normalize-rules))
                             (tac-pred-rewrite-hyps-ok-necc))))))



(define is-pred-in-set-w ((x pseudo-termp))
  (pseudo-term-case x
    :fncall (and (eq x.fn 'pred-in-set)
                 (consp x.args)
                 (eq (first x.args) 'w))
    :otherwise nil))

(define tac-pred-rewrite-parse-ok ((rule cmr::rewrite-p))
  :guard-hints (("goal" :in-theory (enable is-pred-in-set-w)))
  (b* (((cmr::rewrite rule))
       ((mv ok results) (tac-parse-ruleres rule.rhs)))
    (and (is-pred-in-set-w rule.lhs)
         (not (member-equal 'w (cmr::term-vars (cadr (pseudo-term-call->args rule.lhs)))))
         (or (not (is-special-instantiation-rule rule))
             (not (member-equal 'w (cmr::term-vars
                                    (special-instantiation-rule-binding-hyp rule)))))
         ok
         (not (member-equal 'w (tac-ruleres-branchlist-vars results)))))
  ///
  (defthmd tac-pred-rewrite-parse-ok-implies
    (b* (((cmr::rewrite rule))
         ((mv ok results) (tac-parse-ruleres rule.rhs)))
      (implies (tac-pred-rewrite-parse-ok rule)
               (and (equal (pseudo-term-kind rule.lhs) :fncall)
                    (equal (pseudo-term-fncall->fn rule.lhs) 'pred-in-set)
                    (equal (first (pseudo-term-call->args rule.lhs)) 'w)
                    (is-pred-in-set-w rule.lhs)
                    (not (member-equal 'w (cmr::term-vars (cadr (pseudo-term-call->args rule.lhs)))))
                    ok
                    (not (member-equal 'w (tac-ruleres-branchlist-vars results)))
                    (implies (is-special-instantiation-rule rule)
                             (not (member-equal 'w (cmr::term-vars
                                                    (special-instantiation-rule-binding-hyp rule))))))))
    :hints(("Goal" :in-theory (enable is-pred-in-set-w)))))
                    

(define tac-pred-rewrites-parse-ok ((rules tac-rewritelist-p))
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-pred-rewrite-parse-ok (cdar rules)))
         (tac-pred-rewrites-parse-ok (cdr rules))))
  ///
  (defthm tac-pred-rewriteso-parse-ok-of-positive-normalize
    (tac-pred-rewrites-parse-ok (tac-positive-normalize-rules))
    :hints(("Goal" :in-theory (enable (tac-positive-normalize-rules)))))

  (defthm tac-pred-rewrites-parse-ok-of-negative-normalize
    (tac-pred-rewrites-parse-ok (tac-negative-normalize-rules))
    :hints(("Goal" :in-theory (enable (tac-negative-normalize-rules)))))

  (local (in-theory (enable tac-rewritelist-fix))))




(defthm tac-ev-theorem-rewritesp-of-tac-positive-normalize-rules
  (tac-ev-theoremlist-p (tac-rewritelist-terms (tac-positive-normalize-rules)))
  :hints(("Goal" :in-theory (acl2::e/d* ((tac-positive-normalize-rules)
                                         tac-ev-theoremp*-expand
                                         tac-ev-theoremlist-p)
                                        ((:ruleset tac-negative-normalize-rules)
                                         (tac-ev-theoremlist-p)
                                         tac-functions
                                         (emptyset)
                                         (pred-false))
                                        ((:ruleset tac-positive-normalize-rules)))
          :expand ((:Free (a b) (tac-rewritelist-terms (cons a b)))))))

(defsection tac-ev-theorem-rewritesp-of-tac-negative-normalize-rules
  (local (define tac-ev-theorem-rewrite-p ((name symbolp)
                                           (rule cmr::rewrite-p))
           :verify-guards nil
           (declare (ignore name))
           (tac-ev-theoremp* (cmr::rewrite-term rule))))

  (local (in-theory (disable (tac-ev-theorem-rewrite-p))))
  (local (defthm tac-ev-theoremlist-of-tac-rewritelist-terms-in-terms-of-rewrite-p
           (equal (tac-ev-theoremlist-p (tac-rewritelist-terms (cons a b)))
                  (and (or (not (consp a))
                           (tac-ev-theorem-rewrite-p (car a) (cdr a)))
                       (tac-ev-theoremlist-p (tac-rewritelist-terms b))))
           :hints (("goal" :in-theory (enable tac-rewritelist-terms
                                              tac-ev-theorem-rewrite-p
                                              tac-ev-theoremlist-p)))))

  (local (defun instance-subst (vars term)
           (if (atom vars)
               nil
             (cons (list (car vars)
                         `(cdr (assoc-equal ',(car vars)
                                            (tac-ev-falsify ',term))))
                   (instance-subst (cdr vars) term)))))

  (defthm tac-ev-theorem-rewritesp-of-tac-negative-normalize-rules
    (tac-ev-theoremlist-p (tac-rewritelist-terms (tac-negative-normalize-rules)))
    :hints(("Goal" :in-theory (acl2::e/d* ((tac-negative-normalize-rules)
                                           tac-ev-theoremp*-expand)
                                          ((:ruleset tac-negative-normalize-rules)
                                           (:ruleset tac-positive-normalize-rules)
                                           tac-functions
                                           (tac-rewritelist-terms)
                                           (emptyset)
                                           (pred-false)))
            :expand ((tac-rewritelist-terms nil)))
           (and stable-under-simplificationp
                (let ((lit (car (last clause))))
                  (case-match lit
                    (('tac-ev-theorem-rewrite-p ('quote name) ('quote rule))
                     (let ((rule-term (cmr::rewrite-term rule)))
                       `(:use ((:instance ,name
                                . ,(instance-subst (cmr::term-vars rule-term) rule-term)))
                         :expand (,lit))))))))))
