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

(include-book "basic-rewrites")
(include-book "utils")
(include-book "terms")


(acl2::defconsts *tac-rewrites*
  (b* (((mv err rewrites)
        (tac-collect-rewrites-aux
         (acl2::get-ruleset 'tac-rewrites (w state))
         (w state))))
    (if err
        (er hard? '*tac-rewrites* "~@0" err)
      rewrites)))

(define tac-rewrites ()
  :returns (rewrites tac-rewritelist-p)
  *tac-rewrites*
  ///
  (in-theory (disable (tac-rewrites))))

(local (defthm prefixp-of-cons
         (equal (acl2::prefixp (cons a b) c)
                (And (consp c)
                     (equal (car c) a)
                     (acl2::prefixp b (cdr c))))
         :hints(("Goal" :in-theory (enable acl2::prefixp)))))

(defsection tac-rewrite-rhs-preserved
  (defun-sk tac-rewrite-rhs-preserved (rule)
    (forall (ctx)
            (b* (((cmr::rewrite rule)))
              (implies (tac-term-type rule.lhs ctx)
                       (equal (tac-term-type rule.rhs ctx)
                              (tac-term-type rule.lhs ctx)))))
    :rewrite :direct)

  (in-theory (disable tac-rewrite-rhs-preserved)))

(define tac-rewrites-rhs-preserved (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-rewrite-rhs-preserved (cdar rules)))
         (tac-rewrites-rhs-preserved (cdr rules))))
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
  
  (defthm tac-rewrites-rhs-preserved-of-tac-rewrites
    (tac-rewrites-rhs-preserved (tac-rewrites))
    :hints (("goal" :expand ((:free (x) (tac-rewrite-rhs-preserved x))
                             (:free (a b) (tac-rewrites-rhs-preserved (cons a b))))
             :in-theory (e/d (;; cmr::term-subst-strict
                              ;; cmr::termlist-subst-strict
                              cmr::equal-of-pseudo-term-fncall
                              (tac-rewrites))
                             (tac-rewrite-rhs-preserved-necc))))))



(defsection tac-rewrite-hyps-ok
  (defun-sk tac-rewrite-hyps-ok (rule)
    (forall (ctx env)
            (b* (((cmr::rewrite rule)))
              (implies (and (tac-term-type rule.lhs ctx)
                            (tac-typed-env-p env ctx))
                       (tac-ev-cube rule.hyps env))))
    :rewrite :direct)

  (in-theory (disable tac-rewrite-hyps-ok)))

(define tac-rewrites-hyps-ok (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-rewrite-hyps-ok (cdar rules)))
         (tac-rewrites-hyps-ok (cdr rules))))
  ///
  (local (defthm car-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (car x) a))))
  (local (defthm cdr-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (cdr x) b))))
  
  (defthm tac-rewrites-hyps-ok-of-tac-rewrites
    (tac-rewrites-hyps-ok (tac-rewrites))
    :hints (("goal" :expand ((:free (x) (tac-rewrite-hyps-ok x))
                             (:free (a b) (tac-rewrites-hyps-ok (cons a b))))
             :in-theory (e/d (cmr::equal-of-pseudo-term-fncall
                              tac-ev-cube
                              (tac-rewrites))
                             (tac-rewrite-hyps-ok-necc))))))


(defthm tac-ev-theoremlist-p-of-tac-rewrites
  (tac-ev-theoremlist-p (tac-rewritelist-terms (tac-rewrites)))
  :hints(("Goal" :in-theory (acl2::e/d* ((tac-rewrites)
                                         tac-rewritelist-terms
                                         tac-ev-theoremlist-p
                                         tac-ev-theoremp*-expand)
                                        ((:ruleset tac-functions)
                                         (tac-ev-theoremlist-p)
                                         (emptyset))))))
