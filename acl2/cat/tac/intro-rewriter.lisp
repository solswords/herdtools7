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





