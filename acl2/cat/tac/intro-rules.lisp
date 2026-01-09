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

(include-book "intro-rewrites")
(include-book "utils")
(include-book "terms")
(include-book "centaur/meta/pseudo-term-var-list" :dir :system)
(include-book "std/lists/index-of" :dir :system)
(local (include-book "std/lists/sets" :dir :system))
(local (std::add-default-post-define-hook :fix))
(encapsulate nil
  (acl2::defconsts *tac-intersect-propagate-rules*
    (b* (((mv err rewrites)
          (tac-collect-rewrites-aux
           (cdr (assoc 'intersect-propagate-rules (table-alist 'tac-rules (w state))))
           (w state))))
      (if err
          (er hard? '*tac-intersect-propagate-rules* "~@0" err)
        rewrites)))

  (define tac-intersect-propagate-rules ()
    :returns (rewrites tac-rewritelist-p)
    *tac-intersect-propagate-rules*
    ///
    (in-theory (disable (tac-intersect-propagate-rules)))))


(define pred-intersects-p ((fn pseudo-fnsym-p))
  (member-eq (pseudo-fnsym-fix fn) '(pred-set-intersects
                                     pred-rel-intersects)))



;; duplicated in ruleresults.lisp
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

(cmr::defthm-term-vars-flag
  (defthm tac-ev-of-second-cons-non-var
    (implies (not (member-equal v (cmr::term-vars x)))
             (equal (tac-ev x (list* pair (cons v val) env))
                    (tac-ev x (cons pair env))))
    :hints ('(:expand ((cmr::term-vars x))
              :in-theory (enable tac-ev-when-pseudo-term-call)))
    :flag cmr::term-vars)
  (defthm tac-ev-lst-of-second-cons-non-var
    (implies (not (member-equal v (cmr::termlist-vars x)))
             (equal (tac-ev-lst x (list* pair (cons v val) env))
                    (tac-ev-lst x (cons pair env))))
    :hints ('(:expand ((cmr::termlist-vars x))))
    :flag cmr::termlist-vars))



;; (cmr::defthm-term-vars-flag
;;   (defthm tac-term-type-of-cons-non-var
;;     (implies (not (member-equal v (cmr::term-vars x)))
;;              (equal (tac-term-type x (cons (cons v typ) ctx))
;;                     (tac-term-type x ctx)))
;;     :hints ('(:expand ((cmr::term-vars x))))
;;     :flag cmr::term-vars)
;;   (defthm tac-termlist-types-of-cons-non-var
;;     (implies (not (member-equal v (cmr::termlist-vars x)))
;;              (equal (tac-termlist-types x (cons (cons v typ) ctx))
;;                     (tac-termlist-types x ctx)))
;;     :hints ('(:expand ((cmr::termlist-vars x))))
;;     :flag cmr::termlist-vars))

;; (cmr::defthm-term-vars-flag
;;   (defthm tac-term-type-of-second-cons-non-var
;;     (implies (not (member-equal v (cmr::term-vars x)))
;;              (equal (tac-term-type x (list* pair (cons v typ) ctx))
;;                     (tac-term-type x (cons pair ctx))))
;;     :hints ('(:expand ((cmr::term-vars x))))
;;     :flag cmr::term-vars)
;;   (defthm tac-termlist-types-of-second-cons-non-var
;;     (implies (not (member-equal v (cmr::termlist-vars x)))
;;              (equal (tac-termlist-types x (list* pair (cons v typ) ctx))
;;                     (tac-termlist-types x (cons pair ctx))))
;;     :hints ('(:expand ((cmr::termlist-vars x))))
;;     :flag cmr::termlist-vars))


(local
 (defthm assoc-equal-is-hons-assoc-equal
   (implies k
            (equal (assoc-equal k x)
                   (hons-assoc-equal k x)))))


(local (defthm termlist-vars-when-pseudo-term-var-listp
         (implies (cmr::pseudo-term-var-listp x)
                  (acl2::set-equiv (cmr::termlist-vars x)
                                   (cmr::pseudo-term-var-list->names x)))
         :hints(("Goal" :in-theory (enable cmr::termlist-vars
                                           cmr::pseudo-term-var-list->names
                                           cmr::pseudo-term-var-listp
                                           cmr::term-vars)))))


(define tac-intersect-propagate-rule-wellformed ((rule cmr::rewrite-p))
  (b* (((cmr::rewrite rule)))
    (and (eq rule.equiv 'iff)
         (not rule.hyps)
         (pseudo-term-case rule.lhs :fncall)
         (pseudo-term-case rule.rhs :fncall)
         (b* (((pseudo-term-fncall rule.lhs))
              ((pseudo-term-fncall rule.rhs)))
           (and ;; (pred-intersects-p rule.lhs.fn)
                ;; (pred-intersects-p rule.rhs.fn)
                (pseudo-term-case (first rule.lhs.args) :var)
                (pseudo-term-case (second rule.rhs.args) :var)
                (pseudo-term-case (second rule.lhs.args) :fncall)
                (b* ((desc-var (pseudo-term-var->name (second rule.rhs.args)))
                     (int-var (pseudo-term-var->name (first rule.lhs.args)))
                     ((pseudo-term-fncall target) (second rule.lhs.args))
                     (target-type (tac-function-return-type target.fn))
                     (target-argtypes (tac-function-argument-types target.fn))
                     ((unless (cmr::pseudo-term-var-listp target.args)) nil)
                     (arg-vars (cmr::pseudo-term-var-list->names target.args))
                     ((unless (no-duplicatesp-equal arg-vars))
                      nil)
                     (desc-pos (acl2::index-of desc-var arg-vars))
                     ((unless desc-pos) nil)
                     (desc-type (nth desc-pos target-argtypes)))
                  (and (not (member-equal int-var arg-vars))
                       (not (member-equal desc-var (cmr::term-vars (first rule.rhs.args))))
                       (or (and (eq target-type :set) (eq rule.lhs.fn 'pred-set-intersects))
                           (and (eq target-type :rel) (eq rule.lhs.fn 'pred-rel-intersects)))
                       (or (and (eq desc-type :set) (eq rule.rhs.fn 'pred-set-intersects))
                           (and (eq desc-type :rel) (eq rule.rhs.fn 'pred-rel-intersects))))))))))

(define tac-intersect-propagate-rule->intersect-var ((rule cmr::rewrite-p))
  :guard (tac-intersect-propagate-rule-wellformed rule)
  :guard-hints (("goal" :in-theory (enable tac-intersect-propagate-rule-wellformed)))
  :returns (var pseudo-var-p)
  (b* (((cmr::rewrite rule))
       ((pseudo-term-fncall rule.lhs)))
    (pseudo-term-var->name (first rule.lhs.args))))

(define tac-intersect-propagate-rule->target-fn ((rule cmr::rewrite-p))
  :guard (tac-intersect-propagate-rule-wellformed rule)
  :guard-hints (("goal" :in-theory (enable tac-intersect-propagate-rule-wellformed)))
  :returns (var pseudo-fnsym-p)
  (b* (((cmr::rewrite rule))
       ((pseudo-term-fncall rule.lhs)))
    (pseudo-term-fncall->fn (second rule.lhs.args))))

(define tac-intersect-propagate-rule->target-pattern ((rule cmr::rewrite-p))
  :guard (tac-intersect-propagate-rule-wellformed rule)
  :guard-hints (("goal" :in-theory (enable tac-intersect-propagate-rule-wellformed)))
  :returns (pat pseudo-termp)
  (b* (((cmr::rewrite rule))
       ((pseudo-term-fncall rule.lhs)))
    (second rule.lhs.args))
  ///
  (defret <fn>-when-wellformed
    (implies (tac-intersect-propagate-rule-wellformed rule)
             (and (equal (pseudo-term-kind pat) :fncall)
                  (equal (pseudo-term-fncall->fn pat)
                         (tac-intersect-propagate-rule->target-fn rule))
                  (cmr::pseudo-term-var-listp (pseudo-term-call->args pat))
                  (no-duplicatesp-equal (cmr::pseudo-term-var-list->names (pseudo-term-call->args pat)))))
    :hints(("Goal" :in-theory (enable tac-intersect-propagate-rule->target-fn
                                      tac-intersect-propagate-rule-wellformed))))

  (defret term-vars-of-<fn>
    (implies (tac-intersect-propagate-rule-wellformed rule)
             (acl2::set-equiv (cmr::term-vars pat)
                              (cmr::pseudo-term-var-list->names
                               (pseudo-term-call->args pat))))
    :hints(("Goal" :in-theory (enable tac-intersect-propagate-rule-wellformed
                                      cmr::term-vars
                                      termlist-vars-when-pseudo-term-var-listp))))

  

  (defret <fn>-intersect-var
    (implies (tac-intersect-propagate-rule-wellformed rule)
             (not (member-equal (tac-intersect-propagate-rule->intersect-var rule)
                                (cmr::pseudo-term-var-list->names
                                 (pseudo-term-call->args pat)))))
    :hints(("Goal" :in-theory (e/d (tac-intersect-propagate-rule->intersect-var
                                    tac-intersect-propagate-rule-wellformed
                                    cmr::term-vars)
                                   (cmr::pseudo-term-var-list->names-when-pseudo-term-listp))))))

(local (defthm nth-name-in-args
         (implies (and (pseudo-term-case x :var)
                       (cmr::pseudo-term-var-listp args)
                       (pseudo-term-listp args)
                       (member-equal (pseudo-term-var->name x) (cmr::pseudo-term-var-list->names args)))
                  (equal
                   (nth (acl2::index-of (pseudo-term-var->name x) (cmr::pseudo-term-var-list->names args)) args)
                   (pseudo-term-fix x)))
         :hints(("Goal" :in-theory (e/d (acl2::index-of cmr::pseudo-term-var-list->names
                                                        cmr::pseudo-term-var-listp)
                                        (CMR::PSEUDO-TERM-VAR-LIST->NAMES-WHEN-PSEUDO-TERM-LISTP))
                 :induct t)
                (and stable-under-simplificationp
                     '(:use ((:instance acl2::pseudo-term-var-of-accessors (x x))
                             (:instance acl2::pseudo-term-var-of-accessors (x (car args))))
                       :in-theory (disable acl2::pseudo-term-var-of-accessors
                                           CMR::PSEUDO-TERM-VAR-LIST->NAMES-WHEN-PSEUDO-TERM-LISTP))))))

(define tac-intersect-propagate-rule->descent-pos ((rule cmr::rewrite-p))
  :guard (tac-intersect-propagate-rule-wellformed rule)
  :guard-hints (("goal" :in-theory (enable tac-intersect-propagate-rule-wellformed)))
  :returns (pos natp :rule-classes :type-prescription)
  (b* (((cmr::rewrite rule))
       ((pseudo-term-fncall rule.lhs))
       ((pseudo-term-fncall rule.rhs))
       (desc-var (pseudo-term-var->name (second rule.rhs.args)))
       (arg-vars (cmr::pseudo-term-var-list->names
                  (pseudo-term-call->args (second rule.lhs.args)))))
    (lnfix (acl2::index-of desc-var arg-vars)))
  ///
  (defret <fn>-var-not-equal-intersect-var
    (implies (tac-intersect-propagate-rule-wellformed rule)
             (not (equal (pseudo-term-var->name
                          (nth pos (pseudo-term-call->args
                                    (tac-intersect-propagate-rule->target-pattern rule))))
                         (tac-intersect-propagate-rule->intersect-var rule))))
    :hints(("Goal" :in-theory (e/d (tac-intersect-propagate-rule->intersect-var
                                      tac-intersect-propagate-rule->target-pattern
                                      tac-intersect-propagate-rule-wellformed)
                                   (cmr::pseudo-term-var-list->names-when-pseudo-term-listp)))))

  (defret <fn>-element-is-var
    (implies (tac-intersect-propagate-rule-wellformed rule)
             (equal (pseudo-term-kind
                     (nth pos (pseudo-term-call->args
                               (tac-intersect-propagate-rule->target-pattern rule))))
                    :var))
    :hints(("Goal" :in-theory (e/d (tac-intersect-propagate-rule->intersect-var
                                      tac-intersect-propagate-rule->target-pattern
                                      tac-intersect-propagate-rule-wellformed)
                                   (cmr::pseudo-term-var-list->names-when-pseudo-term-listp)))))

  (defret <fn>-bound
    (implies (tac-intersect-propagate-rule-wellformed rule)
             (< pos (len (pseudo-term-call->args
                          (tac-intersect-propagate-rule->target-pattern rule)))))
    :hints(("Goal" :in-theory (enable tac-intersect-propagate-rule->target-pattern
                                      tac-intersect-propagate-rule-wellformed)))))


(local (defthm nth-of-tac-termlist-types
         (equal (nth n (tac-termlist-types x ctx))
                (tac-term-type (nth n x) ctx))
         :hints(("Goal" :in-theory (enable tac-termlist-types)
                 :induct (nth n x)))))

(local (defthmd nth-when-prefix
         (implies (and (acl2::prefixp x y)
                       (nth n x))
                  (equal (nth n y) (nth n x)))
         :hints(("Goal" :in-theory (enable acl2::prefixp)))))

(local (defthm nth-of-termlist-subst-strict
         (equal (nth pos (cmr::termlist-subst-strict pat subst))
                (cmr::term-subst-strict (nth pos pat) subst))
         :hints(("Goal" :induct (nth pos pat)
                 :in-theory (e/d (nth cmr::termlist-subst-strict))
                 :expand ((cmr::term-subst-strict nil subst))))))

(local (defthmd nth-of-equal-to-termlist-subst-strict
         (implies (equal lst (cmr::termlist-subst-strict pat subst))
                  (equal (nth pos lst)
                         (cmr::term-subst-strict (nth pos pat) subst)))))
                         

(defthmd lookup-of-nth-var-in-pattern-in-subst
  (b* (((mv ok subst) (cmr::term-unify-strict target-pattern arg nil)))
    (implies (and ok
                  (pseudo-term-case target-pattern :fncall)
                  (pseudo-term-case (nth pos (pseudo-term-call->args target-pattern)) :var))
             (equal (cdr (hons-assoc-equal (pseudo-term-var->name (nth pos (pseudo-term-call->args target-pattern)))
                                           subst))
                    (nth pos (pseudo-term-call->args arg)))))
  :hints (("goal" :expand ((:free (subst) (cmr::term-subst-strict target-pattern subst)))
           :in-theory (enable cmr::equal-of-pseudo-term-fncall
                              nth-of-equal-to-termlist-subst-strict
                              cmr::term-subst-strict))))


(local (defthm lookup-of-tac-subst-ctx
         (equal (hons-assoc-equal v (tac-subst-ctx subst ctx))
                (let ((look (hons-assoc-equal v (cmr::pseudo-term-subst-fix subst))))
                  (and look
                       (cons v (tac-term-type (cdr look) ctx)))))
         :hints(("Goal" :in-theory (enable tac-subst-ctx)))))

(local (defthm tac-term-type-of-tac-subst-ctx-unify
         (b* (((mv ok subst) (cmr::term-unify-strict pat target nil)))
           (implies ok
                    (equal (tac-term-type pat (tac-subst-ctx subst ctx))
                           (tac-term-type target ctx))))
         :hints (("goal" :use ((:instance tac-term-type-of-term-subst-strict
                                (x pat)
                                (subst (mv-nth 1 (cmr::term-unify-strict pat target nil)))))
                  :in-theory (disable tac-term-type-of-term-subst-strict)))))


(define tac-intersect-propagate-rule->result-type ((rule cmr::rewrite-p))
  :guard (tac-intersect-propagate-rule-wellformed rule)
  :guard-hints (("goal" :in-theory (enable tac-intersect-propagate-rule-wellformed
                                           tac-intersect-propagate-rule->target-fn
                                           tac-intersect-propagate-rule->descent-pos)))
  :returns (type tac-type-p)
  (tac-type-fix
   (nth (tac-intersect-propagate-rule->descent-pos rule)
        (tac-function-argument-types (tac-intersect-propagate-rule->target-fn rule))))
  ///
  (defret <fn>-when-wellformed
    (implies (tac-intersect-propagate-rule-wellformed rule)
             (or (equal type :set)
                 (equal type :rel)))
    :hints(("Goal" :in-theory (enable tac-intersect-propagate-rule-wellformed
                                      tac-intersect-propagate-rule->descent-pos
                                      tac-intersect-propagate-rule->target-fn)))
    :rule-classes :forward-chaining)

  (defret <fn>-is-desc-var-type
    (implies (and (tac-intersect-propagate-rule-wellformed rule)
                  (tac-term-type (tac-intersect-propagate-rule->target-pattern rule) ctx))
             (tac-type-equiv
              (cdr (hons-assoc-equal
                    (pseudo-term-var->name
                     (nth (tac-intersect-propagate-rule->descent-pos rule)
                          (pseudo-term-call->args
                           (tac-intersect-propagate-rule->target-pattern rule))))
                    ctx))
              type))
    :hints(("Goal" :in-theory (e/d (tac-intersect-propagate-rule->target-pattern
                                      tac-intersect-propagate-rule->target-fn
                                      tac-intersect-propagate-rule->descent-pos
                                      tac-intersect-propagate-rule-wellformed
                                      nth-when-prefix)
                                   (nth-of-tac-termlist-types
                                    CMR::PSEUDO-TERM-VAR-LIST->NAMES-WHEN-PSEUDO-TERM-LISTP))
            :use ((:instance nth-of-tac-termlist-types
                   (n (tac-intersect-propagate-rule->descent-pos rule))
                   (x (pseudo-term-call->args
                       (tac-intersect-propagate-rule->target-pattern rule))))))))

  (defret <fn>-is-desc-var-type-unify
    (b* (((mv ok ?subst)
          (cmr::term-unify-strict (tac-intersect-propagate-rule->target-pattern rule) target nil)))
      (implies (and (tac-intersect-propagate-rule-wellformed rule)
                    (tac-term-type target ctx)
                    ok)
               (equal
                (tac-term-type
                 (nth (tac-intersect-propagate-rule->descent-pos rule)
                      (pseudo-term-call->args target))
                 ctx)
                type)))
    :hints(("Goal" :use ((:instance <fn>-is-desc-var-type
                          (ctx (tac-subst-ctx (mv-nth 1 (cmr::term-unify-strict (tac-intersect-propagate-rule->target-pattern rule) target nil)) ctx))))
            :in-theory (e/d (lookup-of-nth-var-in-pattern-in-subst)
                            (<fn> <fn>-is-desc-var-type))))))

(define tac-intersect-propagate-rule->intersect-term ((rule cmr::rewrite-p))
  :guard (tac-intersect-propagate-rule-wellformed rule)
  :guard-hints (("goal" :in-theory (enable tac-intersect-propagate-rule-wellformed
                                           tac-intersect-propagate-rule->target-fn
                                           tac-intersect-propagate-rule->descent-pos)))
  :returns (intterm pseudo-termp)
  (b* (((cmr::rewrite rule))
       ((pseudo-term-fncall rule.rhs)))
    (first rule.rhs.args))
  ///
  (defret vars-of-<fn>-when-wellformed
    (implies (tac-intersect-propagate-rule-wellformed rule)
             (not (member-equal (pseudo-term-var->name
                                 (nth (tac-intersect-propagate-rule->descent-pos rule)
                                      (pseudo-term-call->args
                                       (tac-intersect-propagate-rule->target-pattern rule))))
                                (cmr::term-vars intterm))))
    :hints(("Goal" :in-theory (e/d (tac-intersect-propagate-rule->target-pattern
                                      tac-intersect-propagate-rule->descent-pos
                                      tac-intersect-propagate-rule-wellformed)
                                   (cmr::pseudo-term-var-list->names-when-pseudo-term-listp))))))




(defthm tac-intersect-propagate-rule-wellformed-implies
  (b* ((target-pattern (tac-intersect-propagate-rule->target-pattern rule))
       (target-fn (tac-intersect-propagate-rule->target-fn rule))
       (target-type (tac-function-return-type target-fn))
       (desc-type (tac-intersect-propagate-rule->result-type rule))
       (desc-pos (tac-intersect-propagate-rule->descent-pos rule))
       (desc-var (pseudo-term-var->name (nth desc-pos (pseudo-term-call->args target-pattern))))
       (old-int-var (tac-intersect-propagate-rule->intersect-var rule))
       (new-int-term (tac-intersect-propagate-rule->intersect-term rule))
       (old-int-val (cdr (hons-assoc-equal old-int-var env)))
       (target-val (tac-ev target-pattern env))
       (new-int-val (tac-ev new-int-term env))
       (desc-val (cdr (hons-assoc-equal desc-var env)))
       (lhs (if (eq target-type :set)
                (pred-set-intersects old-int-val target-val)
              (pred-rel-intersects old-int-val target-val)))
       (rhs (if (eq desc-type :set)
                (pred-set-intersects new-int-val desc-val)
              (pred-rel-intersects new-int-val desc-val))))
    (implies (and (tac-intersect-propagate-rule-wellformed rule)
                  (tac-ev-theoremp* (cmr::rewrite-term rule)))
             (iff lhs rhs)))
  :hints (("goal" :use ((:instance tac-ev-theoremp*-implies
                         (x (cmr::rewrite-term rule)) (a env)))
           :in-theory (e/d (tac-intersect-propagate-rule-wellformed
                            tac-intersect-propagate-rule->intersect-term
                            tac-intersect-propagate-rule->intersect-var
                            tac-intersect-propagate-rule->target-pattern
                            tac-intersect-propagate-rule->result-type
                            tac-intersect-propagate-rule->descent-pos
                            tac-intersect-propagate-rule->target-pattern
                            tac-intersect-propagate-rule->target-fn
                            cmr::rewrite-term
                            tac-ev-cube)
                           (tac-ev-theoremp*-implies
                            cmr::pseudo-term-var-list->names-when-pseudo-term-listp))))
  :rule-classes nil)

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


(defthm tac-intersect-propagate-rule-wellformed-implies-can-rewrite-inner
  (b* ((target-fn (tac-intersect-propagate-rule->target-fn rule))
       (target-pattern (tac-intersect-propagate-rule->target-pattern rule))
       (target-type (tac-function-return-type target-fn))
       (desc-type (tac-intersect-propagate-rule->result-type rule))
       (desc-pos (tac-intersect-propagate-rule->descent-pos rule))
       (desc-var (pseudo-term-var->name (nth desc-pos (pseudo-term-call->args target-pattern))))
       (int-var (tac-intersect-propagate-rule->intersect-var rule))
       (int-term (tac-intersect-propagate-rule->intersect-term rule))
       ((mv ok subst) (cmr::term-unify-strict target-pattern arg nil))
       (new-int-val (tac-ev int-term
                            (cons (cons int-var w)
                                  (tac-ev-alist subst env))))
       (desc-val (tac-ev (cdr (hons-assoc-equal desc-var subst)) env))
       (target-val (tac-ev arg env))
       (target-new-val (tac-ev target-pattern (cons (cons desc-var desc-new-val)
                                                    (tac-ev-alist subst env)))))
    (implies (and (tac-ev-theoremp* (cmr::rewrite-term rule))
                  (tac-intersect-propagate-rule-wellformed rule)
                  ok
                  ;; (eq rule.rhs.fn 'pred-set-intersects)
                    
                  (if (eq desc-type :set)
                      (iff (pred-set-intersects new-int-val desc-val)
                           (and new-assum
                                (pred-set-intersects new-int-val desc-new-val)))
                    (iff (pred-rel-intersects new-int-val desc-val)
                         (and new-assum
                              (pred-rel-intersects new-int-val desc-new-val)))))
             (and (implies (eq target-type :set)
                           (iff (pred-set-intersects w target-val)
                                (and new-assum
                                     (pred-set-intersects w target-new-val))))
                  (implies (not (eq target-type :set))
                           (iff (pred-rel-intersects w target-val)
                                (and new-assum
                                     (pred-rel-intersects w target-new-val)))))))
  :hints (("goal" :in-theory (e/d (tac-ev-of-pattern-by-alist)
                                  (tac-ev-when-pseudo-term-fncall
                                   cmr::pseudo-term-var-list->names-when-pseudo-term-listp)))
          (acl2::use-termhint
           (b* ((target-pattern (tac-intersect-propagate-rule->target-pattern rule))
                (desc-pos (tac-intersect-propagate-rule->descent-pos rule))
                (desc-var (pseudo-term-var->name (nth desc-pos (pseudo-term-call->args target-pattern))))
                (int-var (tac-intersect-propagate-rule->intersect-var rule))
                ((mv ?ok subst) (cmr::term-unify-strict target-pattern arg nil)))
             `(:use ((:instance tac-intersect-propagate-rule-wellformed-implies
                      (env ,(acl2::hq (cons (cons int-var w)
                                            (tac-ev-alist subst env)))))
                     (:instance tac-intersect-propagate-rule-wellformed-implies
                      (env ,(acl2::hq (list* (cons desc-var (and new-assum desc-new-val))
                                             (cons int-var w)
                                             (tac-ev-alist subst env))))))))))
  :rule-classes nil)



(defthm tac-intersect-propagate-rule-wellformed-implies-can-rewrite-inner2
  (b* ((target-fn (tac-intersect-propagate-rule->target-fn rule))
       (target-pattern (tac-intersect-propagate-rule->target-pattern rule))
       (target-type (tac-function-return-type target-fn))
       (desc-type (tac-intersect-propagate-rule->result-type rule))
       (desc-pos (tac-intersect-propagate-rule->descent-pos rule))
       (desc-var (pseudo-term-var->name (nth desc-pos (pseudo-term-call->args target-pattern))))
       (desc-term (nth desc-pos (pseudo-term-call->args arg)))
       (int-var (tac-intersect-propagate-rule->intersect-var rule))
       (int-term (tac-intersect-propagate-rule->intersect-term rule))
       ((mv ok subst) (cmr::term-unify-strict target-pattern arg nil))
       (new-int-val (tac-ev int-term
                            (cons (cons int-var w)
                                  (tac-ev-alist subst env))))
       (desc-val (tac-ev desc-term env))
       (target-val (tac-ev arg env))
       (target-new-val (tac-ev target-pattern (cons (cons desc-var desc-new-val)
                                                    (tac-ev-alist subst env)))))
    (implies (and (tac-ev-theoremp* (cmr::rewrite-term rule))
                  (tac-intersect-propagate-rule-wellformed rule)
                  ok
                  ;; (eq rule.rhs.fn 'pred-set-intersects)
                    
                  (if (eq desc-type :set)
                      (iff (pred-set-intersects new-int-val desc-val)
                           (and new-assum
                                (pred-set-intersects new-int-val desc-new-val)))
                    (iff (pred-rel-intersects new-int-val desc-val)
                         (and new-assum
                              (pred-rel-intersects new-int-val desc-new-val)))))
             (and (implies (eq target-type :set)
                           (iff (pred-set-intersects w target-val)
                                (and new-assum
                                     (pred-set-intersects w target-new-val))))
                  (implies (not (eq target-type :set))
                           (iff (pred-rel-intersects w target-val)
                                (and new-assum
                                     (pred-rel-intersects w target-new-val)))))))
  :hints (("goal" :use ((:instance tac-intersect-propagate-rule-wellformed-implies-can-rewrite-inner))
           :in-theory (enable lookup-of-nth-var-in-pattern-in-subst)))
  :rule-classes nil)

(define tac-intersect-propagate-rules-wellformed ((rules tac-rewritelist-p))
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-intersect-propagate-rule-wellformed (cdar rules)))
         (tac-intersect-propagate-rules-wellformed (cdr rules))))
  ///
  (defthm tac-intersect-propagate-rules-wellformed-of-tac-intersect-propagate-rules
    (tac-intersect-propagate-rules-wellformed (tac-intersect-propagate-rules))
    :hints(("Goal" :in-theory (enable (tac-intersect-propagate-rules)))))

  (defthmd tac-intersect-propagate-rules-wellformed-when-subsetp
    (implies (and (subsetp-equal x y)
                  (tac-intersect-propagate-rules-wellformed y))
             (tac-intersect-propagate-rules-wellformed x))
    :hints (("goal" :use ((:functional-instance acl2::element-list-p-when-subsetp-equal-non-true-list
                           (acl2::element-p (lambda (x)
                                              (or (not (consp x))
                                                  (tac-intersect-propagate-rule-wellformed (cdr x)))))
                           (acl2::element-list-p tac-intersect-propagate-rules-wellformed)
                           (acl2::element-example (lambda () nil))
                           (acl2::element-list-final-cdr-p (lambda (x) t))))
             :do-not-induct t)))

  (local (in-theory (enable tac-rewritelist-fix))))

                              
                            
       

(defsection tac-intersect-propagate-rule-typed
  (defun-sk tac-intersect-propagate-rule-typed (rule)
    (forall (ctx)
            (b* (((cmr::rewrite rule))
                 (lhs-type (tac-term-type rule.lhs ctx))
                 (rhs-type (tac-term-type rule.rhs ctx)))
              (implies (equal lhs-type :pred)
                       (equal rhs-type :pred))))
    :rewrite :direct)

  (fty::deffixcong cmr::rewrite-equiv iff (tac-intersect-propagate-rule-typed rule) rule
    :hints (("goal" :use ((:instance tac-intersect-propagate-rule-typed-necc
                           (rule (cmr::rewrite-fix rule))
                           (ctx (tac-intersect-propagate-rule-typed-witness rule)))
                          (:instance tac-intersect-propagate-rule-typed-necc
                           (rule rule)
                           (ctx (tac-intersect-propagate-rule-typed-witness (cmr::rewrite-fix rule)))))
             :in-theory (disable tac-intersect-propagate-rule-typed-necc))))
  
  (in-theory (disable tac-intersect-propagate-rule-typed)))

(local (defthm prefixp-of-cons
         (equal (acl2::prefixp (cons a b) c)
                (And (consp c)
                     (equal (car c) a)
                     (acl2::prefixp b (cdr c))))
         :hints(("Goal" :in-theory (enable acl2::prefixp)))))


(defthm tac-intersect-propagate-rule-typed-and-wellformed-implies
  (b* (((cmr::rewrite rule)))
    (implies (and ;; (tac-intersect-propagate-rule-typed rule)
              (tac-intersect-propagate-rule-wellformed rule)
              (equal (tac-term-type rule.lhs ctx) :pred))
             (equal (tac-type-fix
                     (cdr (hons-assoc-equal (pseudo-term-var->name
                                             (nth (tac-intersect-propagate-rule->descent-pos rule)
                                                  (pseudo-term-call->args
                                                   (tac-intersect-propagate-rule->target-pattern rule))))
                                            ctx)))
                    (tac-intersect-propagate-rule->result-type rule))))
  :hints(("Goal" :in-theory (e/d (tac-intersect-propagate-rule->result-type
                                    tac-intersect-propagate-rule->target-pattern
                                    tac-intersect-propagate-rule->descent-pos
                                    tac-intersect-propagate-rule-wellformed
                                    tac-intersect-propagate-rule->target-fn
                                    nth-when-prefix)
                                 (CMR::PSEUDO-TERM-VAR-LIST->NAMES-WHEN-PSEUDO-TERM-LISTP
                                  nth-of-tac-termlist-types))
          :use ((:instance nth-of-tac-termlist-types
                 (n (tac-intersect-propagate-rule->descent-pos rule))
                 (x (pseudo-term-call->args
                     (tac-intersect-propagate-rule->target-pattern rule))))))))

(defthm tac-intersect-propagate-rule-typed-and-wellformed-implies2
  (b* (((cmr::rewrite rule))
       (pat (tac-intersect-propagate-rule->target-pattern rule))
       ((mv ok ?subst) (cmr::term-unify-strict pat target nil)))
    (implies (and ;; (tac-intersect-propagate-rule-typed rule)
              ok
              (tac-intersect-propagate-rule-wellformed rule)
              (tac-term-type target ctx))
             (equal (tac-term-type
                     (nth (tac-intersect-propagate-rule->descent-pos rule)
                          (pseudo-term-call->args target))
                     ctx)
                    (tac-intersect-propagate-rule->result-type rule))))
  :hints(("Goal" :in-theory (e/d (tac-intersect-propagate-rule->result-type
                                    tac-intersect-propagate-rule->target-pattern
                                    tac-intersect-propagate-rule->descent-pos
                                    tac-intersect-propagate-rule-wellformed
                                    tac-intersect-propagate-rule->target-fn
                                    nth-when-prefix)
                                 (CMR::PSEUDO-TERM-VAR-LIST->NAMES-WHEN-PSEUDO-TERM-LISTP
                                  nth-of-tac-termlist-types))
          :expand ((tac-term-type target ctx)
                   (:free (pat) (cmr::term-unify-strict pat target nil)))
          :use ((:instance nth-of-tac-termlist-types
                 (n (tac-intersect-propagate-rule->descent-pos rule))
                 (x (pseudo-term-call->args target))
                 (ctx ctx))))))

(defthm tac-term-type-of-intersect-term-when-wellformed
  (implies (and (tac-intersect-propagate-rule-wellformed rule)
                (tac-intersect-propagate-rule-typed rule)
                (tac-term-type (tac-intersect-propagate-rule->target-pattern rule) ctx)
                (equal (tac-type-fix
                        (cdr (hons-assoc-equal
                              (tac-intersect-propagate-rule->intersect-var rule) ctx)))
                       (tac-term-type (tac-intersect-propagate-rule->target-pattern rule) ctx)))
           (equal (tac-term-type (tac-intersect-propagate-rule->intersect-term rule) ctx)
                  (tac-intersect-propagate-rule->result-type rule)))
  :hints(("Goal" :in-theory (e/d (tac-intersect-propagate-rule-wellformed
                                  tac-intersect-propagate-rule->target-pattern
                                  tac-intersect-propagate-rule->intersect-term
                                  tac-intersect-propagate-rule->intersect-var
                                  tac-intersect-propagate-rule->result-type
                                  tac-intersect-propagate-rule->descent-pos
                                  tac-intersect-propagate-rule->target-fn
                                  acl2::prefixp)
                                 (tac-intersect-propagate-rule-typed-necc
                                  cmr::pseudo-term-var-list->names-when-pseudo-term-listp))
          :use ((:instance tac-intersect-propagate-rule-typed-necc))
          :do-not-induct t)))


;; (encapsulate nil
           
;; (defthm tac-intersect-propagate-rule-typed-and-wellformed-implies3
;;   (b* (((cmr::rewrite rule))
;;        (pat (tac-intersect-propagate-rule->target-pattern rule))
;;        ((mv ok ?subst) (cmr::term-unify-strict pat target nil)))
;;     (implies (and ;; (tac-intersect-propagate-rule-typed rule)
;;               ok
;;               (tac-intersect-propagate-rule-wellformed rule)
;;               (tac-term-type target ctx))
;;              (equal (cdr (hons-assoc-equal
;;                           (PSEUDO-TERM-VAR->NAME
;;                            (NTH (TAC-INTERSECT-PROPAGATE-RULE->DESCENT-POS RULE)
;;                                 (PSEUDO-TERM-CALL->ARGS
;;                                  (TAC-INTERSECT-PROPAGATE-RULE->TARGET-PATTERN RULE))))
;;                           ctx))
;;                     (tac-intersect-propagate-rule->result-type rule))))
;;   :hints(("Goal" :in-theory (e/d (tac-intersect-propagate-rule->result-type
;;                                     tac-intersect-propagate-rule->target-pattern
;;                                     tac-intersect-propagate-rule->descent-pos
;;                                     tac-intersect-propagate-rule-wellformed
;;                                     tac-intersect-propagate-rule->target-fn
;;                                     nth-when-prefix
;;                                     nth-of-equal-to-termlist-subst-strict)
;;                                  (CMR::PSEUDO-TERM-VAR-LIST->NAMES-WHEN-PSEUDO-TERM-LISTP
;;                                   nth-of-tac-termlist-types))
;;           :expand ((tac-term-type target ctx)
;;                    (:free (pat) (cmr::term-unify-strict pat target nil)))
;;           :use ((:instance nth-of-tac-termlist-types
;;                  (n (tac-intersect-propagate-rule->descent-pos rule))
;;                  (x (pseudo-term-call->args target))
;;                  (ctx ctx))))))


;;          ("Goal" :use ((:instance tac-intersect-propagate-rule-typed-and-wellformed-implies
;;                         (ctx
;;                          (cons
;;                           (cons (tac-intersect-propagate-rule->intersect-var rule)
;;                                 (tac-intersect-propagate-rule->result-type rule))
;;                           (tac-subst-ctx (mv-nth 1 (cmr::term-unify-strict
;;                                                     (tac-intersect-propagate-rule->target-pattern rule)
;;                                                     target nil))
;;                                          ctx)))))
;;           :expand ((cmr::term-unify-strict (tac-intersect-propagate-rule->target-pattern rule)
;;                                           target nil)))
;;          (and stable-under-simplificationp
;;               '(:in-theory (enable tac-intersect-propagate-rule->target-pattern
;;                                    tac-intersect-propagate-rule->target-fn
;;                                    tac-intersect-propagate-rule->result-type
;;                                    tac-intersect-propagate-rule->intersect-var
;;                                    tac-intersect-propagate-rule->descent-pos
;;                                    tac-intersect-propagate-rule-wellformed
;;                                    acl2::prefixp)
;;                 :expand ((tac-term-type target ctx))))))
                                   
                  




(define tac-intersect-propagate-rules-typed ((rules tac-rewritelist-p))
  :verify-guards nil
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-intersect-propagate-rule-typed (cdar rules)))
         (tac-intersect-propagate-rules-typed (cdr rules))))
  ///
  (defthm tac-intersect-propagate-rules-typed-of-tac-intersect-propagate-rules
    (tac-intersect-propagate-rules-typed (tac-intersect-propagate-rules))
    :hints(("Goal" :in-theory (e/d ((tac-intersect-propagate-rules)
                                    tac-intersect-propagate-rule-typed)
                                   ((tac-intersect-propagate-rules-typed))))))

  (defthmd tac-intersect-propagate-rules-typed-when-subsetp
    (implies (and (subsetp-equal x y)
                  (tac-intersect-propagate-rules-typed y))
             (tac-intersect-propagate-rules-typed x))
    :hints (("goal" :use ((:functional-instance acl2::element-list-p-when-subsetp-equal-non-true-list
                           (acl2::element-p (lambda (x)
                                              (or (not (consp x))
                                                  (tac-intersect-propagate-rule-typed (cdr x)))))
                           (acl2::element-list-p tac-intersect-propagate-rules-typed)
                           (acl2::element-example (lambda () nil))
                           (acl2::element-list-final-cdr-p (lambda (x) t))))
             :do-not-induct t)))

  (local (in-theory (enable tac-rewritelist-fix))))

(defthmd tac-ev-theoremlist-p-of-tac-rewritelist-terms-when-subsetp
  (implies (and (subsetp-equal x y)
                (tac-ev-theoremlist-p (tac-rewritelist-terms y)))
           (tac-ev-theoremlist-p (tac-rewritelist-terms x)))
  :hints (("goal" :use ((:functional-instance acl2::element-list-p-when-subsetp-equal-non-true-list
                         (acl2::element-p (lambda (x)
                                            (or (not (consp x))
                                                (tac-ev-theoremp* (cmr::rewrite-term (cdr x))))))
                         (acl2::element-list-p (lambda (x)
                                                 (tac-ev-theoremlist-p (tac-rewritelist-terms x))))
                         (acl2::element-example (lambda () nil))
                         (acl2::element-list-final-cdr-p (lambda (x) t))))
           :in-theory (enable tac-rewritelist-terms
                              tac-ev-theoremlist-p)
           :do-not-induct t)))


(defsection tac-ev-theorem-rewritesp-of-tac-intersect-propagate-rules
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
  
  (defthm tac-ev-theorem-rewritesp-of-tac-intersect-propagate-rules
    (tac-ev-theoremlist-p (tac-rewritelist-terms (tac-intersect-propagate-rules)))
    :hints(("Goal" :in-theory (acl2::e/d* ((tac-intersect-propagate-rules)
                                           tac-ev-theoremp*-expand)
                                          (tac-functions
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



(local
 (define collect-intersect-propagate-table ((rules tac-rewritelist-p))
   :guard (tac-intersect-propagate-rules-wellformed rules)
   :returns (table (and (true-list-listp table)
                        (alistp table)))
   :verify-guards nil
   :hooks nil
   (b* (((when (atom rules)) nil)
        (rest (collect-intersect-propagate-table (cdr rules)))
        ((unless (mbt (consp (car rules)))) rest)
        (pair (car rules))
        (rule (cdr pair))
        (target (tac-intersect-propagate-rule->target-fn rule))
        (entry (cdr (assoc-equal target rest)))
        (new-entry (update-nth (tac-intersect-propagate-rule->descent-pos rule)
                               pair entry)))
     (cons (cons target new-entry) rest))
   ///
   (local (defthm true-listp-assoc-equal
            (implies (true-list-listp x)
                     (true-listp (cdr (assoc-equal k x))))))
   (local (defthm consp-assoc-equal-under-iff
            (implies (alistp x)
                     (iff (consp (assoc-equal k x))
                          (assoc-equal k x)))))
   (verify-guards collect-intersect-propagate-table
     :hints(("Goal" :in-theory (enable tac-intersect-propagate-rules-wellformed))))))

(make-event
 `(defconst *tac-intersect-propagate-table*
    ',(fast-alist-free
       (fast-alist-clean (collect-intersect-propagate-table (tac-intersect-propagate-rules))))))

(define tac-intersect-propagate-table ()
  :returns (table symbol-alistp)
  *tac-intersect-propagate-table*
  ///
  (defret tac-rewritelist-p-of-<fn>
    (tac-rewritelist-p (cdr (hons-assoc-equal fn table))))

  (defretd <fn>-lookup-subset-of-tac-intersect-propagate-rules
    (subsetp-equal (cdr (hons-assoc-equal fn table))
                   (tac-intersect-propagate-rules))
    :hints(("Goal" :in-theory (enable tac-intersect-propagate-rules))))

  (local (defthm nth-open
           (equal (nth n x)
                  (if (zp n)
                      (car x)
                    (nth (1- n) (cdr x))))))

  (defret <fn>-lookup-index-function-correct
    (implies (and (< (nfix n) (len (tac-function-argument-types fn)))
                  (hons-assoc-equal fn table))
             (equal (tac-intersect-propagate-rule->target-fn
                     (cdr (nth n (cdr (hons-assoc-equal fn table)))))
                    fn)))

  (defret <fn>-lookup-index-posn-correct
    (implies (and (< (nfix n) (len (tac-function-argument-types fn)))
                  (hons-assoc-equal fn table))
             (equal (tac-intersect-propagate-rule->descent-pos
                     (cdr (nth n (cdr (hons-assoc-equal fn table)))))
                    (nfix n))))
  
  (in-theory (disable (tac-intersect-propagate-table)
                      tac-intersect-propagate-table))

  (defret <fn>-lookup-wellformed
    (tac-intersect-propagate-rules-wellformed (cdr (hons-assoc-equal fn table)))
    :hints(("Goal" :in-theory (enable tac-intersect-propagate-rules-wellformed-when-subsetp)
            :use <fn>-lookup-subset-of-tac-intersect-propagate-rules)))

  (defret <fn>-lookup-typed
    (tac-intersect-propagate-rules-typed (cdr (hons-assoc-equal fn table)))
    :hints(("Goal" :in-theory (enable tac-intersect-propagate-rules-typed-when-subsetp)
            :use <fn>-lookup-subset-of-tac-intersect-propagate-rules)))

  (defret <fn>-lookup-theorems
    (tac-ev-theoremlist-p (tac-rewritelist-terms (cdr (hons-assoc-equal fn table))))
    :hints(("Goal" :in-theory (enable tac-ev-theoremlist-p-of-tac-rewritelist-terms-when-subsetp)
            :use <fn>-lookup-subset-of-tac-intersect-propagate-rules))))
                  






(encapsulate nil
  (acl2::defconsts *tac-var-intro-rules*
    (b* (((mv err rewrites)
          (tac-collect-rewrites-aux
           (cdr (assoc 'var-intro-rules (table-alist 'tac-rules (w state))))
           (w state))))
      (if err
          (er hard? '*tac-var-intro-rules* "~@0" err)
        rewrites)))

  (define tac-var-intro-rules ()
    :returns (rewrites tac-rewritelist-p)
    *tac-var-intro-rules*
    ///
    (in-theory (disable (tac-var-intro-rules)))))



(define tac-var-intro-rule-wellformed ((rule cmr::rewrite-p))
  (b* (((cmr::rewrite rule)))
    (and (eq rule.equiv 'iff)
         (pseudo-term-case rule.lhs :fncall)
         (b* (((pseudo-term-fncall rule.lhs)))
           (and (eq rule.lhs.fn 'pred-in-set)
                (pseudo-term-case (first rule.lhs.args) :var)
                (not (member-equal (pseudo-term-var->name (first rule.lhs.args))
                                   (cmr::term-vars (second rule.lhs.args))))
                (subsetp-equal (cmr::termlist-vars rule.hyps)
                               (cmr::term-vars (second rule.lhs.args)))
                (subsetp-equal (cmr::term-vars rule.rhs)
                               (cmr::term-vars rule.lhs)))))))

(define tac-var-intro-rules-wellformed ((rules tac-rewritelist-p))
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-var-intro-rule-wellformed (cdar rules)))
         (tac-var-intro-rules-wellformed (cdr rules))))
  ///
  (defthm tac-var-intro-rules-wellformed-of-tac-var-intro-rules
    (tac-var-intro-rules-wellformed (tac-var-intro-rules))
    :hints(("Goal" :in-theory (enable (tac-var-intro-rules)))))

  (local (in-theory (enable tac-rewritelist-fix))))


(defsection tac-var-intro-rule-typed
  (defun-sk tac-var-intro-rule-typed (rule)
    (forall (ctx)
            (b* (((cmr::rewrite rule))
                 (lhs-type (tac-term-type rule.lhs ctx))
                 (rhs-type (tac-term-type rule.rhs ctx))
                 (hyp-types (tac-termlist-types rule.hyps ctx)))
              (implies (equal lhs-type :pred)
                       (and (equal rhs-type :pred)
                            (subsetp-equal hyp-types '(:pred))))))
    :rewrite :direct)

  (fty::deffixcong cmr::rewrite-equiv iff (tac-var-intro-rule-typed rule) rule
    :hints (("goal" :use ((:instance tac-var-intro-rule-typed-necc
                           (rule (cmr::rewrite-fix rule))
                           (ctx (tac-var-intro-rule-typed-witness rule)))
                          (:instance tac-var-intro-rule-typed-necc
                           (rule rule)
                           (ctx (tac-var-intro-rule-typed-witness (cmr::rewrite-fix rule)))))
             :in-theory (disable tac-var-intro-rule-typed-necc))))

  (in-theory (disable tac-var-intro-rule-typed)))


(define tac-var-intro-rules-typed ((rules tac-rewritelist-p))
  :verify-guards nil
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-var-intro-rule-typed (cdar rules)))
         (tac-var-intro-rules-typed (cdr rules))))
  ///
  (defthm tac-var-intro-rules-typed-of-tac-var-intro-rules
    (tac-var-intro-rules-typed (tac-var-intro-rules))
    :hints(("Goal" :in-theory (e/d ((tac-var-intro-rules)
                                    tac-var-intro-rule-typed
                                    acl2::prefixp
                                    tac-termlist-types)
                                   ((tac-var-intro-rules-typed))))))

  (local (in-theory (enable tac-rewritelist-fix))))



(defsection tac-ev-theorem-rewritesp-of-tac-var-intro-rules
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
  
  (defthm tac-ev-theorem-rewritesp-of-tac-var-intro-rules
    (tac-ev-theoremlist-p (tac-rewritelist-terms (tac-var-intro-rules)))
    :hints(("Goal" :in-theory (acl2::e/d* ((tac-var-intro-rules)
                                           tac-ev-theoremp*-expand)
                                          (tac-functions
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



