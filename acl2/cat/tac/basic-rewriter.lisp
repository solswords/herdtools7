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

(include-book "basic-rewrite-rules")
(include-book "centaur/meta/subst-vars" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(local (std::add-default-post-define-hook :fix))



(define tac-rewrite-apply-rule ((rule cmr::rewrite-p)
                                (fn pseudo-fnsym-p)
                                (args pseudo-term-listp))
  :returns (mv ok
               (rhs pseudo-termp)
               (subst cmr::pseudo-term-subst-p))
  (b* (((cmr::rewrite rule))
       ((unless (and (eq rule.equiv 'equal)
                     (pseudo-term-case rule.lhs :fncall)))
        (mv nil nil nil))
       ((pseudo-term-fncall rule.lhs))
       ((unless (eq rule.lhs.fn (pseudo-fnsym-fix fn)))
        (mv nil nil nil))
       ((mv ok subst) (cmr::termlist-unify-strict rule.lhs.args args nil))
       ((unless ok)
        (mv nil nil nil)))
    (mv t rule.rhs subst))
  ///
  (local (in-theory (enable tac-ev-of-fncall-args)))
  
  (local (defthm tac-ev-list-equal-of-termlist-subst-strict
           (implies (equal (pseudo-term-list-fix x)
                           (cmr::termlist-subst-strict pat subst))
                    (equal (tac-ev-lst x a)
                           (tac-ev-lst pat (tac-ev-alist subst a))))
           :hints (("goal" :use ((:instance tac-ev-lst-of-pseudo-term-list-fix-x
                                  (x x) (a a)))
                    :in-theory (disable tac-ev-lst-of-pseudo-term-list-fix-x
                                        tac-ev-lst-pseudo-term-list-equiv-congruence-on-x)))))

  (local (defthm tac-rewrite-hyps-ok-necc-special
           (b* (((cmr::rewrite rule))
                (subst-env (tac-ev-alist subst env))
                (subst-ctx (tac-subst-ctx subst ctx)))
             (implies (and (tac-rewrite-hyps-ok rule)
                           (tac-typed-env-p env ctx)
                           ;; unify-ok
                           (tac-term-type rule.lhs subst-ctx))
                      (tac-ev-cube rule.hyps subst-env)))
           :hints (("goal" :use ((:instance tac-rewrite-hyps-ok-necc
                                  (env (tac-ev-alist subst env))
                                  (ctx (tac-subst-ctx subst ctx))))
                    :in-theory (disable tac-rewrite-hyps-ok-necc)))))

  (local (defthm tac-term-type-of-tac-subst-ctx
           (equal (Tac-term-type x (tac-subst-ctx subst ctx))
                  (tac-term-type (cmr::term-subst-strict x subst) ctx))))
  (local (in-theory (disable tac-term-type-of-term-subst-strict)))
  
  (defret <fn>-correct
    (implies (and ok
                  (tac-ev-theoremp (cmr::rewrite-term rule))
                  (tac-rewrite-hyps-ok rule)
                  (tac-typed-env-p env ctx)
                  (tac-term-type (pseudo-term-fncall fn args) ctx))
             (equal (tac-ev rhs (tac-ev-alist subst env))
                    (tac-ev (pseudo-term-fncall fn args) env)))
    :hints(("Goal" :in-theory (e/d (cmr::rewrite-term)
                                   (;; tac-rewrite-hyps-ok-necc
                                    ))
            :expand ((CMR::TERM-UNIFY-STRICT (CMR::REWRITE->LHS RULE)
                                             (pseudo-term-fncall fn args) NIL)
                     (:free (subst) (cmr::term-subst-strict (cmr::rewrite->lhs rule) subst)))
            :use ((:instance tac-ev-falsify
                   (a (tac-ev-alist (mv-nth 1 (cmr::termlist-unify-strict
                                               (pseudo-term-call->args (cmr::rewrite->lhs rule))
                                               args nil))
                                    env))
                   (x (cmr::rewrite-term rule)))
                  ;; (:instance tac-rewrite-hyps-ok-necc
                  ;;  (x (pseudo-term-fncall fn args)))
                  ))))

  (local (defthm tac-rewrite-rhs-preserved-necc-special
           (b* (((cmr::rewrite rule))
                (type (tac-term-type (cmr::term-subst-strict rule.lhs subst) ctx)))
             (implies (and (tac-rewrite-rhs-preserved rule)
                           type)
                      (equal (tac-term-type (cmr::term-subst-strict rule.rhs subst) ctx)
                             type)))
           :hints (("goal" :use ((:instance tac-rewrite-rhs-preserved-necc
                                  (ctx (tac-subst-ctx subst ctx))))
                    :in-theory (disable tac-rewrite-rhs-preserved-necc)))))
                          
  
  (defret <fn>-preserves-type
    (implies (and ok
                  (tac-rewrite-rhs-preserved rule)
                  (equal type (tac-term-type (pseudo-term-fncall fn args) ctx))
                  type)
             (equal (tac-term-type (cmr::term-subst-strict rhs subst) ctx)
                    type))
    :hints (("goal" 
            :expand ((CMR::TERM-UNIFY-STRICT (CMR::REWRITE->LHS RULE)
                                             (pseudo-term-fncall fn args) NIL)
                     (:free (subst) (cmr::term-subst-strict (cmr::rewrite->lhs rule) subst))))))

  (defret vars-of-<fn>
    (implies (not (member v (cmr::termlist-vars args)))
             (not (member v (cmr::term-subst-vars subst))))))

(local (defthm alistp-when-pseudo-term-subst-p
         (implies (cmr::pseudo-term-subst-p x)
                  (alistp x))))

(local (in-theory (disable pseudo-termp
                           pseudo-term-listp)))

(defines tac-rewrite
  (define tac-rewrite ((clk natp)
                       (x pseudo-termp)
                       (subst cmr::pseudo-term-subst-p))
    :measure (acl2::nat-list-measure (list clk 0 (pseudo-term-count x) 0 0))
    :returns (new-x pseudo-termp)
    :verify-guards nil
    (pseudo-term-case x
      :fncall (b* ((args (tac-rewrite-list clk x.args subst)))
                (tac-rewrite-fncall clk x.fn args))
      :var (cdr (assoc-equal x.name (cmr::pseudo-term-subst-fix subst)))
      :otherwise (cmr::term-subst-strict x subst)))

  (define tac-rewrite-list ((clk natp)
                            (x pseudo-term-listp)
                            (subst cmr::pseudo-term-subst-p))
    :measure (acl2::nat-list-measure (list clk 0 (pseudo-term-list-count x) 0 0))
    :returns (new-x (and (pseudo-term-listp new-x)
                         (Equal (len new-x) (len x))))
    (if (atom x)
        nil
      (cons (tac-rewrite clk (car x) subst)
            (tac-rewrite-list clk (cdr x) subst))))

  (define tac-rewrite-fncall ((clk natp)
                              (fn pseudo-fnsym-p)
                              (args pseudo-term-listp))
    :measure (acl2::nat-list-measure (list clk 0 0 1 0))
    :returns (new-x pseudo-termp)
    (tac-rewrite-apply-rules clk (tac-rewrites) fn args))

  (define tac-rewrite-apply-rules ((clk natp)
                                   (rules tac-rewritelist-p)
                                   (fn pseudo-fnsym-p)
                                   (args pseudo-term-listp))
    :measure (acl2::nat-list-measure (list clk 0 0 0 (len rules)))
    :returns (new-x pseudo-termp)
    (if (atom rules)
        (pseudo-term-fncall fn args)
      (b* (((unless (mbt (consp (car rules))))
            (tac-rewrite-apply-rules clk (cdr rules) fn args))
           ((mv ok rhs subst) (tac-rewrite-apply-rule (cdar rules) fn args))
           ((when (and ok (not (zp clk))))
            (tac-rewrite (1- clk) rhs subst)))
        (tac-rewrite-apply-rules clk (cdr rules) fn args))))
  ///
  (verify-guards tac-rewrite)

  (defun termlists-types-preserved (x y subst ctx)
    (if (atom x)
        t
      (and (let ((orig (tac-term-type (cmr::term-subst-strict (car x) subst) ctx)))
             (or (not orig)
                 (equal orig (tac-term-type (car y) ctx))))
           (termlists-types-preserved (cdr x) (cdr y) subst ctx))))

  (local (defthmd termlists-types-preserved-when-consp
           (implies (consp x)
                    (equal (termlists-types-preserved x y subst ctx)
                           (and (let ((orig (tac-term-type (cmr::term-subst-strict (car x) subst) ctx)))
                                  (or (not orig)
                                      (equal orig (tac-term-type (car y) ctx))))
                                (termlists-types-preserved (cdr x) (cdr y) subst ctx))))))
  
  (local (defthm open-prefixp
           (equal (acl2::prefixp (cons a b) x)
                  (and (consp x)
                       (equal (car x) a)
                       (acl2::prefixp b (cdr x))))
           :hints(("Goal" :in-theory (enable acl2::prefixp)))))

  (local (defthm prefixp-of-nil
           (acl2::prefixp nil x)
           :hints(("Goal" :in-theory (enable acl2::prefixp)))))
  
  
  (local
   (defthm term-type-when-termlists-types-preserved
     (implies (and (bind-free '((subst . subst)) (subst))
                   (termlists-types-preserved (pseudo-term-call->args x) rw-args subst ctx)
                   (equal xsubst  (cmr::term-subst-strict x subst))
                   (equal type (tac-term-type xsubst ctx))
                   type
                   (equal (len rw-args) (len (pseudo-term-call->args x)))
                   (pseudo-term-case x :fncall))
              (equal (tac-term-type (pseudo-term-fncall
                                     (pseudo-term-fncall->fn x) rw-args)
                                    ctx)
                     type))
     :hints(("Goal"
             :in-theory (e/d (tac-function-argument-types
                              termlists-types-preserved-when-consp)
                             (termlists-types-preserved))
             :do-not-induct t
             :expand ((cmr::term-subst-strict x subst)
                      ;; (cmr::termlist-subst-strict nil subst)
                      ;; (cmr::termlist-subst-strict (pseudo-term-call->args x) subst)
                      ;; (cmr::termlist-subst-strict (cdr (pseudo-term-call->args x)) subst)
                      ;; (cmr::termlist-subst-strict (cddr (pseudo-term-call->args x)) subst)
                      (:free (fn args) (tac-term-type (pseudo-term-fncall fn args) ctx))))
            ;; (and stable-under-simplificationp
            ;;      '(:expand ((termlists-types-preserved (pseudo-term-call->args x) rw-args subst ctx)
            ;;                 (termlists-types-preserved (cdr (pseudo-term-call->args x)) (cdr rw-args) subst ctx))))
            ;; (and stable-under-simplificationp
            ;;      '(:expand ((cmr::termlist-subst-strict (cddr (pseudo-term-call->args x)) subst)
            ;;                 (cmr::termlist-subst-strict nil subst)
            ;;                 (termlists-types-preserved (cddr (pseudo-term-call->args x)) (cddr rw-args) subst ctx))))
            )))


  (local (defthm tac-term-type-of-tac-subst-ctx
           (equal (Tac-term-type x (tac-subst-ctx subst ctx))
                  (tac-term-type (cmr::term-subst-strict x subst) ctx))))
  (local (in-theory (disable tac-term-type-of-term-subst-strict)))
  (std::defret-mutual tac-rewrite-types-preserved
    (defret tac-rewrite-types-preserved
      (let ((type (tac-term-type (cmr::term-subst-strict x subst) ctx)))
        (implies type
                 (equal (tac-term-type new-x ctx) type)))
      :hints ('(:expand (<call>)
                :do-not-induct t)
              (and stable-under-simplificationp
                   '(:expand ((cmr::term-subst-strict x subst)))))
      :fn tac-rewrite)

    (defret tac-rewrite-list-types-preserved
      (termlists-types-preserved x new-x subst ctx)
      :hints ('(:expand (<call>
                         (:free (newx) (termlists-types-preserved x newx subst ctx))
                         (:free (newx) (termlists-types-preserved nil newx subst ctx)))))
      :fn tac-rewrite-list)

    (defret tac-rewrite-fncall-types-preserved
      (let ((type (tac-term-type (pseudo-term-fncall fn args) ctx)))
        (implies type
                 (equal (tac-term-type new-x ctx) type)))
      :hints ('(:expand (<call>)))
      :fn tac-rewrite-fncall)

    (defret tac-rewrite-apply-rules-types-preserved
      (implies (tac-rewrites-rhs-preserved rules)
               (let ((type (tac-term-type (pseudo-term-fncall fn args) ctx)))
                 (implies type
                          (equal (tac-term-type new-x ctx) type))))
      :hints ('(:expand (<call>
                         (tac-rewrites-rhs-preserved rules))))
      :fn tac-rewrite-apply-rules))

  (defun tac-rewrite-list-evals-preserved (x new-x subst env ctx)
    (if (atom x)
        t
      (and (implies (or (not (pseudo-term-case (car x) :fncall))
                        (tac-term-type (cmr::term-subst-strict (car x) subst) ctx))
                    (equal (tac-ev (car new-x) env)
                           (tac-ev (car x) (tac-ev-alist subst env))))
           (tac-rewrite-list-evals-preserved (cdr x) (cdr new-x) subst env ctx))))

  (local (defthmd tac-rewrite-list-evals-preserved-when-consp
           (implies (consp x)
                    (equal (tac-rewrite-list-evals-preserved x new-x subst env ctx)
                           (and (implies (or (not (pseudo-term-case (car x) :fncall))
                                             (tac-term-type (cmr::term-subst-strict (car x) subst) ctx))
                                         (equal (tac-ev (car new-x) env)
                                                (tac-ev (car x) (tac-ev-alist subst env))))
                                (tac-rewrite-list-evals-preserved (cdr x) (cdr new-x) subst env ctx))))))
           

  (local (defthm fncall-of-term-subst-strict
           (implies (pseudo-term-case x :fncall)
                    (pseudo-term-case (cmr::term-subst-strict x subst) :fncall))
           :hints(("Goal" :expand ((cmr::term-subst-strict x subst))))))

  (defthm eval-preserved-of-rel-term-when-arg-evals-preserved
    (implies (and (tac-rewrite-list-evals-preserved
                   args rw-args subst env ctx)
                  (equal (len args) (len rw-args))
                  (tac-term-type (pseudo-term-fncall fn
                                                     (cmr::termlist-subst-strict args subst))
                                 ctx)
                  (pseudo-fnsym-p fn))
             (equal (tac-ev (cons fn rw-args) env)
                    (tac-ev (cons fn args) (tac-ev-alist subst env))))
    :hints (("goal" :expand ((:free (args)
                              (tac-term-type (pseudo-term-fncall fn args)
                                          ctx)))
             :in-theory (enable tac-function-return-type
                                tac-function-argument-types
                                tac-rewrite-list-evals-preserved-when-consp)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((cmr::termlist-subst-strict (cddr args) subst)
                             (tac-rewrite-list-evals-preserved
                              (cddr args) (cddr rw-args) subst env ctx))))))
  
  (std::defret-mutual tac-rewrite-correct
    (defret tac-rewrite-correct
      (implies (and (tac-term-type (cmr::term-subst-strict x subst) ctx)
                    (tac-typed-env-p env ctx))
               (equal (tac-ev new-x env)
                      (tac-ev x (tac-ev-alist subst env))))
      :hints ('(:expand (<call>)
                :do-not-induct t)
              (and stable-under-simplificationp
                   '(:expand ((cmr::term-subst-strict x subst))))
              (and stable-under-simplificationp
                   '(:cases ((equal (pseudo-term-kind x) :quote)
                             (equal (pseudo-term-kind x) :lambda)))))
      :fn tac-rewrite)

    (defret tac-rewrite-list-correct
      (implies (tac-typed-env-p env ctx)
               (tac-rewrite-list-evals-preserved x new-x subst env ctx))
      :hints ('(:expand (<call>
                         (:free (newx) (tac-rewrite-list-evals-preserved x newx subst env ctx))
                         (:free (newx) (tac-rewrite-list-evals-preserved nil newx subst env ctx)))))
      :fn tac-rewrite-list)

    (defret tac-rewrite-fncall-correct
      (implies (and (tac-term-type (pseudo-term-fncall fn args) ctx)
                    (tac-typed-env-p env ctx))
               (equal (tac-ev new-x env)
                      (tac-ev (pseudo-term-fncall fn args) env)))
      :hints ('(:expand (<call>)))
      :fn tac-rewrite-fncall)

    (defret tac-rewrite-apply-rules-correct
      (implies (and (tac-term-type (pseudo-term-fncall fn args) ctx)
                    (tac-typed-env-p env ctx)
                    (tac-ev-theoremlist-p (tac-rewritelist-terms rules))
                    (tac-rewrites-hyps-ok rules)
                    (tac-rewrites-rhs-preserved rules))
               (equal (tac-ev new-x env)
                      (tac-ev (pseudo-term-fncall fn args) env)))
      :hints ('(:expand (<call>
                         (:free (a b) (tac-ev-theoremlist-p (cons a b)))
                         (tac-rewritelist-terms rules)
                         (tac-rewrites-hyps-ok rules)
                         (tac-rewrites-rhs-preserved rules))))
      :fn tac-rewrite-apply-rules))
  (local (defthm tac-rewrite-apply-rules-of-0
           (equal (tac-rewrite-apply-rules 0 rules fn args)
                  (pseudo-term-fncall fn args))
           :hints (("goal" :induct (len rules)
                    :expand ((tac-rewrite-apply-rules 0 rules fn args))))))
  (local (in-theory (enable tac-rewritelist-fix)))
  (fty::deffixequiv-mutual tac-rewrite))

