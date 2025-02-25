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

(in-package "ASL")

(include-book "abs")
(include-book "ilog2-alg")
(local (include-book "ast-theory"))
(local (in-theory (disable (tau-system)
                           hons-assoc-equal
                           put-assoc-equal
                           floor mod)))


(defsection ilog2-loop-1

  (defconst *ilog2-loop-1*
    (find-nth-form 0 :s_while (assoc-equal "ILog2" (static_env_global->subprograms
                                                    (stdlib-static-env)))))

  (defconst *ilog2-loop-1-test*
    (s_while->test *ilog2-loop-1*))

  (defconst *ilog2-loop-1-body*
    (s_while->body *ilog2-loop-1*))

  (defthm ilog2-loop-1-correct
    (b* ((storage (local-env->storage
                   (env->local env)))
         (val-look (assoc-equal "__stdlib_local_val" storage))
         (val (cdr val-look))
         ((v_real val))
         (high-look (assoc-equal "__stdlib_local_high" storage))
         (high (cdr high-look))
         ((v_int high))
         (low-look (assoc-equal "__stdlib_local_low" storage))
         (low (cdr low-look))
         ((v_int low)))
      (implies (and val-look
                    (val-case val :v_real)
                    (<= 1 val.val)
                    high-look
                    (val-case high :v_int)
                    (<= 1 high.val)
                    low-look
                    (val-case low :v_int)
                    (natp clk)
                    (< (- (+ 1 (acl2::rational-exponent val.val)) high.val) clk)
                    (no-duplicatesp-equal (acl2::alist-keys storage)))
               (b* (((ev_normal res) (eval_loop env t *ilog2-loop-1-test* *ilog2-loop-1-body*))
                    ((continuing res.res))
                    ((mv low-spec high-spec) (acl2::ilog2-search-up val.val low.val high.val))
                    ((env env))
                    ((local-env env.local)))
                 (and (equal res.res.env
                             (change-env env
                                         :local (change-local-env
                                                 env.local
                                                 :storage (put-assoc-equal "__stdlib_local_low"
                                                                           (v_int low-spec)
                                                                           (put-assoc-equal "__stdlib_local_high"
                                                                                            (v_int high-spec)
                                                                                            env.local.storage)))))
                      (equal (eval_result-kind res) :ev_normal)
                      (equal (control_flow_state-kind res.res) :continuing)))))
    :hints (("goal" :induct (loop-induct env clk *ilog2-loop-1-test* *ilog2-loop-1-body* t)
             :in-theory (enable check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                pop_scope)
             :expand ((ACL2::ILOG2-SEARCH-UP
                       (V_REAL->VAL (CDR (HONS-ASSOC-EQUAL "__stdlib_local_val"
                                                           (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))
                       (V_INT->VAL (CDR (HONS-ASSOC-EQUAL "__stdlib_local_low"
                                                          (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))
                       (V_INT->VAL
                        (CDR (HONS-ASSOC-EQUAL "__stdlib_local_high"
                                               (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((eval_loop env t *ilog2-loop-1-test* *ilog2-loop-1-body*)))))))


(defsection ilog2-loop-2
  
  (defconst *ilog2-loop-2*
    (find-nth-form 1 :s_while (assoc-equal "ILog2" (static_env_global->subprograms
                                                    (stdlib-static-env)))))

  (defconst *ilog2-loop-2-test*
    (s_while->test *ilog2-loop-2*))

  (defconst *ilog2-loop-2-body*
    (s_while->body *ilog2-loop-2*))
                    
  
  (defthm ilog2-loop-2-correct
    (b* ((storage (local-env->storage
                   (env->local env)))
         (val-look (assoc-equal "__stdlib_local_val" storage))
         (val (cdr val-look))
         ((v_real val))
         (high-look (assoc-equal "__stdlib_local_high" storage))
         (high (cdr high-look))
         ((v_int high))
         (low-look (assoc-equal "__stdlib_local_low" storage))
         (low (cdr low-look))
         ((v_int low)))
      (implies (and val-look
                    (val-case val :v_real)
                    (< 0 val.val)
                    (< val.val 1)
                    high-look
                    (val-case high :v_int)
                    low-look
                    (val-case low :v_int)
                    (<= low.val -1)
                    (natp clk)
                    (< (- (+ 1 (- (acl2::rational-exponent val.val))) (- low.val)) clk)
                    (no-duplicatesp-equal (acl2::alist-keys storage)))
               (b* (((ev_normal res) (eval_loop env t *ilog2-loop-2-test* *ilog2-loop-2-body*))
                    ((continuing res.res))
                    ((mv low-spec high-spec) (acl2::ilog2-search-down val.val low.val high.val))
                    ((env env))
                    ((local-env env.local)))
                 (and (equal res.res.env
                             (change-env env
                                         :local (change-local-env
                                                 env.local
                                                 :storage (put-assoc-equal "__stdlib_local_low"
                                                                           (v_int low-spec)
                                                                           (put-assoc-equal "__stdlib_local_high"
                                                                                            (v_int high-spec)
                                                                                            env.local.storage)))))
                      (equal (eval_result-kind res) :ev_normal)
                      (equal (control_flow_state-kind res.res) :continuing)))))
    :hints (("goal" :induct (loop-induct env clk *ilog2-loop-2-test* *ilog2-loop-2-body* t)
             :in-theory (enable check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                pop_scope
                                v_to_bool)
             :expand ((ACL2::ILOG2-SEARCH-down
                       (V_REAL->VAL (CDR (HONS-ASSOC-EQUAL "__stdlib_local_val"
                                                      (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))
                       (V_INT->VAL (CDR (HONS-ASSOC-EQUAL "__stdlib_local_low"
                                                     (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))
                       (V_INT->VAL
                        (CDR (HONS-ASSOC-EQUAL "__stdlib_local_high"
                                          (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((eval_loop env t *ilog2-loop-2-test* *ilog2-loop-2-body*)))))))

(defsection ilog2-loop-3
  
  (defconst *ilog2-loop-3*
    (find-nth-form 2 :s_while (assoc-equal "ILog2" (static_env_global->subprograms
                                                    (stdlib-static-env)))))

  (defconst *ilog2-loop-3-test*
    (s_while->test *ilog2-loop-3*))

  (defconst *ilog2-loop-3-body*
    (s_while->body *ilog2-loop-3*))


  
  (defthm ilog2-loop-3-correct
    (b* ((storage (local-env->storage
                   (env->local env)))
         (val-look (assoc-equal "__stdlib_local_val" storage))
         (val (cdr val-look))
         ((v_real val))
         (high-look (assoc-equal "__stdlib_local_high" storage))
         (high (cdr high-look))
         ((v_int high))
         (low-look (assoc-equal "__stdlib_local_low" storage))
         (low (cdr low-look))
         ((v_int low))
         (mid-look (assoc-equal "__stdlib_local_mid" storage)))
      (implies (and val-look
                    (val-case val :v_real)
                    (< 0 val.val)
                    high-look
                    (val-case high :v_int)
                    low-look
                    (val-case low :v_int)
                    (not mid-look)
                    (natp clk)
                    (< (- high.val low.val) clk)
                    (no-duplicatesp-equal (acl2::alist-keys storage)))
               (b* (((ev_normal res) (eval_loop env t *ilog2-loop-3-test* *ilog2-loop-3-body*))
                    ((continuing res.res))
                    ((mv low-spec high-spec) (acl2::ilog2-binary-search val.val low.val high.val))
                    ((env env))
                    ((local-env env.local)))
                 (and (equal res.res.env
                             (change-env env
                                         :local (change-local-env
                                                 env.local
                                                 :storage (put-assoc-equal "__stdlib_local_low"
                                                                           (v_int low-spec)
                                                                           (put-assoc-equal "__stdlib_local_high"
                                                                                            (v_int high-spec)
                                                                                            env.local.storage)))))
                      (equal (eval_result-kind res) :ev_normal)
                      (equal (control_flow_state-kind res.res) :continuing)))))
    :hints (("goal" :induct (loop-induct env clk *ilog2-loop-3-test* *ilog2-loop-3-body* t)
             :in-theory (enable check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                pop_scope
                                v_to_bool)
             :expand ((acl2::ilog2-binary-search
                       (V_REAL->VAL (CDR (HONS-ASSOC-EQUAL "__stdlib_local_val"
                                                      (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))
                       (V_INT->VAL (CDR (HONS-ASSOC-EQUAL "__stdlib_local_low"
                                                     (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))
                       (V_INT->VAL
                        (CDR (HONS-ASSOC-EQUAL "__stdlib_local_high"
                                          (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((eval_loop env t *ilog2-loop-3-test* *ilog2-loop-3-body*)))))))


(defsection ilog2-correct


  (define ilog2-safe-clock ((val rationalp))
    :guard (< 0 val)
    :returns (clock posp :rule-classes :type-prescription)
    (+ 1 (max (max (acl2::rational-exponent val)
                   (- (acl2::rational-exponent val)))
              (if (<= 1 val)
                  (b* (((mv low high) (acl2::ilog2-search-up val 0 1)))
                    (- high low))
                (b* (((mv low high) (acl2::ilog2-search-down val -1 0)))
                  (- high low)))))
    ///
    (defthm ilog2-safe-clock-implies
      (implies (<= (ilog2-safe-clock val) clk)
               (and (< (acl2::Rational-exponent val) clk)
                    (< (- (acl2::rational-exponent val)) clk)
                    (implies (<= 1 val)
                             (< (b* (((mv low high) (acl2::ilog2-search-up val 0 1)))
                                  (+ (- low) high))
                                clk))
                    (implies (< val 1)
                             (< (b* (((mv low high) (acl2::ilog2-search-down val -1 0)))
                                  (+ (- low) high))
                                clk))))))
         
  
  (defthm ilog2-correct
    (implies (and (subprograms-match '("Abs" "ILog2")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (rationalp val)
                  (< 0 val)
                  (integerp clk)
                  (<= (ilog2-safe-clock val) clk)
                  (< (stack_size-lookup "Abs" (global-env->stack_size (env->global env)))
                     (expt 2 40))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (eval_subprogram env "ILog2" nil (list (v_real val)) :clk clk)
                    (ev_normal (func_result (list (v_int (acl2::ilog2 val))) (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram  env "ILog2" nil (list (v_real val)) :clk clk))
             :in-theory (enable (stdlib-static-env)
                                check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                acl2::ilog2)
             :do-not-induct t))))

