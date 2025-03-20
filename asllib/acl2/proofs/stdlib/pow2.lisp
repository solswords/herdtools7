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

(include-book "../../openers")
(include-book "stdlib")
(include-book "utils")
(include-book "centaur/bitops/rational-exponent" :dir :system)
(include-book "pow2-alg")
(local (include-book "ast-theory"))

(local (in-theory (disable (tau-system))))

(local (in-theory (disable floor mod
                           put-assoc-equal
                           hons-assoc-equal)))


(defsection floorpow2-loop

  (defconst *floorpow2-loop*
    (find-nth-form 0 :s_while (assoc-equal "FloorPow2" (static_env_global->subprograms
                                                        (stdlib-static-env)))))

  (defconst *floorpow2-loop-test*
    (s_while->test *floorpow2-loop*))

  (defconst *floorpow2-loop-body*
    (s_while->body *floorpow2-loop*))


  (local (defthm rational-exponent-plus1-by-compare
           (implies (and (<= p2 (* 2 x))
                         (equal p2 (expt 2 p2e))
                         (< x p2)
                         (rationalp x))
                    (equal (acl2::rational-exponent x)
                           (+ -1 (ifix p2e))))
           :hints (("goal" :use ((:instance acl2::rational-exponent-less-than-power-of-2
                                  (n (ifix p2e)) (x x))
                                 (:instance acl2::rational-exponent-gte-power-of-2
                                  (n (1- (ifix p2e))) (x x)))
                    :do-not-induct t
                    :in-theory (e/d (acl2::exponents-add-unrestricted)
                                    (acl2::rational-exponent-gte-power-of-2
                                     acl2::rational-exponent-less-than-power-of-2))))))

  (local (in-theory (disable not expt)))

  (local (defthm my-rational-exponent-monotonic
           (implies (and (<= x y)
                         (rationalp x)
                         (rationalp y)
                         (< 0 x))
                    (<= (acl2::rational-exponent x) (acl2::rational-exponent y)))
           :hints (("goal" :use ((:instance acl2::rational-exponent-monotonic (x x) (y y)))))
           :rule-classes :linear))
           
  
  (defthm floorpow2-loop-correct
    (b* ((storage (local-env->storage
                   (env->local env)))
         (x-look (assoc-equal "__stdlib_local_x" storage))
         (x (cdr x-look))
         ((v_int x))
         (p2-look (assoc-equal "__stdlib_local_p2" storage))
         (p2 (cdr p2-look))
         ((v_int p2)))
      (implies (and x-look
                    (val-case x :v_int)
                    p2-look
                    (val-case p2 :v_int)
                    (< 0 x.val)
                    (<= 2 p2.val)
                    (<= p2.val (* 2 x.val))
                    ;; (equal p2.val (expt 2 (acl2::rational-exponent p2.val)))
                    (natp clk)
                    (< (- (+ 1 (acl2::rational-exponent x.val))
                          (acl2::rational-exponent p2.val))
                       clk)
                    (integerp limit)
                    (< (- (+ 1 (acl2::rational-exponent x.val))
                          (acl2::rational-exponent p2.val)) limit)
                    (no-duplicatesp-equal (acl2::alist-keys storage)))
               (b* (((mv (ev_normal res) &) (eval_loop env t limit *floorpow2-loop-test* *floorpow2-loop-body*))
                    ((continuing res.res))
                    (p2-spec ;; (expt 2 (+ 1 (acl2::rational-exponent x.val)))
                     (acl2::floor-pow-2-loop x.val p2.val))
                    ((env env))
                    ((local-env env.local)))
                 (and (equal (eval_result-kind res) :ev_normal)
                      (equal (control_flow_state-kind res.res) :continuing)
                      (equal res.res.env
                             (change-env env
                                         :local (change-local-env
                                                 env.local
                                                 :storage (put-assoc-equal "__stdlib_local_p2"
                                                                           (v_int p2-spec)
                                                                           env.local.storage))))))))
    :hints (("goal" :induct (loop-induct env clk *floorpow2-loop-test* *floorpow2-loop-body* t limit orac)
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
                                tick_loop_limit
                                v_to_bool)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((eval_loop env t limit *floorpow2-loop-test* *floorpow2-loop-body*)
                            (:free (x) (acl2::floor-pow-2-loop x
                                                        (v_int->val (cdr (hons-assoc-equal "__stdlib_local_p2"
                                                                                           (local-env->storage
                                                                                            (env->local env)))))))))))))


(defsection floorpow2-correct

  (local (defthm rational-exponent-type-when-posp
           (implies (posp x)
                    (natp (acl2::rational-exponent x)))
           :hints(("Goal" :in-theory (enable acl2::rational-exponent-induct
                                             acl2::rational-exponent-recursive)))
           :rule-classes :type-prescription))
  
  (defthm floorpow2-correct
    (implies (and (subprograms-match '("FloorPow2")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (posp x)
                  (integerp clk)
                  (< (acl2::rational-exponent x) clk)
                  (< (acl2::rational-exponent x) (expt 2 128))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "FloorPow2" nil (list (v_int x)) :clk clk))
                    (ev_normal (func_result (list (v_int (acl2::floor-pow-2 x))) (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "FloorPow2" nil (list (v_int x)) :clk clk))
             :in-theory (enable check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                acl2::floor-pow-2)
             :do-not-induct t))))



(defsection ceilpow2-correct

  (local (defthm rational-exponent-type-when-posp
           (implies (posp x)
                    (natp (acl2::rational-exponent x)))
           :hints(("Goal" :in-theory (enable acl2::rational-exponent-induct
                                             acl2::rational-exponent-recursive)))
           :rule-classes :type-prescription))
  
  (defthm ceilpow2-correct
    (implies (and (subprograms-match '("CeilPow2" "FloorPow2")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (posp x)
                  (integerp clk)
                  (< (+ 1 (acl2::rational-exponent (1- x))) clk)
                  (< (+ 1 (acl2::rational-exponent (1- x))) (expt 2 128))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "CeilPow2" nil (list (v_int x)) :clk clk))
                    (ev_normal (func_result (list (v_int (acl2::ceil-pow-2 x))) (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "CeilPow2" nil (list (v_int x)) :clk clk))
             :in-theory (enable check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                acl2::ceil-pow-2)
             :do-not-induct t))))


(defsection ispow2-correct

  (local (defthm rational-exponent-type-when-posp
           (implies (posp x)
                    (natp (acl2::rational-exponent x)))
           :hints(("Goal" :in-theory (enable acl2::rational-exponent-induct
                                             acl2::rational-exponent-recursive)))
           :rule-classes :type-prescription))

  (local (defthm rational-exponent-of-xminus1
           (implies (posp x)
                    (<= (acl2::rational-exponent (+ -1 x)) (acl2::rational-exponent x)))
           :hints (("goal" :use ((:instance acl2::rational-exponent-monotonic
                                  (x (1- x)) (y x)))
                    :in-theory (disable acl2::rational-exponent-monotonic)))
           :rule-classes :linear))
  
  (defthm ispow2-correct
    (implies (and (subprograms-match '("IsPow2" "FloorPow2" "CeilPow2")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (integerp x)
                  (integerp clk)
                  (< (+ 2 (acl2::rational-exponent x)) clk)
                  (< (+ 2 (acl2::rational-exponent x)) (expt 2 128))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "IsPow2" nil (list (v_int x)) :clk clk))
                    (ev_normal (func_result (list (v_bool (acl2::is-pow-2 x))) (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "IsPow2" nil (list (v_int x)) :clk clk))
             :in-theory (enable check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                acl2::is-pow-2)
             :do-not-induct t))))


