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
(include-book "ilog2")
(include-book "misc")
(include-book "centaur/bitops/rational-exponent" :dir :system)
(local (include-book "ast-theory"))

(local (in-theory (disable (tau-system))))

(local (in-theory (disable floor mod expt
                           put-assoc-equal
                           hons-assoc-equal)))





(local
 (encapsulate nil
   (local (include-book "centaur/misc/multiply-out" :dir :system))
   (defthmd floor-in-terms-of-*-2
     (implies (and (rationalp x)
                   (posp y))
              (equal (floor x y)
                     (+ (if (<= (+ y (* 2 y (floor x (* 2 y)))) x) 1 0)
                        (* 2 (floor x (* 2 y))))))
     :hints (("goal" :use ((:instance acl2::floor-bounded-by-/ (x x) (y y))
                           (:instance acl2::floor-bounded-by-/ (x x) (y (* 2 y))))
              :in-theory (e/d (acl2::multiply-out-<
                               acl2::multiply-out-equal)
                              (acl2::floor-bounded-by-/))
              :do-not '(eliminate-destructors
                        fertilize))
             (and stable-under-simplificationp
                  '(:nonlinearp t)))
     :rule-classes ((:definition :controller-alist ((floor nil t))
                     :install-body nil))
     :otf-flg t)))




(defsection roundtowardszero-loop
  
  (defconst *roundtowardszero-loop*
    (find-nth-form 0 :s_for (assoc-equal "RoundTowardsZero" (static_env_global->subprograms
                                                 (stdlib-static-env)))))

  (defconst *roundtowardszero-loop-body*
    (s_for->body *roundtowardszero-loop*))

  (local (defund same (x y)
           (equal x y)))
  
  (local (defthm acc-equal-to-same
           (b* ((storage (local-env->storage
                          (env->local env)))
                (acc-look (hons-assoc-equal "__stdlib_local_acc" storage))
                (acc (cdr acc-look))
                ((v_int acc)))
             (equal (equal acc.val (* 2 (expt 2 x) y))
                    (same  acc.val (* 2 (expt 2 x) y))))
           :hints(("Goal" :in-theory (enable same)))))

  (local (defthm acc-when-same
           (b* ((storage (local-env->storage
                          (env->local env)))
                (acc-look (hons-assoc-equal "__stdlib_local_acc" storage))
                (acc (cdr acc-look))
                ((v_int acc)))
             (implies (same  acc.val (* 2 (expt 2 x) y))
                      (equal acc.val (* 2 (expt 2 x) y))))
           :hints(("Goal" :in-theory (e/d (same)
                                          (acc-equal-to-same))))))
           

  (local (in-theory (disable default-*-2 default-*-1 default-+-2 default-+-1
                             acl2::hons-assoc-equal-when-atom
                             acl2::expt-with-violated-guards
                             acl2::floor-=-x/y
                             acl2::floor-type-3
                             acl2::mod-minus
                             default-cdr
                             acl2::floor-type-4
                             acl2::floor-type-1
                             not)))

  (local (defthm v_int->val-equal-quote
           (implies (and (syntaxp (quotep v))
                         (val-case x :v_int)
                         (val-p x))
                    (equal (equal (v_int->val x) v)
                           (and (integerp v)
                                (equal x (v_int v)))))))
  
  (defthm roundtowardszero-loop-correct
    (b* ((storage (local-env->storage
                   (env->local env)))
         (i-look (assoc-equal "__stdlib_local_i" storage))
         (i (cdr i-look))
         ((v_int i))
         (acc-look (assoc-equal "__stdlib_local_acc" storage))
         (acc (cdr acc-look))
         ((v_int acc))
         (x_pos-look (assoc-equal "__stdlib_local_x_pos" storage))
         (x_pos (cdr x_pos-look))
         ((v_real x_pos))
         (next-look (assoc-equal "__stdlib_local_next" storage)))
      (implies (and (subprograms-match '("Real")
                                       (global-env->static (env->global env))
                                       (stdlib-static-env))
                    i-look
                    (val-case i :v_int)
                    (equal i.val start)
                    acc-look
                    (val-case acc :v_int)
                    x_pos-look
                    (val-case x_pos :v_real)
                    (<= 1 x_pos.val)
                    (not next-look)
                    (equal acc.val (* (expt 2 (+ 1 start))
                                      (floor x_pos.val (expt 2 (+ 1 start)))))
                    (posp clk)
                    (integerp start)
                    (<= -1 start)
                    (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                             (env->global env))))
                    (no-duplicatesp-equal (acl2::alist-keys storage)))
               (b* (((mv (ev_normal res) &) (eval_for env "__stdlib_local_i" nil start :down 0 *roundtowardszero-loop-body*))
                    ((continuing res.res))
                    (acc-spec (floor x_pos.val 1))
                    ((env env))
                    ((local-env env.local)))
                 (and (equal (eval_result-kind res) :ev_normal)
                      (equal (control_flow_state-kind res.res) :continuing)
                      (equal res.res.env
                             (change-env env
                                         :local (change-local-env
                                                 env.local
                                                 :storage (put-assoc-equal "__stdlib_local_i"
                                                                           (v_int -1)
                                                                           (put-assoc-equal "__stdlib_local_acc"
                                                                                            (v_int acc-spec)
                                                                                            env.local.storage)))))))))
    :hints (("goal" :induct (for-induct env "__stdlib_local_i" start :down 0 *roundtowardszero-loop-body* clk nil orac)
             :in-theory (enable check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                eval_for_step
                                for_loop-step
                                FOR_LOOP-TEST
                                pop_scope
                                check-bad-slices
                                slices_sub)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((:free (clk)
                             (eval_for env "__stdlib_local_i"
                                       nil
                                       (V_INT->VAL
                                        (CDR (HONS-ASSOC-EQUAL "__stdlib_local_i"
                                                               (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))
                                       :down 0 *roundtowardszero-loop-body*))
                            (:free (clk) (eval_for env "__stdlib_local_i" nil -1 :down 0 *roundtowardszero-loop-body*))
                            (:free (clk) (eval_for env "__stdlib_local_i" nil 0 :down 0 *roundtowardszero-loop-body*))
                            (:with floor-in-terms-of-*-2
                             (:free (x i) (floor (v_real->val x) (expt 2 (v_int->val i)))))))))))



(defsection roundtowardszero-correct

  (local (in-theory (disable acl2::ilog2-is-ilog2-spec)))
  (local (defthm ilog2-is-rational-exponent
         (implies (and (rationalp x)
                       (< 0 x))
                  (equal (acl2::ilog2 x)
                         (acl2::rational-exponent x)))
         :hints (("goal" :use ((:instance acl2::rational-exponent-unique
                                (n (acl2::ilog2 x)))
                               (:instance acl2::ilog2-correct (value x)))
                  :in-theory (disable acl2::exponents-add expt)))))

  (local (defthm rational-exponent-nonneg
           (implies (and (rationalp val)
                         (<= 1 (abs val)))
                    (<= 0 (acl2::rational-exponent val)))
           :hints (("goal" :use ((:instance acl2::rational-exponent-gte-power-of-2
                                  (n 0) (x val)))))
           :rule-classes :linear))

  (local (defthm floor-of-rational-exponent
           (implies (and (rationalp val)
                         (< 0 val))
                    (equal (floor val (expt 2 (acl2::rational-exponent val)))
                           1))
           :hints (("goal" 
                    :in-theory (enable acl2::rational-exponent-in-terms-of-rational-significand-abs))
                   )))

  (local (in-theory (disable acl2::floor-minus)))
  
  (local (defthm floor-neg-of-rational-exponent
           (implies (and (rationalp val)
                         (< val 0))
                    (equal (floor (- val) (expt 2 (acl2::rational-exponent val)))
                           1))
           :hints (("goal" 
                    :in-theory (enable acl2::rational-exponent-in-terms-of-rational-significand-abs))
                   )))
  
  
  (defthm roundtowardszero-correct
    (implies (and (subprograms-match '("Real" "RoundTowardsZero" "Abs" "ILog2")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (rationalp val)
                  (integerp clk)
                  (< (ilog2-safe-clock (abs val)) clk)
                  (<= (ilog2-safe-clock (abs val)) (expt 2 128))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "RoundTowardsZero" nil (list (v_real val)) :clk clk))
                    (ev_normal (func_result (list (v_int (truncate val 1))) (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram  env "RoundTowardsZero" nil (list (v_real val)) :clk clk))
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int)
                             (truncate))
             :do-not-induct t))))


(defsection roundup-correct

  
  (defthm roundup-correct
    (implies (and (subprograms-match '("Real" "RoundUp" "Abs" "ILog2" "RoundTowardsZero")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (rationalp val)
                  (< 0 val)
                  (integerp clk)
                  (< (+ 1 (ilog2-safe-clock (abs val))) clk)
                  (<= (ilog2-safe-clock (abs val)) (expt 2 128))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "RoundUp" nil (list (v_real val)) :clk clk))
                    (ev_normal (func_result (list (v_int (ceiling val 1))) (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram  env "RoundUp" nil (list (v_real val)) :clk clk))
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int)
                             (truncate))
             :do-not-induct t))))


(defsection rounddown-correct

  
  (defthm rounddown-correct
    (implies (and (subprograms-match '("Real" "RoundDown" "Abs" "ILog2" "RoundTowardsZero")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (rationalp val)
                  (< 0 val)
                  (integerp clk)
                  (< (+ 1 (ilog2-safe-clock (abs val))) clk)
                  (<= (ilog2-safe-clock (abs val)) (expt 2 128))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "RoundDown" nil (list (v_real val)) :clk clk))
                    (ev_normal (func_result (list (v_int (floor val 1))) (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram  env "RoundDown" nil (list (v_real val)) :clk clk))
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int)
                             (truncate))
             :do-not-induct t))))

