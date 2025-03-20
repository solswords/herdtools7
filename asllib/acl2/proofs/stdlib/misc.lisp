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
(local (include-book "ast-theory"))

(local (in-theory (disable (tau-system))))

(defthm abs-real-correct
  (implies (subprograms-match '("Abs") 
                              (global-env->static (env->global env))
                              (stdlib-static-env))
           (equal (mv-nth 0 (eval_subprogram env "Abs" nil (list (v_real val)) :clk clk))
                  (ev_normal (func_result (list (v_real (abs val))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram  env "Abs" nil (list (v_real val)) :clk clk))
           :in-theory (enable check_recurse_limit
                              declare_local_identifiers
                              env-find))))

(defthm abs-int-correct
  (implies (subprograms-match '("Abs-1") 
                              (global-env->static (env->global env))
                              (stdlib-static-env))
           (equal (mv-nth 0 (eval_subprogram env "Abs-1" nil (list (v_int val)) :clk clk))
                  (ev_normal (func_result (list (v_int (abs val))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram  env "Abs-1" nil (list (v_int val)) :clk clk))
           :in-theory (enable check_recurse_limit
                              declare_local_identifiers
                              env-find))))

(local (in-theory (disable rfix)))


(defthm min-real-correct
  (implies (subprograms-match '("Min") 
                              (global-env->static (env->global env))
                              (stdlib-static-env))
           (equal (mv-nth 0 (eval_subprogram env "Min" nil (list (v_real a) (v_real b)) :clk clk))
                  (ev_normal (func_result (list (v_real (min (rfix a) (rfix b)))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram  env "Min" nil (list (v_real a) (v_real b)) :clk clk))
           :in-theory (enable check_recurse_limit
                              declare_local_identifiers
                              env-find))))

(defthm min-int-correct
  (implies (subprograms-match '("Min-1") 
                              (global-env->static (env->global env))
                              (stdlib-static-env))
           (equal (mv-nth 0 (eval_subprogram env "Min-1" nil (list (v_int a) (v_int b)) :clk clk))
                  (ev_normal (func_result (list (v_int (min (ifix a) (ifix b)))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram  env "Min-1" nil (list (v_int a) (v_int b)) :clk clk))
           :in-theory (enable check_recurse_limit
                              declare_local_identifiers
                              env-find))))

(defthm max-real-correct
  (implies (subprograms-match '("Max") 
                              (global-env->static (env->global env))
                              (stdlib-static-env))
           (equal (mv-nth 0 (eval_subprogram env "Max" nil (list (v_real a) (v_real b)) :clk clk))
                  (ev_normal (func_result (list (v_real (max (rfix a) (rfix b)))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram  env "Max" nil (list (v_real a) (v_real b)) :clk clk))
           :in-theory (enable check_recurse_limit
                              declare_local_identifiers
                              env-find))))

(defthm max-int-correct
  (implies (subprograms-match '("Max-1") 
                              (global-env->static (env->global env))
                              (stdlib-static-env))
           (equal (mv-nth 0 (eval_subprogram env "Max-1" nil (list (v_int a) (v_int b)) :clk clk))
                  (ev_normal (func_result (list (v_int (max (ifix a) (ifix b)))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram  env "Max-1" nil (list (v_int a) (v_int b)) :clk clk))
           :in-theory (enable check_recurse_limit
                              declare_local_identifiers
                              env-find))))


(defthm iseven-correct
  (implies (subprograms-match '("IsEven") 
                              (global-env->static (env->global env))
                              (stdlib-static-env))
           (equal (mv-nth 0 (eval_subprogram env "IsEven" nil (list (v_int a)) :clk clk))
                  (ev_normal (func_result (list (v_bool (evenp (ifix a)))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram  env "IsEven" nil (list (v_int a)) :clk clk))
           :in-theory (enable check_recurse_limit
                              declare_local_identifiers
                              env-find))))

(defthm isodd-correct
  (implies (subprograms-match '("IsOdd") 
                              (global-env->static (env->global env))
                              (stdlib-static-env))
           (equal (mv-nth 0 (eval_subprogram env "IsOdd" nil (list (v_int a)) :clk clk))
                  (ev_normal (func_result (list (v_bool (oddp (ifix a)))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram  env "IsOdd" nil (list (v_int a)) :clk clk))
           :in-theory (enable check_recurse_limit
                              declare_local_identifiers
                              env-find))))

(defthm real-correct
  (implies (subprograms-match '("Real") 
                              (global-env->static (env->global env))
                              (stdlib-static-env))
           (equal (mv-nth 0 (eval_subprogram env "Real" nil (list (v_int a)) :clk clk))
                  (ev_normal (func_result (list (v_real (ifix a))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram  env "Real" nil (list (v_int a)) :clk clk))
           :in-theory (enable check_recurse_limit
                              declare_local_identifiers
                              env-find))))


(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (defthm nfix-when-not-negp
         (implies (not (negp x))
                  (equal (nfix x) (ifix x)))
         :hints(("Goal" :in-theory (enable nfix ifix)))))

(defthm zeros-1-correct
  (implies (and (subprograms-match '("Zeros-1") 
                                   (global-env->static (env->global env))
                                   (stdlib-static-env))
                (<= 0 (ifix n)))
           (equal (mv-nth 0 (eval_subprogram env "Zeros-1" (list (v_int n)) nil :clk clk))
                  (ev_normal (func_result (list (v_bitvector n 0)) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram env "Zeros-1" (list (v_int n)) nil :clk clk))
           :in-theory (enable check_recurse_limit
                              declare_local_identifiers
                              env-find
                              slices_sub
                              check-bad-slices))))

(defthm zeros-correct
  (implies (and (subprograms-match '("Zeros" "Zeros-1") 
                                   (global-env->static (env->global env))
                                   (stdlib-static-env))
                (natp n)
                (posp clk))
           (equal (mv-nth 0 (eval_subprogram env "Zeros" (list (v_int n)) (list (v_int n)) :clk clk))
                  (ev_normal (func_result (list (v_bitvector n 0)) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram env "Zeros" (list (v_int n)) (list (v_int n)) :clk clk))
           :in-theory (enable check_recurse_limit
                              declare_local_identifiers
                              env-find
                              slices_sub
                              check-bad-slices
                              env-push-stack
                              env-pop-stack))))


(local (in-theory (disable logmask)))

(local (defthm loghead-neg1
         (equal (loghead n -1)
                (logmask n))
         :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-inductions
                                                  bitops::ihsext-recursive-redefs)))))

(defthm ones-1-correct
  (implies (and (subprograms-match '("Ones-1" "Zeros-1") 
                                   (global-env->static (env->global env))
                                   (stdlib-static-env))
                (natp n)
                (posp clk))
           (equal (mv-nth 0 (eval_subprogram env "Ones-1" (list (v_int n)) nil :clk clk))
                  (ev_normal (func_result (list (v_bitvector n (logmask n))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram env "Ones-1" (list (v_int n)) nil :clk clk))
           :in-theory (enable check_recurse_limit
                              declare_local_identifiers
                              env-find
                              slices_sub
                              check-bad-slices
                              env-push-stack
                              env-pop-stack))))

(defthm ones-correct
  (implies (and (subprograms-match '("Ones" "Ones-1" "Zeros-1") 
                                   (global-env->static (env->global env))
                                   (stdlib-static-env))
                (natp n)
                (< 1 (nfix clk)))
           (equal (mv-nth 0 (eval_subprogram env "Ones" (list (v_int n)) (list (v_int n)) :clk clk))
                  (ev_normal (func_result (list (v_bitvector n (logmask n))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram env "Ones" (list (v_int n)) (list (v_int n)) :clk clk))
           :in-theory (enable check_recurse_limit
                              declare_local_identifiers
                              env-find
                              slices_sub
                              check-bad-slices
                              env-push-stack
                              env-pop-stack))))
(defthm replicatebit-1-correct
  (implies (and (subprograms-match '("ReplicateBit-1" "Ones-1" "Zeros-1") 
                                   (global-env->static (env->global env))
                                   (stdlib-static-env))
                (natp n)
                (< 1 (nfix clk)))
           (equal (mv-nth 0 (eval_subprogram env "ReplicateBit-1" (list (v_int n)) (list (v_bool b)) :clk clk))
                  (ev_normal (func_result (list (v_bitvector n (if b 0 (logmask n)))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram env "ReplicateBit-1" (list (v_int n)) (list (v_bool b)) :clk clk))
           :in-theory (enable check_recurse_limit
                              declare_local_identifiers
                              env-find
                              slices_sub
                              check-bad-slices
                              env-push-stack
                              env-pop-stack))))


(defthm replicatebit-correct
  (implies (and (subprograms-match '("ReplicateBit" "ReplicateBit-1" "Ones-1" "Zeros-1") 
                                   (global-env->static (env->global env))
                                   (stdlib-static-env))
                (natp n)
                (< 2 (nfix clk)))
           (equal (mv-nth 0 (eval_subprogram env "ReplicateBit" (list (v_int n)) (list (v_bool b) (v_int n)) :clk clk))
                  (ev_normal (func_result (list (v_bitvector n (if b 0 (logmask n)))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram env "ReplicateBit" (list (v_int n)) (list (v_bool b) (v_int n)) :clk clk))
           :in-theory (e/d (check_recurse_limit
                              declare_local_identifiers
                              env-find
                              slices_sub
                              check-bad-slices
                              env-push-stack
                              env-pop-stack)
                           ((v_bool))))))

(defthm len-correct
  (implies (and (subprograms-match '("Len") 
                                   (global-env->static (env->global env))
                                   (stdlib-static-env))
                (natp n))
           (equal (mv-nth 0 (eval_subprogram env "Len" (list (v_int n)) (list (v_bitvector n v)) :clk clk))
                  (ev_normal (func_result (list (v_int n)) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram env "Len" (list (v_int n)) (list (v_bitvector n v)) :clk clk))
           :in-theory (e/d (check_recurse_limit
                              declare_local_identifiers
                              env-find
                              slices_sub
                              check-bad-slices
                              env-push-stack
                              env-pop-stack)))))


(defthm iszero-correct
  (implies (and (subprograms-match '("IsZero" "Zeros-1")
                                   (global-env->static (env->global env))
                                   (stdlib-static-env))
                (natp n)
                (posp clk))
           (equal (mv-nth 0 (eval_subprogram env "IsZero" (list (v_int n)) (list (v_bitvector n v)) :clk clk))
                  (ev_normal (func_result (list (v_bool (equal (loghead n (nfix v)) 0))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram env "IsZero" (list (v_int n)) (list (v_bitvector n v)) :clk clk))
           :in-theory (e/d (check_recurse_limit
                              declare_local_identifiers
                              env-find
                              slices_sub
                              check-bad-slices
                              env-push-stack
                              env-pop-stack)))))

(defthm isones-correct
  (implies (and (subprograms-match '("IsOnes" "Ones-1" "Zeros-1")
                                   (global-env->static (env->global env))
                                   (stdlib-static-env))
                (natp n)
                (< 1 (nfix clk)))
           (equal (mv-nth 0 (eval_subprogram env "IsOnes" (list (v_int n)) (list (v_bitvector n v)) :clk clk))
                  (ev_normal (func_result (list (v_bool (equal (loghead n (nfix v)) (logmask n)))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram env "IsOnes" (list (v_int n)) (list (v_bitvector n v)) :clk clk))
           :in-theory (e/d (check_recurse_limit
                              declare_local_identifiers
                              env-find
                              slices_sub
                              check-bad-slices
                              env-push-stack
                              env-pop-stack)))))


(defthm zeroextend-1-correct
  (implies (and (subprograms-match '("ZeroExtend-1" "Zeros-1")
                                   (global-env->static (env->global env))
                                   (stdlib-static-env))
                (natp m)
                (integerp n)
                (<= m n)
                (posp clk))
           (equal (mv-nth 0 (eval_subprogram env "ZeroExtend-1" (list (v_int n) (v_int m)) (list (v_bitvector m v)) :clk clk))
                  (ev_normal (func_result (list (v_bitvector n (loghead m (nfix v)))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram env "ZeroExtend-1" (list (v_int n) (v_int m)) (list (v_bitvector m v)) :clk clk))
           :in-theory (e/d (check_recurse_limit
                              declare_local_identifiers
                              env-find
                              slices_sub
                              check-bad-slices
                              env-push-stack
                              env-pop-stack)))))

(defthm zeroextend-correct
  (implies (and (subprograms-match '("ZeroExtend" "ZeroExtend-1" "Zeros-1")
                                   (global-env->static (env->global env))
                                   (stdlib-static-env))
                (natp m)
                (integerp n)
                (<= m n)
                (< 1 (nfix clk)))
           (equal (mv-nth 0 (eval_subprogram env "ZeroExtend" (list (v_int n) (v_int m)) (list (v_bitvector m v) (v_int n)) :clk clk))
                  (ev_normal (func_result (list (v_bitvector n (loghead m (nfix v)))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram env "ZeroExtend" (list (v_int n) (v_int m)) (list (v_bitvector m v) (v_int n)) :clk clk))
           :in-theory (e/d (check_recurse_limit
                              declare_local_identifiers
                              env-find
                              slices_sub
                              check-bad-slices
                              env-push-stack
                              env-pop-stack)))))
