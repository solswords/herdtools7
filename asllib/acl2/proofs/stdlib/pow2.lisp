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



(defloop floorpow2-loop
  :function "FloorPow2"
  :looptype :s_while
  :local-vars (((v_int x) "__stdlib_local_x")
               ((v_int p2) "__stdlib_local_p2"
                (v_int (acl2::floor-pow-2-loop x.val p2.val))))
  :invariants (and (< 0 x.val)
                   (<= 2 p2.val)
                   (<= p2.val (* 2 x.val))
                   (< (- (+ 1 (acl2::rational-exponent x.val))
                         (acl2::rational-exponent p2.val))
                      (ifix clk))
                   (integerp limit)
                   (< (- (+ 1 (acl2::rational-exponent x.val))
                         (acl2::rational-exponent p2.val))
                      limit))
  :hints ((and stable-under-simplificationp
               '(:expand ((:free (x) (acl2::floor-pow-2-loop
                                      x
                                      (v_int->val (cdr (hons-assoc-equal "__stdlib_local_p2"
                                                                         (local-env->storage
                                                                          (env->local env)))))))))))
  :prepwork
  ((local (defthm rational-exponent-plus1-by-compare
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
            :rule-classes :linear))))


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


