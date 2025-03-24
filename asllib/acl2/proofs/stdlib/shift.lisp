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
(include-book "bits")
(include-book "centaur/bitops/rotate" :dir :system)
(local (include-book "ast-theory"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))

(local (in-theory (disable (tau-system))))

(local (in-theory (disable floor mod expt
                           put-assoc-equal
                           hons-assoc-equal
                           unsigned-byte-p
                           logmask)))





;; LSL
;; LSL_C
;; LSR
;; LSR_C
;; ASR
;; ASR_C
;; ROR
;; ROR_C

(local (defthm nfix-when-not-negp
         (implies (not (negp x))
                  (equal (nfix x) (ifix x)))
         :hints(("Goal" :in-theory (enable nfix ifix)))))



(local (defthm loghead-when-zp
         (implies (zp n)
                  (equal (loghead n x) 0))
         :hints(("Goal" :in-theory (enable bitops::loghead**)))))

(defsection LSL-correct
  
  (defthm LSL-correct
    (implies (and (subprograms-match '("LSL" "Zeros-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (<= 0 (ifix n))
                  (posp clk)
                  (<= 0 (ifix shift))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "LSL"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
                    (ev_normal (func_result (list (v_bitvector n (loghead n (ash (nfix x) shift))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "LSL"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
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
                                v_to_int
                                slices_sub
                                check-bad-slices
                                bitops::loghead-of-ash))
             :do-not-induct t))))

(defsection LSL_C-correct
  
  (defthm LSL_C-correct
    (implies (and (subprograms-match '("LSL_C" "LSL" "Zeros-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (<= 0 (ifix n))
                  (<= 2 (nfix clk))
                  (posp shift)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "LSL_C"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
                    (ev_normal (func_result (list (v_bitvector n (loghead n (ash (nfix x) shift)))
                                                  (v_bitvector 1 (logbit n (ash (nfix x) shift))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "LSL_C"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
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
                                v_to_int
                                slices_sub
                                check-bad-slices
                                bitops::loghead-of-ash))
             :do-not-induct t))))


(defsection LSR-correct
  
  (defthm LSR-correct
    (implies (and (subprograms-match '("LSR" "Zeros-1" "ZeroExtend-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (natp n)
                  (<= 2 (nfix clk))
                  (<= 0 (ifix shift))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "LSR"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
                    (ev_normal (func_result (list (v_bitvector n (ash (loghead n (nfix x)) (- shift))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "LSR"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
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
                                v_to_int
                                slices_sub
                                check-bad-slices
                                bitops::loghead-of-loghead-split))
             :do-not-induct t))))


(defsection LSR_C-correct
  
  (defthm LSR_C-correct
    (implies (and (subprograms-match '("LSR_C" "LSR" "Zeros-1" "ZeroExtend-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (natp n)
                  (<= 3 (nfix clk))
                  (posp shift)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "LSR_C"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
                    (ev_normal (func_result (list (v_bitvector n (logtail shift (loghead n (nfix x))))
                                                  (v_bitvector 1 (logbit (1- shift) (loghead n (nfix x)))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "LSR_C"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
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
                                v_to_int
                                slices_sub
                                check-bad-slices
                                bitops::loghead-of-ash))
             :do-not-induct t))))



(defsection ASR-correct
  
  (defthm ASR-correct
    (implies (and (subprograms-match '("ASR" "Min-1" "SignExtend-1" "Replicate-1" "Zeros-1" "Ones-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (posp n)
                  (<= 4 (nfix clk))
                  (<= 0 (ifix shift))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "ASR"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
                    (ev_normal (func_result (list (v_bitvector n (loghead n (logtail shift (logext n (nfix x))))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "ASR"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
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
                                v_to_int
                                slices_sub
                                check-bad-slices
                                bitops::loghead-of-loghead-split
                                logext
                                bitops::logtail-of-logapp-split))
             :do-not-induct t))))

(defsection ASR_C-correct
  
  (defthm ASR_C-correct
    (implies (and (subprograms-match '("ASR_C" "ASR" "Min-1" "SignExtend-1" "Replicate-1" "Zeros-1" "Ones-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (posp n)
                  (<= 5 (nfix clk))
                  (posp shift)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "ASR_C"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
                    (ev_normal (func_result (list (v_bitvector n (loghead n (logtail shift (logext n (nfix x)))))
                                                  (v_bitvector 1 (logbit (1- shift) (logext n (nfix x)))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "ASR_C"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
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
                                v_to_int
                                slices_sub
                                check-bad-slices
                                bitops::loghead-of-ash))
             :do-not-induct t))))



(defsection ROR-correct

  (local (defthm logand-with-ash-minus-1
           (implies (not (negp n))
                    (equal (logand x (+ -1 (ash 1 n)))
                           (loghead n x)))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-inductions
                                                    bitops::ihsext-recursive-redefs
                                                    bitops::equal-logcons-strong)))))

    
  
  (local (defthm logior-loghead-ash
           (implies (not (negp w))
                    (equal (logior (ash x w)
                                   (loghead w y))
                           (logapp w y x)))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-inductions
                                                    bitops::ihsext-recursive-redefs
                                                    bitops::equal-logcons-strong)))))
  (local (defthm rotate-right-in-terms-of-logapp
           (implies (posp n)
                    (equal (rotate-right x n shift)
                           (b* ((shift-mod-n (mod (nfix shift) n)))
                             (logapp (- n shift-mod-n)
                                     (logtail shift-mod-n x)
                                     (loghead shift-mod-n x)))))
           :hints(("Goal" :in-theory (enable rotate-right)))))
  
  (defthm ROR-correct
    (implies (and (subprograms-match '("ROR")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (posp n)
                  (<= 0 (ifix shift))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "ROR"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
                    (ev_normal (func_result (list (v_bitvector n (bitops::rotate-right (loghead n (nfix x))
                                                                                       n shift)))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "ROR"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
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
                                v_to_int
                                slices_sub
                                check-bad-slices
                                bitops::loghead-of-loghead-split
                                logext
                                bitops::logtail-of-logapp-split))
             :do-not-induct t))))

(defsection ROR_C-correct
  
  (defthm ROR_C-correct
    (implies (and (subprograms-match '("ROR_C" "ROR")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (posp n)
                  (posp clk)
                  (posp shift)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "ROR_C"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
                    (ev_normal (func_result (list (v_bitvector n (bitops::rotate-right (loghead n (nfix x))
                                                                                       n shift))
                                                  (v_bitvector 1 (logbit (mod (1- shift) n)
                                                                         (nfix x))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "ROR_C"
                                               (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int shift))
                                               :clk clk))
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
                                v_to_int
                                slices_sub
                                check-bad-slices
                                bitops::loghead-of-ash))
             :do-not-induct t))))

