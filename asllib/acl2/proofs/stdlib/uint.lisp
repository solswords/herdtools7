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
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))


(local (in-theory (disable (tau-system)
                           hons-assoc-equal
                           put-assoc-equal
                           floor mod
                           bitops::part-select)))


(defloop uint-loop
  :function "UInt"
  :looptype :s_for
  :local-vars (((v_bitvector x) "__stdlib_local_x")
               ((v_int n) "__stdlib_local_N")
               ((v_int result) "__stdlib_local_result"
                (v_int (+ result.val (ash (bitops::part-select x.val :low start :high end) start)))))
  :index-var i
  :invariants (and (<= 0 start)
                   (<= (+ 1 end) x.len))
  :prepwork
  ((local (defthm ash-of-partselect-plus-one
            (implies (natp start)
                     (equal (ash (bitops::part-select-width-low val width (+ 1 start)) (+ 1 start))
                            (- (ash (bitops::part-select-width-low val (+ 1 (nfix width)) start) start)
                               (* (logbit start val) (expt 2 start)))))
            :hints(("Goal" :in-theory (enable bitops::ash-is-expt-*-x
                                              bitops::part-select-width-low
                                              logcons)
                    :expand ((logtail (+ 1 start) val)
                             (:free (x) (loghead (+ 1 (nfix width)) x)))))))
  
   (local (defthm loghead-of-part-select
            (implies (<= (nfix n) (nfix width))
                     (equal (loghead n (bitops::part-select-width-low val width low))
                            (loghead n (logtail low val))))
            :hints(("Goal" :in-theory (enable bitops::part-select-width-low)))))


   (local (defthm part-select-0-width
            (equal (bitops::part-select-width-low val 0 low) 0)
            :hints(("Goal" :in-theory (enable bitops::part-select-width-low)))))))





(defsection uint-correct

  (local (defthm nfix-when-not-negp
           (implies (not (negp n))
                    (equal (nfix n) (ifix n)))
           :hints(("Goal" :in-theory (enable nfix)))))

  (local (defthm expt-when-not-negp
           (implies (not (negp n))
                    (posp (expt 2 n)))
           :hints(("Goal" :in-theory (enable expt)))
           :rule-classes :type-prescription))
  
  (defthm uint-correct
    (implies (and (subprograms-match '("UInt")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (<= 0 (ifix n))
                  (natp clk))
             (equal (mv-nth 0 (eval_subprogram env "UInt"
                                               (list (v_int n))
                                               (list (v_bitvector n val))
                                               :clk clk))
                    (ev_normal (func_result (list (v_int (loghead n (nfix val)))) (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "UInt"
                                              (list (v_int n))
                                              (list (v_bitvector n val))
                                              :clk clk))
             :in-theory (enable bitops::part-select-width-low
                                check_recurse_limit
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
             :do-not-induct t))))


