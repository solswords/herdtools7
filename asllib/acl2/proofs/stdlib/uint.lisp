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





(defsection uint-loop

  (local (defthm ash-of-partselect-plus-one
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
           :hints(("Goal" :in-theory (enable bitops::part-select-width-low)))))
  
  (defconst *uint-loop*
    (find-nth-form 0 :s_for (assoc-equal "UInt" (static_env_global->subprograms
                                                 (stdlib-static-env)))))

  (defconst *uint-loop-body*
    (s_for->body *uint-loop*))

  (defthm uint-loop-correct
    (b* ((storage (local-env->storage
                   (env->local env)))
         (i-look (assoc-equal "__stdlib_local_i" storage))
         (i (cdr i-look))
         ((v_int i))
         (x-look (assoc-equal "__stdlib_local_x" storage))
         (x (cdr x-look))
         ((v_bitvector x))
         (N-look (assoc-equal "__stdlib_local_N" storage))
         (N (cdr N-look))
         ((v_int N))
         (result-look (assoc-equal "__stdlib_local_result" storage))
         (result (cdr result-look))
         ((v_int result)))
      (implies (and i-look
                    (val-case i :v_int)
                    (equal i.val start)
                    x-look
                    (val-case x :v_bitvector)
                    N-look
                    (val-case N :v_int)
                    result-look
                    (val-case result :v_int)

                    (natp clk)
                    (natp start)
                    (integerp end)
                    (<= start (+ 1 end))
                    (<= (+ 1 end) x.len)
                    (no-duplicatesp-equal (acl2::alist-keys storage)))
               (b* (((mv (ev_normal res) &) (eval_for env "__stdlib_local_i" nil start :up end *uint-loop-body*))
                    ((continuing res.res))
                    (result-spec (+ result.val (ash (bitops::part-select x.val :low start :high end) start)))
                    ((env env))
                    ((local-env env.local)))
                 (and (equal res.res.env
                             (change-env env
                                         :local (change-local-env
                                                 env.local
                                                 :storage (put-assoc-equal "__stdlib_local_i"
                                                                           (v_int (+ 1 end))
                                                                           (put-assoc-equal "__stdlib_local_result"
                                                                                            (v_int result-spec)
                                                                                            env.local.storage)))))
                      (equal (eval_result-kind res) :ev_normal)
                      (equal (control_flow_state-kind res.res) :continuing)))))
    :hints (("goal" :induct (for-induct env "__stdlib_local_i" start :up end *uint-loop-body* clk nil orac)
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
                 '(:expand ((eval_for env "__stdlib_local_i"
                                      nil
                                      (V_INT->VAL
                                       (CDR (HONS-ASSOC-EQUAL "__stdlib_local_i"
                                                              (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))
                                      :up end *uint-loop-body*)
                            (eval_for env "__stdlib_local_i" nil end :up end *uint-loop-body*)
                            (eval_for env "__stdlib_local_i" nil (+ 1 end) :up end *uint-loop-body*)))))))





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


