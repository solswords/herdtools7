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

(defthm abs-correct
  (implies (subprograms-match '("Abs") 
                              (global-env->static (env->global env))
                              (stdlib-static-env))
           (equal (mv-nth 0 (eval_subprogram env "Abs" nil (list (v_real val)) :clk clk))
                  (ev_normal (func_result (list (v_real (abs val))) (env->global env)))))
  :hints (("goal" :expand ((eval_subprogram  env "Abs" nil (list (v_real val)) :clk clk))
           :in-theory (enable (stdlib-static-env)
                              check_recurse_limit
                              declare_local_identifiers
                              env-find))))
