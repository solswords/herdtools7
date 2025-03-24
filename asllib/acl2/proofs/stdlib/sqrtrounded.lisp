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

(include-book "ilog2")
(include-book "sqrtrounded-alg")
(local (include-book "ast-theory"))
(local (include-book "std/lists/no-duplicatesp" :dir :system))
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (in-theory (disable (tau-system)
                           hons-assoc-equal
                           put-assoc-equal
                           floor mod expt
                           no-duplicatesp-equal
                           member-equal)))



(defloop sqrtrounded-loop
  :function "SqrtRounded"
  :looptype :s_for
  :local-vars (((v_real mant) "__stdlib_local_mant")
               ((v_real prec) "__stdlib_local_prec" (v_real prec-spec))
               ((v_real root) "__stdlib_local_root" (v_real root-spec)))
  :bindings (((mv root-spec prec-spec)
              (acl2::sqrtrounded-loop mant.val root.val prec.val start (+ 1 end))))
  :index-var n
  :hints ((and stable-under-simplificationp
               '(:expand ((:free (start)
                           (ACL2::SQRTROUNDED-LOOP
                            (V_REAL->VAL
                             (CDR (HONS-ASSOC-EQUAL "__stdlib_local_mant"
                                                    (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))
                            (V_REAL->VAL
                             (CDR (HONS-ASSOC-EQUAL "__stdlib_local_root"
                                                    (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))
                            (V_REAL->VAL
                             (CDR (HONS-ASSOC-EQUAL "__stdlib_local_prec"
                                                    (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))
                            start
                            (+ 1 END))))))))


(defsection sqrtrounded-correct


  (define sqrtrounded-safe-clock ((val rationalp))
    :guard (< 0 val)
    :returns (clock posp :rule-classes :type-prescription)
    (+ 1 (ilog2-safe-clock val))
    ///
    (defthm sqrtrounded-safe-clock-linear
      (< (ilog2-safe-clock val) (sqrtrounded-safe-clock val))
      :rule-classes :linear))

  (local (in-theory (disable acl2::ilog2-is-ilog2-spec)))
  
  (local (defthm integerp-of-plus-half
           (implies (and (integerp x)
                         (not (integerp (* 1/2 x))))
                    (integerp (+ -1/2 (* 1/2 x))))
           :hints (("goal" :use ((:instance acl2::mod-=-0
                                  (x x) (y 2))
                                 (:instance acl2::mod-=-0
                                  (x (- x 1)) (y 2)))
                    :in-theory (disable acl2::mod-=-0)))))

  (defthm sqrtrounded-correct
    (implies (and (subprograms-match '("Abs" "SqrtRounded" "ILog2" "Real" "Log2")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (rationalp val)
                  (< 0 val)
                  (posp fracbits)
                  (integerp clk)
                  (<= (sqrtrounded-safe-clock val) clk)
                  (<= (sqrtrounded-safe-clock val) (expt 2 128))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "SqrtRounded" nil (list (v_real val)
                                                                           (v_int fracbits)) :clk clk))
                    (ev_normal (func_result (list (v_real (acl2::sqrtrounded val fracbits))) (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram  env "SqrtRounded" nil (list (v_real val)
                                                                           (v_int fracbits)) :clk clk))
             :in-theory (enable check_recurse_limit
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
                                acl2::sqrtrounded)
             :do-not-induct t))))


