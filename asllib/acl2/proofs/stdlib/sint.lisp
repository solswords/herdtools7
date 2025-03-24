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

(include-book "uint")
(local (include-book "ast-theory"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))


(local (in-theory (disable (tau-system)
                           hons-assoc-equal
                           put-assoc-equal
                           floor mod
                           bitops::part-select)))




(defsection sint-correct

  (local (defthm loghead-lower-bound-when-logbitp
           (implies (and (logbitp (+ -1 n) val)
                         (posp n))
                    (<= (expt 2 (+ -1 n))
                        (loghead n val)))
           :hints(("Goal" :in-theory (acl2::enable*
                                      bitops::ihsext-inductions
                                      bitops::ihsext-recursive-redefs
                                      logcons)
                   :induct (loghead n val)
                   :expand ((expt 2 n))))
           :rule-classes :linear))

  (local (defthm less-than-of-+bit
           (implies (and (integerp x)
                         (integerp y)
                         (bitp b)
                         (< x y))
                    (< (+ b (* 2 x)) (* 2 y)))))
  
  (local (defthm loghead-upper-bound-when-not-logbitp
           (implies (and (not (logbitp (+ -1 n) val))
                         (posp n))
                    (< (loghead n val)
                       (expt 2 (+ -1 n))))
           :hints(("Goal" :in-theory (acl2::e/d*
                                      (bitops::ihsext-inductions
                                      bitops::ihsext-recursive-redefs
                                      logcons)
                                      (acl2::exponents-add))
                   :induct (loghead n val)
                   :expand ((loghead n val)
                            (expt 2 (+ -1 n))
                            (logbitp (+ -1 n) val))))
           :rule-classes :linear))

  (local (defthm logext-in-terms-of-loghead
           (implies (posp n)
                    (equal (logext n x)
                           (+ (if (logbitp (+ -1 n) x)
                                  (- (expt 2 n))
                                0)
                              (loghead n x))))
           :hints(("Goal" :in-theory (acl2::e/d*
                                      (bitops::ihsext-inductions
                                      bitops::ihsext-recursive-redefs
                                      logcons)
                                      (acl2::exponents-add))
                   :induct (loghead n x)
                   :expand ((loghead n x)
                            (logext n x)
                            (expt 2 n)
                            (logbitp (+ -1 n) x))))))
           
  
  (defthm sint-correct
    (implies (and (subprograms-match '("SInt" "UInt")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (natp val)
                  (posp n)
                  (posp clk))
             (equal (mv-nth 0 (eval_subprogram env "SInt"
                                               (list (v_int n))
                                               (list (v_bitvector n val))
                                               :clk clk))
                    (ev_normal (func_result (list (v_int (logext n (nfix val)))) (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "SInt"
                                              (list (v_int n))
                                              (list (v_bitvector n val))
                                              :clk clk)
                             (expt 2 n))
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
                                v_to_int
                                slices_sub
                                check-bad-slices)
             :do-not-induct t))))


