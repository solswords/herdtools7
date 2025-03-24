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
(include-book "misc")
(include-book "uint")
(local (include-book "ast-theory"))

(local (in-theory (disable (tau-system))))

(local (in-theory (disable floor mod expt ceiling
                           put-assoc-equal
                           hons-assoc-equal)))



(defsection aligndownsize-1-correct

  
  (defthm aligndownsize-1-correct
    (implies (and (subprograms-match '("AlignDownSize-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (<= 0 (ifix x))
                  (< 0 (ifix size))
                  (natp clk)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "AlignDownSize-1" nil (list (v_int x) (v_int size)) :clk clk))
                    (ev_normal (func_result (list (v_int (* size (floor (ifix x) size)))) (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram  env "AlignDownSize-1" nil (list (v_int x) (v_int size)) :clk clk))
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
                                v_to_int))
             :do-not-induct t))))

(local (defthm ceiling-in-terms-of-floor
         (implies (and (<= 0 x)
                       (< 0 size)
                       (rationalp x)
                       (rationalp size))
                  (equal (ceiling x size)
                         (if (integerp (/ x size))
                             (floor x size)
                           (+ 1 (floor x size)))))
         :hints(("Goal" :in-theory (enable floor ceiling)))))


(defsection alignupsize-1-correct

  (local (defthm integerp-recip-when-posp
           (implies (posp x)
                    (equal (integerp (/ x))
                           (equal x 1)))))

  (local (in-theory (disable ceiling)))
  
  
  

  (local (defthm floor-of-x+size-1
           (implies (and (<= 0 x)
                         (< 0 size)
                         (integerp x)
                         (integerp size)
                         (not (integerp (/ x size))))
                    (equal (floor (+ -1 size x) size)
                           (+ 1 (floor x size))))))
  
  (defthm alignupsize-1-correct
    (implies (and (subprograms-match '("AlignUpSize-1" "AlignDownSize-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (<= 0 (ifix x))
                  (< 0 (ifix size))
                  (posp clk)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "AlignUpSize-1" nil (list (v_int x) (v_int size)) :clk clk))
                    (ev_normal (func_result (list (v_int (* size (ceiling (ifix x) size)))) (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram  env "AlignUpSize-1" nil (list (v_int x) (v_int size)) :clk clk))
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
                                v_to_int))
             :do-not-induct t))))


(local (defthm posp-expt
         (implies (not (negp x))
                  (posp (expt 2 x)))
         :hints(("Goal" :in-theory (enable expt)))
         :rule-classes :type-prescription))

(defsection aligndownp2-1-correct



  (defthm aligndownp2-1-correct
    (implies (and (subprograms-match '("AlignDownP2-1" "AlignDownSize-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (<= 0 (ifix x))
                  (<= 0 (ifix p2))
                  (posp clk)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "AlignDownP2-1" nil (list (v_int x) (v_int p2)) :clk clk))
                    (ev_normal (func_result (list (v_int (* (expt 2 (ifix p2))
                                                            (floor (ifix x) (expt 2 (ifix p2))))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram  env "AlignDownP2-1" nil (list (v_int x) (v_int p2)) :clk clk))
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
                                v_to_int))
             :do-not-induct t))))


(defsection alignupp2-1-correct


  (defthm alignupp2-1-correct
    (implies (and (subprograms-match '("AlignUpP2-1" "AlignUpSize-1" "AlignDownSize-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (<= 0 (ifix x))
                  (<= 0 (ifix p2))
                  (integerp clk)
                  (<= 2 clk)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "AlignUpP2-1" nil (list (v_int x) (v_int p2)) :clk clk))
                    (ev_normal (func_result (list (v_int (* (expt 2 (ifix p2))
                                                            (ceiling (ifix x) (expt 2 (ifix p2))))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram  env "AlignUpP2-1" nil (list (v_int x) (v_int p2)) :clk clk))
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
                                v_to_int))
             :do-not-induct t))))


(local (include-book "centaur/bitops/ihsext-basics" :dir :System))



(local (defthm nfix-when-not-negp
         (implies (not (negp x))
                  (equal (nfix x) (ifix x)))
         :hints(("Goal" :in-theory (enable nfix ifix)))))

(local (defthm logtail-natp
         (implies (not (negp x))
                  (natp (logtail n x)))
         :hints(("Goal" :use ((:instance bitops::logtail-natp
                               (n n)
                               (x (ifix x))))))
         :rule-classes :type-prescription))

(defsection aligndown-correct
  
  (defthm aligndown-correct
    (implies (and (subprograms-match '("AlignDown" "Zeros-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (<= 0 (ifix x))
                  (< 0 (ifix y))
                  (<= (ifix y) (nfix n))
                  (posp clk)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "AlignDown" (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int y))
                                               :clk clk))
                    (ev_normal (func_result (list (v_bitvector n (ash (logtail y x) y)))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "AlignDown" (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int y))
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
                              bitops::loghead-of-ash
                              ))
             :do-not-induct t))))

(local
 (defsection loghead-of-plus-loghead
   

  (local (defun loghead-of-plus-loghead-ind (n a b c)
           (if (zp n)
               (list a b c)
             (loghead-of-plus-loghead-ind
              (1- n) (logcdr a) (logcdr b)
              (b-ior (b-and (logcar a) (logcar b))
                     (b-ior (b-and (logcar a) c)
                            (b-and (logcar b) c)))))))
  
  (local (defthm loghead-of-plus-loghead-lemma
           (implies (and (integerp a)
                         (integerp b)
                         (bitp c))
                    (equal (loghead n (+ c a (loghead n b)))
                           (loghead n (+ c a b))))
           :hints (("goal" :in-theory (acl2::enable* bitops::ihsext-recursive-redefs)
                    :induct (loghead-of-plus-loghead-ind n a b c)))))
  
  (defthm loghead-of-plus-loghead
    (implies (and (integerp a)
                  (integerp b))
             (equal (loghead n (+ a (loghead n b)))
                    (loghead n (+ a b))))
    :hints (("goal" :use ((:instance loghead-of-plus-loghead-lemma (c 0))))))))


(defsection alignup-correct
  
  (defthm alignup-correct
    (implies (and (subprograms-match '("AlignUp" "Zeros-1" "IsZero")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (<= 0 (ifix x))
                  (< 0 (ifix y))
                  (<= (ifix y) (nfix n))
                  (integerp clk)
                  (<= 2 clk)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "AlignUp" (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int y))
                                               :clk clk))
                    (ev_normal (func_result (list (v_bitvector n
                                                               (if (equal (loghead y x) 0)
                                                                   x
                                                                 (ash (+ 1 (logtail y x)) y))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "AlignUp" (list (v_int n))
                                              (list (v_bitvector n x)
                                                    (v_int y))
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
                              bitops::loghead-of-ash
                              ))
             :do-not-induct t))))

(defsection aligndownsize-correct

  
  (defthm aligndownsize-correct
    (implies (and (subprograms-match '("AlignDownSize" "AlignDownSize-1" "UInt")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (natp n)
                  (< 0 (ifix size))
                  (<= size (expt 2 n))
                  (posp clk)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "AlignDownSize" (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int size))
                                               :clk clk))
                    (ev_normal (func_result (list (v_bitvector n (* (ifix size)
                                                                    (floor (loghead n (nfix x))
                                                                           (ifix size)))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "AlignDownSize" (list (v_int n))
                                              (list (v_bitvector n x)
                                                    (v_int size))
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
                                slices_sub
                                check-bad-slices
                                v_to_int))
             :do-not-induct t))))


(defsection alignupsize-correct

  
  (defthm alignupsize-correct
    (implies (and (subprograms-match '("AlignUpSize" "AlignUpSize-1" "AlignDownSize-1" "UInt")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (natp n)
                  (< 0 (ifix size))
                  (<= size (expt 2 n))
                  (<= 2 (ifix clk))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "AlignUpSize" (list (v_int n))
                                               (list (v_bitvector n x)
                                                     (v_int size))
                                               :clk clk))
                    (ev_normal (func_result (list (v_bitvector n (* (ifix size)
                                                                    (ceiling (loghead n (nfix x))
                                                                             (ifix size)))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "AlignUpSize" (list (v_int n))
                                              (list (v_bitvector n x)
                                                    (v_int size))
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
                                slices_sub
                                check-bad-slices
                                v_to_int))
             :do-not-induct t))))






(local (defthmd ash-is-expt
         (implies (not (negp n))
                  (equal (ash x n)
                         (* (ifix x) (expt 2 (ifix n)))))
         :hints (("goal" :use ((:instance bitops::ash-is-expt-*-x
                                (n (ifix n)) (x x)))))))



(local (defthm floor-to-logtail
         (implies (and (not (negp n)) (integerp x))
                  (equal (floor x (expt 2 n))
                         (logtail n x)))
         :hints(("Goal" :in-theory (enable logtail)))))

(defsection aligndownp2-correct

  
  (local (defthm loghead-of-expt-product
           (implies (and (integerp i)
                         (not (negp p2))
                         (<= (ifix p2) (nfix n)))
                    (equal (loghead n (* (expt 2 p2) i))
                           (ash (loghead (- (nfix n) (ifix p2)) i) p2)))
           :hints (("goal" :use ((:instance bitops::loghead-of-ash
                                  (n n) (m p2) (x i)))
                    :in-theory (enable ash-is-expt)))))

  (defthm aligndownp2-correct
    (implies (and (subprograms-match '("AlignDownP2" "Zeros-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (< 0 (ifix n))
                  (<= 0 (ifix p2))
                  (<= (ifix p2) (ifix n))
                  (posp clk)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "AlignDownP2" (list (v_int n))
                                               (list (v_bitvector n x) (v_int p2)) :clk clk))
                    (ev_normal (func_result (list (v_bitvector n
                                                               (* (expt 2 (ifix p2))
                                                                  (floor (loghead n (nfix x))
                                                                         (expt 2 (ifix p2))))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "AlignDownP2" (list (v_int n))
                                               (list (v_bitvector n x) (v_int p2)) :clk clk))
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
                                check-bad-slices
                                slices_sub
                                v_to_int))
             :do-not-induct t))))



(defsection alignupp2-correct


  (defthm loghead-of-plus-loghead3
    (implies (and (integerp a)
                  (integerp b)
                  (integerp c))
             (equal (loghead n (+ a b (loghead n c)))
                    (loghead n (+ a b c))))
    :hints (("goal" :use ((:instance loghead-of-plus-loghead
                           (a (+ a b)) (b c))))))

  (local (defun ind (n x y)
           (if (zp n)
               (list x y)
             (ind (1- n) (logcdr x) (logcdr y)))))
  
  (local (defthm logtail-small-when-loghead-0
           (implies (and (equal (loghead n x) 0)
                         (integerp x)
                         (unsigned-byte-p n y))
                    (equal (logtail n (+ x y))
                           (logtail n x)))
           :hints (("goal" :in-theory (bitops::e/d* (bitops::ihsext-recursive-redefs))
                    :induct (ind n x y)))))

  (local (defthm loghead-0-when-integerp-div
           (implies (and (integerp x)
                         (not (negp n)))
                    (equal (integerp (* (/ (expt 2 n)) x))
                           (equal 0 (loghead n x))))
           :hints(("Goal" :in-theory (enable loghead)))))

  (local (defthm logtail-lemma
           (implies (and (equal (loghead n x) 0)
                         (integerp x)
                         (not (negp n)))
                    (equal (logtail n (+ -1 x (expt 2 n)))
                           (logtail n x)))
           :hints (("goal" :use ((:instance logtail-small-when-loghead-0
                                  (y (+ -1 (expt 2 n)))))))))

  (local (defthm logtail-of-plus-ash
           (implies (and (integerp x)
                         (not (negp n)))
                    (equal (logtail n (+ x (ash 1 n)))
                           (+ 1 (logtail n x))))
           :hints (("goal" :in-theory (bitops::e/d* (bitops::ihsext-inductions
                                                     bitops::ihsext-recursive-redefs))
                    :induct (logtail n x)
                    :expand ((:free (x y) (logtail n (+ x y)))))
                   (and stable-under-simplificationp
                        '(:in-theory (enable ash-is-expt))))))
  
  (local (defthm logtail-lemma2-aux
           (implies (and (not (equal (loghead n x) 0))
                         (integerp x)
                         (not (negp n)))
                    (equal (logtail n (+ -1 x (ash 1 n)))
                           (+ 1 (logtail n x))))
           :hints (("goal" :in-theory (bitops::e/d* (bitops::ihsext-inductions
                                                     bitops::ihsext-recursive-redefs))
                    :induct (logtail n x)
                    :expand ((:free (x y) (logtail n (+ x y))))))))

  (local (defthm logtail-lemma2
           (implies (and (not (equal (loghead n x) 0))
                         (integerp x)
                         (not (negp n)))
                    (equal (logtail n (+ -1 x (expt 2 n)))
                           (+ 1 (logtail n x))))
           :hints (("goal" :use ((:instance logtail-lemma2-aux))
                    :in-theory (e/d (ash-is-expt) (logtail-lemma2-aux))))))
  

  (local (defthm loghead-of-plus-mult-expt
           (implies (and (integerp x)
                         (natp n)
                         (not (negp m))
                         (<= (ifix m) n))
                    (equal (loghead n (+ x (* (expt 2 m) (loghead (+ n (- (ifix m))) y))))
                           (loghead n (+ x (* (expt 2 m) (ifix y))))))
           :hints (("goal" :use ((:instance loghead-of-plus-loghead
                                  (a x)
                                  (b (ash y m))))
                    :in-theory (e/d (bitops::loghead-of-ash)
                                    (loghead-of-plus-loghead)))
                   (and stable-under-simplificationp
                        '(:in-theory (enable ash-is-expt))))))

  (local (defthm loghead-of-mult-expt
           (implies (and (integerp x)
                         (natp n)
                         (not (negp m))
                         (<= (ifix m) n))
                    (equal (loghead n (* (expt 2 m) (loghead (+ n (- (ifix m))) y)))
                           (loghead n (* (expt 2 m) (ifix y)))))
           :hints (("goal" :use ((:instance loghead-of-plus-mult-expt
                                  (x 0)))))))
  

  (local (in-theory (disable ceiling)))
  
  (defthm alignupp2-correct
    (implies (and (subprograms-match '("AlignUpP2" "AlignDownP2" "Zeros-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (< 0 (ifix n))
                  (<= 0 (ifix p2))
                  (<= (ifix p2) (ifix n))
                  (<= 2 (ifix clk))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "AlignUpP2" (list (v_int n))
                                               (list (v_bitvector n x) (v_int p2)) :clk clk))
                    (ev_normal (func_result (list (v_bitvector n
                                                               (* (expt 2 (ifix p2))
                                                                  (ceiling (loghead n (nfix x))
                                                                           (expt 2 (ifix p2))))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "AlignUpP2" (list (v_int n))
                                              (list (v_bitvector n x) (v_int p2)) :clk clk))
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
                                check-bad-slices
                                slices_sub
                                v_to_int))
             :do-not-induct t))))



