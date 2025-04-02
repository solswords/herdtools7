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
(include-book "../../proof-utils")
(include-book "../../shallow")
(local (include-book "ast-theory"))

(local (in-theory (disable (tau-system))))

(local (acl2::add-to-ruleset asl-code-proof-disables abs))

(local (defthm rfix-when-rationalp
         (implies (rationalp x)
                  (equal (rfix x) x))))
(local (in-theory (disable rfix)))



(defthm eval_result-kind-of-if
  (equal (eval_result-kind (if x y z))
         (if x (double-rewrite (eval_result-kind y))
           (double-rewrite (eval_result-kind z)))))

(defthm mv-nth-of-if
  (equal (mv-nth n (if x y z))
         (if x (mv-nth n y) (mv-nth n z))))

(defthm equal-of-if
  (equal (equal (if x y z) a)
         (if x (equal y a) (equal z a))))

(defthm ev_normal->res-of-if
  (equal (ev_normal->res (if x y z))
         (if x (ev_normal->res y)
           (ev_normal->res z))))



(local (defthm posp-ifix-forward
         (implies (posp (ifix x))
                  (equal (ifix x) x))
         :rule-classes ((:forward-chaining :trigger-terms ((ifix x))))))

(local (in-theory (disable unsigned-byte-p)))

(local (defthm unsigned-byte-p-ifix-when-not-negp
         (implies (not (negp n))
                  (unsigned-byte-p (ifix n) 0))
         :hints(("Goal" :in-theory (enable unsigned-byte-p)))))

(local (defthm v_bitvector->val-of-v_bitvector-for-exec
         (equal (v_bitvector->val (v_bitvector n x))
                (loghead* n x))
         :hints(("Goal" :in-theory (enable loghead*)))))


(local (defthm v_bitvector-of-loghead*
         (equal (v_bitvector n (loghead* n x))
                (v_bitvector n x))
         :hints(("Goal" :in-theory (enable loghead*)))))


(local (defthm unsigned-byte-p-width-type-forward
         (implies (unsigned-byte-p n x)
                  (natp n))
         :hints(("Goal" :in-theory (enable unsigned-byte-p)))
         :rule-classes :forward-chaining))


(local (in-theory (disable v_real-of-fields)))

(local (in-theory (disable floor)))

(local (in-theory (disable v_int-of-fields)))
(local (include-book "centaur/bitops/ihsext-basics" :Dir :System))


(def-asl-shallow abs-real
  :function "Abs"
  :args (val)
  :returns (ret))

(def-asl-shallow abs-int
  :function "Abs-1"
  :args (val)
  :returns (ret))

(def-asl-shallow min-real
  :function "Min"
  :args (a b)
  :returns (ret))

(def-asl-shallow min-int
  :function "Min-1"
  :args (a b)
  :returns (ret))

(def-asl-shallow iseven
  :function "IsEven"
  :args (a)
  :returns (ret))

(def-asl-shallow real-of-int
  :function "Real"
  :args (a)
  :returns (ret))



(def-asl-shallow zeros-1
  :function "Zeros-1"
  :params (n)
  :returns (ret))

;; (defopener open-take take :hyp (syntaxp (quotep acl2::n)))
;; (defthm pairlis$-of-cons
;;   (equal (pairlis$ (cons a b) c)
;;          (cons (cons a (car c))
;;                (pairlis$ b (cdr c)))))

;; (defthm pairlis$-when-atom
;;   (implies (atom a)
;;            (equal (pairlis$ a b) nil)))


;; (defopener open-env-find env-find)
;; (defopener open-declare_local_identifiers declare_local_identifiers)
;; (defopener open-env-push-stack env-push-stack)

;; (local (in-theory (disable put-assoc-equal
;;                            assoc-equal
;;                            alistp
;;                            hons-assoc-equal
;;                            ;; take
;;                            ;; pairlis$
;;                            ;; (:t env->global)
;;                            ;; (:t zeros-1)
;;                            ;; (:t global-env->static)
;;                            ;; (:t global-env->stack_size)
;;                            ;; (:t global-env->storage)
;;                            ;; (:t increment-stack)
;;                            ;; (:t v_int)
;;                            ;; (:t env)
;;                            ;; (:t ev_normal)
;;                            ;; (:t ev_throwing)
;;                            ;; (:t ev_error)
;;                            ;; (:t sh_throwing->throwdata)
;;                            ;; (:t sh_error->desc)
;;                            ;; (:t func_result)
;;                            ;; (:t v_bitvector)
;;                            ;; (:t ev_throwing->env)
;;                            ;; (:t eval_subprogram)
;;                            ;; (:t func_result->env)
;;                            ;; (:t local-env)
;;                            ;; (:t decrement-stack)
;;                            ;; (:t ev_throwing->throwdata)
;;                            ;; (:t exprlist_result)
;;                            ;; (:t expr_result)
;;                            ;; (:t exprlist_result->env)
;;                            ;; (:t v_array)
;;                            ;; (:t global-env)
;;                            (:t ACL2::|x < y  =>  0 < -x+y|)
;;                            (:t shallow_result-kind)
;;                            (:t global-env->stack_size)
;;                            (:t global-env->storage)
;;                            (:t increment-stack)
;;                            (:t eval_result-kind)
;;                            (:t sh_error->desc)
;;                            (:t decrement-stack)
;;                            (:t eval_subprogram-fn)
;;                            )))

(def-asl-shallow zeros
  :function "Zeros"
  :params (n)
  :args (n)
  :returns (ret))




(def-asl-shallow ones-1
  :function "Ones-1"
  :params (n)
  :returns (ret))

(def-asl-shallow ones
  :function "Ones"
  :params (n)
  :args (n)
  :returns (ret))


(def-asl-shallow replicatebit-1
  :function "ReplicateBit-1"
  :params (n)
  :args (b)
  :returns (ret))

(local (include-book "arithmetic/top" :dir :system))

(local (defthm consolidate-constants-on-<
         (implies (syntaxp (and (quotep n) (quotep m)))
                  (equal (< (+ n x) m)
                         (< x (+ (- n) (fix m)))))
         :hints (("goal" :cases ((< (+ n x) m))))))

(local (defthm ifix-gte-nonneg
         (implies (and (<= n (ifix x))
                       (posp n))
                  (<= n x))
         :rule-classes :forward-chaining))
                       

(def-asl-shallow replicatebit
  :function "ReplicateBit"
  :params (n)
  :args (b n)
  :returns (ret))

(Defstub foo () nil)
(verify
 (implies (AND
           (SUBPROGRAMS-MATCH '("ReplicateBit" "Zeros-1" "Ones-1" "ReplicateBit-1")
                              (GLOBAL-ENV->STATIC (ENV->GLOBAL ENV))
                              (STDLIB-STATIC-ENV))
           (<= 3 (IFIX CLK))
           (INTEGERP N)
           (INTEGERP N)
           (BOOLEANP B))
          (equal (MV-NTH 0
                         (EVAL_SUBPROGRAM ENV "ReplicateBit" (LIST (V_INT N))
                                          (LIST (V_BOOL B) (V_INT N))))
                 (foo))))

(defthm if-nonnil
  (implies (and (syntaxp (quotep x))
                x)
           (equal (if x y z) y)))

(defthm if-nil
  (equal (if nil y z) z))
