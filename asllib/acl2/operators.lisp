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

(include-book "interp-types")
(include-book "centaur/fty/multicase" :Dir :system)
(include-book "ihs/logops-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable (tau-system))))

(def-eval_result val_result-p val-p)

(fty::def-enumcase binop-case binop-p)


(define eval_binop ((op binop-p)
                    (v1 val-p)
                    (v2 val-p))
  :returns (res val_result-p)
  (fty::multicase
    ((binop-case op)
     (val-case v1)
     (val-case v2))
    ;; int -> int -> int
    ((:plus :v_int :v_int)       (ev_normal (v_int (+ v1.val v2.val))))
    ((:mul  :v_int :v_int)       (ev_normal (v_int (* v1.val v2.val))))
    ((:minus :v_int :v_int)      (ev_normal (v_int (- v1.val v2.val))))
    ((:div   :v_int :v_int)
     :when (and (< 0 v2.val)
                (eql (mod v1.val v2.val) 0))
                                 (ev_normal (v_int (/ v1.val v2.val))))
    ((:divrm :v_int :v_int)      
     :when (< 0 v2.val)          (ev_normal (v_int (floor v1.val v2.val))))
    ((:mod   :v_int :v_int)      
     :when (< 0 v2.val)          (ev_normal (v_int (mod v1.val v2.val))))
    ((:pow   :v_int :v_int)      
     :when (<= 0 v2.val)         (ev_normal (v_int (expt v1.val v2.val))))
    ((:shl   :v_int :v_int)      
     :when (<= 0 v2.val)         (ev_normal (v_int (ash v1.val v2.val))))
    ((:shr   :v_int :v_int)      
     :when (<= 0 v2.val)         (ev_normal (v_int (ash v1.val (- v2.val)))))
    ;; int -> int -> bool        
    ((:eq_op :v_int :v_int)      (ev_normal (v_bool (eql v1.val v2.val))))
    ((:neq   :v_int :v_int)      (ev_normal (v_bool (not (eql v1.val v2.val)))))
    ((:leq   :v_int :v_int)      (ev_normal (v_bool (<= v1.val v2.val))))
    ((:lt    :v_int :v_int)      (ev_normal (v_bool (<  v1.val v2.val))))
    ((:geq   :v_int :v_int)      (ev_normal (v_bool (>= v1.val v2.val))))
    ((:gt    :v_int :v_int)      (ev_normal (v_bool (>  v1.val v2.val))))
    ;; bool -> bool -> bool      
    ((:band  :v_bool :v_bool)    (ev_normal (v_bool (and v1.val v2.val))))
    ((:bor  :v_bool :v_bool)     (ev_normal (v_bool (or  v1.val v2.val))))
    ((:beq  :v_bool :v_bool)     (ev_normal (v_bool (iff v1.val v2.val))))
    ((:impl :v_bool :v_bool)     (ev_normal (v_bool (or (not v1.val) v2.val))))
    ((:eq_op :v_bool :v_bool)    (ev_normal (v_bool (iff v1.val v2.val))))
    ((:neq   :v_bool :v_bool)    (ev_normal (v_bool (xor v1.val v2.val))))
    ;; real -> real -> real      
    ((:plus :v_real :v_real)     (ev_normal (v_real (+ v1.val v2.val))))
    ((:mul  :v_real :v_real)     (ev_normal (v_real (* v1.val v2.val))))
    ((:minus :v_real :v_real)    (ev_normal (v_real (- v1.val v2.val))))
    ((:rdiv :v_real :v_real)
     :when (not (eql v2.val 0))
                                 (ev_normal (v_real (/ v1.val v2.val))))
    ((:pow  :v_real :v_int)
     :when (not (and (eql v1.val 0) (< v2.val 0)))
                                 (ev_normal (v_real (expt v1.val v2.val))))
    ;; real -> real -> bool      
    ((:eq_op :v_real :v_real)    (ev_normal (v_bool (eql v1.val v2.val))))
    ((:neq   :v_real :v_real)    (ev_normal (v_bool (not (eql v1.val v2.val)))))
    ((:leq   :v_real :v_real)    (ev_normal (v_bool (<= v1.val v2.val))))
    ((:lt    :v_real :v_real)    (ev_normal (v_bool (<  v1.val v2.val))))
    ((:geq   :v_real :v_real)    (ev_normal (v_bool (>= v1.val v2.val))))
    ((:gt    :v_real :v_real)    (ev_normal (v_bool (>  v1.val v2.val))))
    ;; bits -> bits -> bool
    ((:eq_op :v_bitvector :v_bitvector)
     :when (eql v1.len v2.len)    (ev_normal (v_bool (eql v1.val v2.val))))
    ((:neq :v_bitvector :v_bitvector)
     :when (eql v1.len v2.len)    (ev_normal (v_bool (not (eql v1.val v2.val)))))
    ;; bits -> bits -> bits
    ((:or  :v_bitvector :v_bitvector)
     :when (eql v1.len v2.len)    (ev_normal (v_bitvector v1.len (logior v1.val v2.val))))
    ((:and :v_bitvector :v_bitvector)
     :when (eql v1.len v2.len)    (ev_normal (v_bitvector v1.len (logand v1.val v2.val))))
    ((:eor :v_bitvector :v_bitvector)
     :when (eql v1.len v2.len)    (ev_normal (v_bitvector v1.len (logxor v1.val v2.val))))
    ((:plus :v_bitvector :v_bitvector)
     :when (eql v1.len v2.len)    (ev_normal (v_bitvector v1.len
                                                          (loghead v1.len (+ v1.val v2.val)))))
    ((:minus :v_bitvector :v_bitvector)
     :when (eql v1.len v2.len)    (ev_normal (v_bitvector v1.len
                                                          (loghead v1.len (- v1.val v2.val)))))
    ((:bv_concat :v_bitvector :v_bitvector)
                                  (ev_normal (v_bitvector (+ v1.len v2.len)
                                                          ;; FIXME check order?
                                                          (logapp v2.len v2.val v1.val))))
    ;; bits -> integer -> bits
    ((:plus :v_bitvector :v_int)  (ev_normal (v_bitvector v1.len
                                                          (loghead v1.len (+ v1.val v2.val)))))
    ((:minus :v_bitvector :v_int) (ev_normal (v_bitvector v1.len
                                                          (loghead v1.len (- v1.val v2.val)))))
    ;; string -> string -> bool
    ((:eq_op :v_string :v_string) (ev_normal (v_bool (equal v1.val v2.val))))
    ((:neq   :v_string :v_string) (ev_normal (v_bool (not (equal v1.val v2.val)))))
    ;; enum -> enum -> bool
    ((:eq_op :v_label :v_label)   (ev_normal (v_bool (equal v1.val v2.val))))
    ((:neq   :v_label :v_label)   (ev_normal (v_bool (not (equal v1.val v2.val)))))
    ;;  Failure
    (-                            (ev_error "Unsupported binop" (list op v1 v2)))))


(fty::def-enumcase unop-case unop-p)

(define eval_unop ((op unop-p)
                   (v val-p))
  :returns (res val_result-p)
  :guard-debug t
  (fty::multicase
    ((unop-case op)
     (val-case v))
    ((:neg :v_int)       (ev_normal (v_int (- v.val))))
    ((:neg :v_real)      (ev_normal (v_real (- v.val))))
    ((:bnot :v_bool)     (ev_normal (v_bool (not v.val))))
    ((:not :v_bitvector) (ev_normal (v_bitvector v.len (loghead v.len (lognot v.val)))))
    (-                   (ev_error "bad unop" (list op v)))))


