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


(include-book "interp")

(defmacro defopener (name fn &key (hyp 't))
  `(encapsulate nil
     (set-ignore-ok t)
     (make-event
      (b* ((fn (acl2::deref-macro-name ',fn (acl2::macro-aliases (w state))))
           (formals (acl2::formals fn (w state)))
           (body (acl2::body fn nil (w state)))
           (hyp ',hyp)
           (name ',name)
           ((acl2::fun (evnt name fn formals body hyp))
            (b* ((call `(,fn . ,formals))
                 (concl `(equal ,call ,body))
                 (thmbody (if (eq hyp t)
                              concl
                            `(implies ,hyp ,concl))))
              `(defthm ,name ,thmbody
                 :hints (("goal" :expand (,call)))))))
        (evnt name fn formals body hyp)))))


(defopener open-eval_stmt eval_stmt :hyp (syntaxp (quotep s)))
(defopener open-eval_block eval_block :hyp (syntaxp (quotep x)))

(defopener open-eval_expr eval_expr :hyp (syntaxp (quotep e)))
(defopener open-eval_binop eval_binop :hyp (syntaxp (quotep op)))
(defopener open-eval_unop eval_unop :hyp (syntaxp (quotep op)))
(defopener open-eval_call eval_call :hyp (syntaxp (quotep name)))
(defopener open-eval_expr_list eval_expr_list :hyp (syntaxp (quotep e)))
(defopener open-eval_lexpr eval_lexpr :hyp (syntaxp (quotep lx)))
(defopener open-eval_limit eval_limit :hyp (syntaxp (quotep x)))

(defopener open-eval_slice_list eval_slice_list :hyp (syntaxp (quotep sl)))
(defopener open-eval_slice eval_slice :hyp (syntaxp (quotep s)))

(defopener open-is_val_of_type is_val_of_type :hyp (syntaxp (quotep ty)))
(defopener open-check_int_constraints check_int_constraints :hyp (syntaxp (quotep constrs)))

