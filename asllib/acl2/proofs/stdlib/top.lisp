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

(include-book "align")
(include-book "bits")
(include-book "ilog2")
(include-book "log2")
(include-book "misc")
(include-book "pow2")
(include-book "round")
(include-book "sint")
(include-book "sqrtrounded")
(include-book "uint")
(include-book "shift")


;; Hackish attempt to make sure there's a theorem for every stdlib function.

(local (include-book "centaur/misc/rewrite-rule" :dir :system))

(local
 (progn
   (std::deflist weak-rewrite-rule-listp (x) (acl2::weak-rewrite-rule-p x))

   (define collect-stdlib-fns-with-rules ((rules weak-rewrite-rule-listp))
     (b* (((when (atom rules)) nil)
          (first (b* (((acl2::rewrite-rule rule) (car rules))
                      ((unless (and (eq rule.equiv 'equal)
                                    (not (eq rule.subclass 'acl2::meta))))
                       nil))
                   (case-match rule.lhs
                     (('mv-nth ''0 ('eval_subprogram-fn 'env ('quote fn) & & 'clk 'orac))
                      (and (stringp fn) fn))
                     (& nil)))))
       (if first
           (cons first (collect-stdlib-fns-with-rules (cdr rules)))
         (collect-stdlib-fns-with-rules (cdr rules)))))

   (assert-event
    (equal (mergesort
            (collect-stdlib-fns-with-rules
             (fgetprop 'mv-nth 'acl2::lemmas nil (w state))))
           (mergesort
            (acl2::alist-keys
             (static_env_global->subprograms (stdlib-static-env))))))))
