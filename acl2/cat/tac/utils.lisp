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

(in-package "TAC")

(include-book "centaur/meta/parse-rewrite" :dir :system)
(include-book "centaur/meta/unify-strict" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(local (include-book "std/lists/append" :dir :system))
(local (std::add-default-post-define-hook :fix))

(fty::defalist tac-rewritelist :key-type symbolp :val-type cmr::rewrite :true-listp t)

(define pair-name-with-rules ((name symbolp) (rules cmr::rewritelist-p))
  :returns (rewrites tac-rewritelist-p)
  (if (atom rules)
      nil
    (cons (cons (mbe :logic (acl2::symbol-fix name) :exec name)
                (cmr::rewrite-fix (car rules)))
          (pair-name-with-rules name (cdr rules)))))

(define tac-collect-rewrites-aux ((names symbol-listp)
                                  (wrld plist-worldp))
  :returns (mv err (rules tac-rewritelist-p))
  (if (atom names)
      (mv nil nil)
    (b* ((formula (acl2::meta-extract-formula-w (car names) wrld))
         ((unless (pseudo-termp formula))
          (mv (msg "~x0 not pseudo-termp: ~x1" (car names) formula) nil))
         ((mv err rules1)
          (cmr::parse-rewrites-from-term formula wrld))
         ((when err)
          (mv err nil))
         ((mv err rules2)
          (tac-collect-rewrites-aux (cdr names) wrld))
         ((when err)
          (mv err nil)))
      (mv nil (append (pair-name-with-rules (car names) rules1) rules2)))))

(define tac-rewritelist-terms ((x tac-rewritelist-p))
  :returns (terms pseudo-term-listp)
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (cons (cmr::rewrite-term (cdar x))
              (tac-rewritelist-terms (cdr x)))
      (tac-rewritelist-terms (cdr x))))
  ///
  (local (in-theory (enable tac-rewritelist-fix))))
