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

(include-book "centaur/meta/term-vars" :dir :system)
(local (include-book "std/lists/sets" :dir :System))

(defthm symbol-listp-when-pseudo-var-list-p
  (implies (cmr::pseudo-var-list-p x)
           (symbol-listp x)))

(defthm pseudo-var-list-p-of-union
  (implies (and (cmr::pseudo-var-list-p x)
                (cmr::pseudo-var-list-p y))
           (cmr::pseudo-var-list-p (union-equal x y))))

(defthm termlist-vars-of-append
  (acl2::set-equiv (cmr::termlist-vars (append x y))
                   (append (cmr::termlist-vars x)
                           (cmr::termlist-vars y)))
  :hints(("Goal" :in-theory (enable cmr::termlist-vars))))

(in-theory (disable pseudo-termp
                    pseudo-term-listp))
