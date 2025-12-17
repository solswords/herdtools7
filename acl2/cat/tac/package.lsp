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

(in-package "ACL2")


(include-book "std/portcullis" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)
(include-book "centaur/bitops/portcullis" :dir :system)
(include-book "../portcullis")
(include-book "centaur/meta/portcullis" :dir :system)


(defpkg "TAC"
  (set-difference-eq
   (union-eq
    '(pattern-match)
    *standard-acl2-imports*
    std::*std-exports*
    set::*sets-exports*
    bitops::*bitops-exports*
    '(fty::deftagsum
       fty::defprod
       fty::deftypes
       fty::defoption
       fty::deflist
       b*
       pseudo-var pseudo-var-p pseudo-var-fix pseudo-var-equiv
       pseudo-fn pseudo-fn-p pseudo-fn-fix pseudo-fn-equiv
       pseudo-lambda pseudo-lambda-p pseudo-lambda-fix pseudo-lambda-equiv
       pseudo-fnsym pseudo-fnsym-p pseudo-fnsym-fix pseudo-fnsym-equiv
       pseudo-term pseudo-term-kind pseudo-term-case
       pseudo-term-fix pseudo-term-equiv pseudo-term-count
       pseudo-term-list pseudo-term-list-fix pseudo-term-list-equiv pseudo-term-list-count
       pseudo-term-null
       pseudo-term-quote pseudo-term-quote->val
       pseudo-term-var pseudo-term-var->name
       pseudo-term-fncall pseudo-term-fncall->fn
       pseudo-term-lambda pseudo-term-lambda->formals pseudo-term-lambda->body pseudo-term-lambda->fn
       pseudo-term-call pseudo-term-call->fn pseudo-term-call->args
       pseudo-term-const
       a b c x y z
       ))
   '(std::deflist tag exp condition)))


        
        
   
