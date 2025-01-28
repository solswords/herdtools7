;;****************************************************************************;;
;;                                ASLRef                                      ;;
;;****************************************************************************;;
;;
;; SPDX-FileCopyrightText: Copyright 2022-2023 Arm Limited and/or its affiliates <open-source-office@arm.com>
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


(defpkg "ASL"
  (set-difference-eq
   (union-eq
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
       ))
   '(std::deflist)))


        
        
   
