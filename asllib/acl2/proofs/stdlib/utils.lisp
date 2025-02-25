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

(include-book "../../interp")
(include-book "centaur/meta/variable-free" :dir :system)

(define find-nth-form-aux ((n natp)
                           (tag symbolp)
                           x)
  :returns (mv (new-n acl2::maybe-natp :rule-classes :type-prescription)
               form)
  (b* (((when (atom x)) (mv (lnfix n) nil))
       ((when (and (zp n) (eq (car x) tag)))
        (mv nil x))
       (next-n (if (eq (car x) tag) (1- n) n))
       ((mv new-n form) (find-nth-form-aux next-n tag (car x)))
       ((unless new-n) (mv nil form)))
    (find-nth-form-aux new-n tag (cdr x))))

(define find-nth-form ((n natp) (tag symbolp) x)
  (b* (((mv & form) (find-nth-form-aux n tag x)))
    form))




;; Induction scheme for while loops
(define loop-induct ((env env-p) (clk natp) (test expr-p) (body stmt-p) (whilep))
  :verify-guards nil
  :measure (nfix clk)
  (b* (((ev_normal cev) (eval_expr env test))
       ((expr_result cev.res))
       ((unless (iff (ev_normal->res (v_to_bool cev.res.val)) whilep))
        env)
       ((ev_normal blkev) (eval_block cev.res.env body))
       ((continuing blkev.res))
       ((when (zp clk))
        blkev.res.env))
    (loop-induct blkev.res.env (1- clk) test body whilep)))
(in-theory (enable (:i loop-induct)))

    

(define spmatch-force-exec (x) x
  ///
  (in-theory (disable (:t spmatch-force-exec))))

(cmr::def-force-execute force-execute-spmatch-force-exec spmatch-force-exec)

(in-theory (enable force-execute-spmatch-force-exec))


(define subprograms-match ((names identifierlist-p)
                           (env static_env_global-p)
                           (env1 static_env_global-p))
  (if (atom names)
      t
    (and (equal (hons-assoc-equal (car names)
                                  (static_env_global->subprograms env))
                (hons-assoc-equal (car names)
                                  (static_env_global->subprograms env1)))
         (subprograms-match (cdr names) env env1)))
  ///
  (defthm subprogram-lookup-when-match
    (implies (and (syntaxp (quotep name))
                  (subprograms-match names env env1)
                  (spmatch-force-exec (member-equal name names))
                  (equal look (spmatch-force-exec
                               (hons-assoc-equal name (static_env_global->subprograms env1))))
                  (syntaxp (quotep look)))
             (equal (hons-assoc-equal name
                                      (static_env_global->subprograms env))
                    look))
    :hints(("Goal" :in-theory (enable spmatch-force-exec))))

  (local (defthm subprogram-match-when-member
           (implies (and (subprograms-match names1 env env1)
                         (member-equal name names1))
                    (equal (equal (hons-assoc-equal name
                                                    (static_env_global->subprograms env))
                                  (hons-assoc-equal name
                                                    (static_env_global->subprograms env1)))
                           t))))

  (defthm subprograms-match-when-subsetp
    (implies (and (syntaxp (quotep names))
                  (subprograms-match names1 env env1)
                  (syntaxp (quotep names1))
                  (subsetp-equal names names1))
             (subprograms-match names env env1))))



