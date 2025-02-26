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

(defconst *eval_global-initial-clock* 1000000)

(defconst *main-initial-clock* 1000000)


(define declare_global ((env env-p)
                        (name identifier-p)
                        (val val-p))
  :returns (new-env env-p)
  (b* (((env env))
       ((global-env g) env.global)
       (new-storage (cons (cons (identifier-fix name) (val-fix val))
                          g.storage)))
    (change-env env :global (change-global-env g :storage new-storage))))

(define eval_global ((env env-p)
                     (x decl-p))
  :returns (res env_eval_result-p)
  (b* ((x (decl->val x)))
    (decl_desc-case x
      :d_globalstorage
      (b* (((global_decl d) x.decl)
           ((unless d.initial_value)
            (ev_error "TypeInferenceNeeded" x))
           ((ev (expr_result iv)) (eval_expr env d.initial_value :clk *eval_global-initial-clock*)))
        (ev_normal (declare_global  iv.env d.name iv.val)))
      :otherwise (ev_normal (env-fix env)))))

(define eval_globals ((env env-p)
                      (x ast-p))
  :measure (len x)
  :returns (res env_eval_result-p)
  (b* (((when (atom x)) (ev_normal (env-fix env)))
       ((ev env2) (eval_global env (car x))))
    (eval_globals env2 (cdr x))))



(local (defthm equal-len
         (implies (syntaxp (quotep n))
                  (Equal (equal (len x) n)
                         (if (zp n)
                             (and (equal n 0) (atom x))
                           (and (consp x)
                                (equal (len (cdr x)) (1- n))))))))

(define run ((tenv static_env_global-p) (ast ast-p))
  :returns (val val_result-p)
  (b* ((env0 (make-env :local (empty-local-env)
                       :global (make-global-env :static tenv)))
       ((ev env1) (eval_globals env0 ast))
       ((ev (func_result res))
        (eval_subprogram env1 "main" nil nil :clk *main-initial-clock*))
       ((when (eql (len res.vals) 1))
        (ev_normal (car res.vals))))
    (ev_error "malformed return values from main" res.vals)))

    
