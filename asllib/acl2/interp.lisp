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

(include-book "ast")

(deftypes val
  (deftagsum val
    (:int ((val integerp)))
    (:bool ((val booleanp)))
    (:real ((val rationalp)))
    (:string ((val stringp)))
    (:bitvector ((len natp) (val natp)))
    (:label ((val stringp)))
    (:record ((rec record-val)))
    (:array  ((arr array-val))))
  (fty::deflist array-val :elt-type val :true-listp t)
  (fty::defmap record-val :key-type symbolp :val-type val :true-listp t))


(define v_of_literal ((x literal-p))
  :returns (v val-p)
  (literal-case x
    :l_int (val-int x.val)
    :l_bool (val-bool x.val)
    :l_real (val-real x.val)
    :l_bitvector (val-bitvector x.len x.val)
    :l_string (Val-string x.val)
    :l_label (val-label x.val)))


(fty::defmap val-storage :key-type identifier :val-type val :true-listp t)
(fty::defmap int-imap :key-type identifier :val-type integerp :true-listp t)

(fty::deflist vallist :elt-type val :true-listp t)

(defprod global-env
  ((static static_env_global)
   (storage val-storage)
   (stack_size int-imap))
  :layout :list)

(defprod unit () :layout :list
  ///
  (defthm unit-p-compound-recognizer
    (implies (unit-p x)
             (equal x nil))
    :hints(("Goal" :in-theory (enable unit-p)))
    :rule-classes :compound-recognizer))

(fty::deflist integer-list :pred integer-listp :elt-type integerp :true-listp t)


(defprod local-env
  ((storage val-storage)
   (scope unit)
   (unroll integer-list)
   (declared identifierlist))
  :layout :list)

(defprod env
  ((global global-env)
   (local local-env))
  :layout :list)


(defprod val_read_from
  ((val val)
   (name identifier)
   (scope unit))
  :layout :list)

(fty::deflist val_read_from-list :elt-type val_read_from :true-listp t)

(defprod throwdata
  ((val val_read_from)
   (ty ty))
  :layout :list)

(defoption maybe-throwdata throwdata)


(deftagsum expr_eval_type
  (:normal ((val val)
            (env env)))
  (:throwing ((throwdata maybe-throwdata)
              (env env)))
  (:error    ((desc stringp)
              (data))))

(deftagsum control_flow_state
  (:returning ((vals vallist)
               (env global-env)))
  (:continuing ((env env))))

(deftagsum stmt_eval_type
  (:normal ((st control_flow_state)))
  (:throwing ((throwdata maybe-throwdata)
              (env env)))
  (:error    ((desc stringp)
              (data))))

(deftagsum func_eval_type
  (:normal ((vals val_read_from-list)
            (env global-env)))
  (:throwing ((throwdata maybe-throwdata)
              (env env)))
  (:error    ((desc stringp)
              (data))))
  


;; sequential bind
(defmacro let*s (&rest args) (cons 'let* args))
;; data bind
(defmacro let*d (&rest args) (cons 'let* args))
;; control bind
(defmacro let*= (&rest args) (cons 'let* args))

;; bind_exception_seq
(defmacro let**-expr (bindings &rest args)
  (b* (((when (atom bindings)) `(let* () . ,args))
       ((cons (list var val) rest-bindings) bindings))
    `(let ((,var ,val))
       (expr_eval_type-case ,var
         :normal (let* ((,var ,(intern-in-package-of-symbol
                                (concatenate 'string (symbol-name var) ".VAL")
                                var))
                        (env ,(intern-in-package-of-symbol
                               (concatenate 'string (symbol-name var) ".ENV")
                               var)))
                   (let**-expr ,rest-bindings . ,args))
         :otherwise ,var))))


(deftagsum env_result
  (:local ((val val)))
  (:global ((val val)))
  (:notfound ()))

(local (defthm assoc-equal-is-hons-assoc-equal
         (implies k
                  (equal (assoc-equal k x)
                         (hons-assoc-equal k x)))))

(local (defthm identifier-p-compound-recognizer
         (implies (identifier-p x)
                  (stringp x))
         :hints(("Goal" :in-theory (enable identifier-p)))
         :rule-classes :compound-recognizer))

(define env-find ((x identifier-p)
                  (env env-p))
  :returns (res env_result-p)
  (b* (((env env))
       ((local-env env.local))
       (local-look (assoc-equal (identifier-fix x) env.local.storage))
       ((When local-look) (env_result-local (cdr local-look)))
       ((global-env env.global))
       (global-look (assoc-equal (identifier-fix x) env.global.storage))
       ((When global-look) (env_result-global (cdr global-look))))
    (env_result-notfound)))




(defines eval_expr
  (define eval_expr ((env env-p)
                     (e expr-p)
                     (clk natp))
    :verify-guards nil
    :returns (eval expr_eval_type-p)
    :measure (acl2::two-nats-measure clk (expr-count e))
    (b* ((desc (expr->desc e)))
      (expr_desc-case desc
        :e_literal (expr_eval_type-normal (v_of_literal desc.val) env) ;; SemanticsRule.ELit
        :e_var (b* ((look (env-find desc.name env)))
                 (env_result-case look
                   :local (expr_eval_type-normal look.val env)
                   :global (expr_eval_type-normal look.val env)
                   :notfound (expr_eval_type-error "Variable not found" desc))) ;; SemanticsRule.EVar
        :e_pattern (let**-expr
                    ((v1 (eval_expr env desc.expr clk)))
                    (let**-expr ((v (eval_pattern env v1 desc.pattern clk)))
                           (expr_eval_type-normal v env)))
        :otherwise (expr_eval_type-error "Unsupported expression" desc))))

  (define eval_pattern ((env env-p)
                        (val val-p)
                        (p pattern-p)
                        (clk natp))
    :measure (acl2::two-nats-measure clk (pattern-count p))
    ;; :returns (val val-p)
    ;; Note: we may want to have this return just a value since it's not
    ;; supposed to produce any side effects?
    :returns (eval expr_eval_type-p)
    (b* ((desc (pattern->val p)))
      (pattern_desc-case desc
        :pattern_all (expr_eval_type-normal (val-bool t) env) ;; SemanticsRule.PAll
        :pattern_any (eval_pattern-any env val desc.patterns clk)
        :otherwise (expr_eval_type-error "Unsupported pattern" desc))))

  (define eval_pattern-any ((env env-p)
                            (val val-p)
                            (p patternlist-p)
                            (clk natp))
    :measure (acl2::two-nats-measure clk (patternlist-count p))

    :returns (eval expr_eval_type-p)
    (if (atom p)
        (expr_eval_type-normal (val-bool nil) env)
      (let**-expr
       ((v1 (eval_pattern env val (car p) clk)))
       (val-case v1
         :bool (if v1.val
                   (expr_eval_type-normal v1 env)
                 (eval_pattern-any env val (cdr p) clk))
         :otherwise (expr_eval_type-error "Bad result type from eval_pattern" v1)))))

  ///
  (verify-guards eval_expr))
