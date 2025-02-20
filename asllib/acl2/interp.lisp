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
(include-book "ihs/basic-definitions" :dir :system)
(local (table fty::deftagsum-defaults :short-names t))

(deftypes val
  (deftagsum val
    (:v_int ((val integerp)))
    (:v_bool ((val booleanp)))
    (:v_real ((val rationalp)))
    (:v_string ((val stringp)))
    (:v_bitvector ((len natp) (val natp)))
    (:v_label ((val stringp)))
    (:v_record ((rec record-val)))
    (:v_array  ((arr vallist))))
  (fty::deflist vallist :elt-type val :true-listp t)
  (fty::defmap record-val :key-type symbolp :val-type val :true-listp t))


(define v_of_literal ((x literal-p))
  :returns (v val-p)
  (literal-case x
    :l_int (v_int x.val)
    :l_bool (v_bool x.val)
    :l_real (v_real x.val)
    :l_bitvector (v_bitvector x.len x.val)
    :l_string (v_string x.val)
    :l_label (v_label x.val)))


(fty::defmap val-storage :key-type identifier :val-type val :true-listp t)
(fty::defmap int-imap :key-type identifier :val-type integerp :true-listp t)



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



(deftagsum eval_result
  (:ev_normal (res))
  (:ev_throwing ((throwdata maybe-throwdata)
                 (env env)))
  (:ev_error    ((desc stringp)
                 (data))))


(defmacro def-eval_result (pred res-pred)
  `(define ,pred (x)
     (and (eval_result-p x)
          (eval_result-case x
            :ev_normal (,res-pred x.res)
            :otherwise t))
     ///
     (defthm ,(intern-in-package-of-symbol
               (concatenate 'string (symbol-name pred) "-IMPLIES") pred)
       (implies (,pred x)
                (and (eval_result-p x)
                     (implies (eval_result-case x :ev_normal)
                              (,res-pred (ev_normal->res x))))))

     (defthm ,(intern-in-package-of-symbol
               (concatenate 'string (symbol-name pred) "-WHEN-EVAL_RESULT-P") pred)
       (implies (and (eval_result-p x)
                     (or (not (eval_result-case x :ev_normal))
                         (,res-pred (ev_normal->res x))))
                (,pred x)))))


(defprod expr_result
  ((val val)
   (env env)))

(def-eval_result expr_eval_result-p expr_result-p)

(defprod exprlist_result
  ((val vallist)
   (env env)))

(def-eval_result exprlist_eval_result-p exprlist_result-p)

(deftagsum control_flow_state
  (:returning ((vals vallist)
               (env global-env)))
  (:continuing ((env env))))

(def-eval_result stmt_eval_result-p control_flow_state-p)

(defprod func_result ((vals val_read_from-list)
                      (env global-env)))

(def-eval_result func_eval_result-p func_result-p)


;; (deftagsum expr_eval_type
;;   (:normal ((val val)
;;             (env env)))
;;   (:throwing ((throwdata maybe-throwdata)
;;               (env env)))
;;   (:error    ((desc stringp)
;;               (data))))


;; (deftagsum stmt_eval_type
;;   (:normal ((st control_flow_state)))
;;   (:throwing ((throwdata maybe-throwdata)
;;               (env env)))
;;   (:error    ((desc stringp)
;;               (data))))

;; (deftagsum func_eval_type
;;   (:normal ((vals val_read_from-list)
;;             (env global-env)))
;;   (:throwing ((throwdata maybe-throwdata)
;;               (env env)))
;;   (:error    ((desc stringp)
;;               (data))))
  


;; sequential bind
(defmacro let*s (&rest args) (cons 'let* args))
;; data bind
(defmacro let*d (&rest args) (cons 'let* args))
;; control bind
(defmacro let*= (&rest args) (cons 'let* args))

;; bind_exception_seq
(defmacro let** (bindings &rest args)
  (b* (((when (atom bindings)) `(let* () . ,args))
       ((cons (list binder val) rest-bindings) bindings))
    `(b* ((evresult ,val))
       (eval_result-case evresult
         :ev_normal (b* ((,binder evresult.res))
                      (let** ,rest-bindings . ,args))
         :otherwise evresult))))
           
(deftagsum env_result
  (:lk_local ((val val)))
  (:lk_global ((val val)))
  (:lk_notfound ()))

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
       ((When local-look) (lk_local (cdr local-look)))
       ((global-env env.global))
       (global-look (assoc-equal (identifier-fix x) env.global.storage))
       ((When global-look) (lk_global (cdr global-look))))
    (lk_notfound)))


(def-eval_result val_result-p val-p)

(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable floor mod)))

(define eval_binop ((op binop-p)
                    (v1 val-p)
                    (v2 val-p))
  :returns (res val_result-p)
  (b* ((op (binop-fix op)))
    (case op
      ((:plus :mul :minus)
       (val-case v1
         :v_int (val-case v2 :v_int (ev_normal (v_int (case op
                                                        (:plus (+ v1.val v2.val))
                                                        (:mul (* v1.val v2.val))
                                                        (:minus (- v1.val v2.val)))))
                  :otherwise (ev_error "bad binop" (list op v1 v2)))
         :v_real (val-case v2 :v_real (ev_normal (v_real (case op
                                                           (:plus (+ v1.val v2.val))
                                                           (:mul (* v1.val v2.val))
                                                           (:minus (- v1.val v2.val)))))
                   :otherwise (ev_error "bad binop" (list op v1 v2)))
         :otherwise (ev_error "bad binop" (list op v1 v2))))
      (:div (val-case v1
              :v_int (val-case v2 :v_int (if (and (< 0 v2.val)
                                                  (eql (mod v1.val v2.val) 0))
                                             (ev_normal (v_int (/ v1.val v2.val)))
                                           (ev_error "bad div operator" (list v1.val v2.val)))
                       :otherwise (ev_error "bad binop" (list op v1 v2)))
              :otherwise (ev_error "bad binop" (list op v1 v2))))
      (:divrm (val-case v1
                :v_int (val-case v2 :v_int (if (< 0 v2.val)
                                               (ev_normal (v_int (floor v1.val v2.val)))
                                             (ev_error "bad divrm operator" (list v1.val v2.val)))
                         :otherwise (ev_error "bad binop" (list op v1 v2)))
                :otherwise (ev_error "bad binop" (list op v1 v2))))
      (:mod (val-case v1
              :v_int (val-case v2 :v_int (if (< 0 v2.val)
                                             (ev_normal (v_int (mod v1.val v2.val)))
                                           (ev_error "bad divrm operator" (list v1.val v2.val)))
                       :otherwise (ev_error "bad binop" (list op v1 v2)))
              :otherwise (ev_error "bad binop" (list op v1 v2))))
      (:pow (val-case v2
              :v_int (val-case v1
                       :v_int (if (<= 0 v2.val)
                                  (ev_normal (v_int (expt v1.val v2.val)))
                                (ev_error "bad pow operator" (list v1.val v2.val)))
                       :v_real (if (and (eql v1.val 0)
                                        (< v2.val 0))
                                   (ev_error "bad pow operator" (list v1.val v2.val))
                                 (ev_normal (v_real (expt v1.val v2.val))))
                       :otherwise (ev_error "bad binop" (list op v1 v2)))
              :otherwise (ev_error "bad binop" (list op v1 v2))))
      (t (ev_error "undefined binop" (list op v1 v2))))))



(define eval_unop ((op unop-p)
                   (v val-p))
  :returns (res val_result-p)
  (b* ((op (unop-fix op)))
    (case op
      (:bnot ;;!
       (val-case v
         :v_bool (ev_normal (v_bool (not v.val)))
         :otherwise (ev_error "bad unop" (list op v))))
      (:neg
       (val-case v
         :v_int (ev_normal (v_int (- v.val)))
         :v_real (ev_normal (v_real (- v.val)))
         :otherwise (ev_error "bad unop" (list op v))))
      (:not
       (val-case v
         :v_bitvector (ev_normal (v_bitvector v.len (acl2::lognotu v.len v.val)))
         :otherwise (ev_error "bad unop" (list op v))))
      (t (ev_error "undefined uop" (list op v)))))
  )


;; (i-am-here)

(local
 (defthm nth-of-vallist
   (implies (and
             (vallist-p l)
             (<= 0 idx)
             (< idx (len l)))
            (val-p (nth idx l)))))

(defines eval_expr
  (define eval_expr ((env env-p)
                     (e expr-p)
                     (clk natp))
    :verify-guards nil
    :returns (eval expr_eval_result-p)
    :measure (acl2::two-nats-measure clk (expr-count e))
    (b* ((desc (expr->desc e)))
      (expr_desc-case desc
        :e_literal (ev_normal (expr_result (v_of_literal desc.val) env)) ;; SemanticsRule.ELit
        :e_var (b* ((look (env-find desc.name env)))
                 (env_result-case look
                   :lk_local (ev_normal (expr_result look.val env))
                   :lk_global (ev_normal (expr_result look.val env))
                   :lk_notfound (ev_error "Variable not found" desc))) ;; SemanticsRule.EVar
        :e_pattern (let**
                    (((expr_result v1) (eval_expr env desc.expr clk)))
                    (eval_pattern v1.env v1.val desc.pattern clk))     
        :e_unop ;; anna
        (let**
         (((expr_result v) (eval_expr env desc.arg clk))
          (val (eval_unop desc.op v.val)))   ;;SemanticsRule.Unop
         (ev_normal (expr_result val v.env)))
        ;;(ev_error "Unsupported expression" desc)
        :e_binop ;;
        (ev_error "Unsupported expression" desc)
        :e_call ;; sol
        (ev_error "Unsupported expression" desc)
        :e_slice ;; anna
        (ev_error "Unsupported expression" desc)
        :e_cond  ;; anna
        (let**
         (((expr_result test) (eval_expr env desc.test clk))
          (choice (val-case test.val
                    :v_bool (ev_normal (if test.val.val desc.then desc.else))
                    :otherwise (ev_error "bad test in e_cond" test.val))))
         (eval_expr test.env choice clk))
        :e_getarray ;; sol
        (ev_error "Unsupported expression" desc)
        :e_getenumarray ;; sol
        (ev_error "Unsupported expression" desc)
        :e_getfield ;; anna
        (ev_error "Unsupported expression" desc)
        :e_getfields ;; sol
        (ev_error "Unsupported expression" desc)
        :e_getitem ;; anna
        (let**
         (((expr_result varr) (eval_expr env desc.base clk)))
         (val-case varr.val
           :v_array (if (or (< desc.index 0) (<= (len varr.val.arr) desc.index))
                        (ev_error "index out of bounds" desc)
                      (ev_normal (expr_result (nth desc.index varr.val.arr) varr.env)))
           :otherwise (ev_error "evaluation of the base did not return v_array as expected" desc)))  
        :e_record ;; sol
        (ev_error "Unsupported expression" desc)
        :e_tuple ;; anna
        (let**
          (((exprlist_result vals) (eval_expr_list env desc.exprs clk)))
          (ev_normal (expr_result (v_array vals.val) vals.env)))
        :e_array ;; sol
        (ev_error "Unsupported expression" desc)
        :e_enumarray ;; anna
        (ev_error "Unsupported expression" desc)
        :e_arbitrary ;; sol
        (ev_error "Unsupported expression" desc)
        :otherwise (ev_error "Unsupported expression" desc))))

  (define eval_pattern ((env env-p)
                        (val val-p)
                        (p pattern-p)
                        (clk natp))
    :measure (acl2::two-nats-measure clk (pattern-count p))
    ;; :returns (val val-p)
    ;; Note: we may want to have this return just a value since it's not
    ;; supposed to produce any side effects?
    :returns (eval expr_eval_result-p)
    (b* ((desc (pattern->val p)))
      (pattern_desc-case desc
        :pattern_all (ev_normal (expr_result (v_bool t) env)) ;; SemanticsRule.PAll
        :pattern_any (eval_pattern-any env val desc.patterns clk)
        :otherwise (ev_error "Unsupported pattern" desc))))

  (define eval_pattern-any ((env env-p)
                            (val val-p)
                            (p patternlist-p)
                            (clk natp))
    :measure (acl2::two-nats-measure clk (patternlist-count p))

    :returns (eval expr_eval_result-p)
    (if (atom p)
        (ev_normal (expr_result (v_bool nil) env))
      (let**
       (((expr_result v1) (eval_pattern env val (car p) clk)))
       (val-case v1.val
         :v_bool (if v1.val.val
                     (ev_normal v1)
                   (eval_pattern-any v1.env val (cdr p) clk))
         :otherwise (ev_error "Bad result type from eval_pattern" v1)))))


  (define eval_expr_list ((env env-p)
                          (e exprlist-p)
                          (clk natp))
    :returns (eval exprlist_eval_result-p)
    :measure (acl2::two-nats-measure clk (exprlist-count e))
    (if (atom e)
        (ev_normal (exprlist_result nil env))
      (let** (((expr_result first) (eval_expr env (car e) clk)))
             (let* ((env first.env))
               (let** (((exprlist_result rest) (eval_expr_list env (cdr e) clk)))
                      (ev_normal (exprlist_result (cons first.val rest.val) rest.env)))))))
  
  ;; (define eval_call ((name identifier-p)
  ;;                    (env env-p)
  ;;                    (params exprlist-p)
  ;;                    (args exprlist-p)
  ;;                    (clk natp))
  ;;   (let** (((exprlist_result vargs) (eval_expr_list

  ///
  (verify-guards eval_expr :guard-debug t))
