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

(include-book "centaur/bitops/part-select" :dir :system)
(include-book "centaur/bitops/part-install" :dir :system)

;; (local (include-book "std/strings/hexify" :dir :system))
(include-book "std/alists/alist-defuns" :dir :system)
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (table fty::deftagsum-defaults :short-names t))
(local (in-theory (disable (tau-system))))
(local (in-theory (disable put-assoc-equal)))

(deftypes val
  (deftagsum val
    (:v_int ((val integerp)))
    (:v_bool ((val booleanp)))
    (:v_real ((val rationalp)))
    (:v_string ((val stringp)))
    (:v_bitvector ((len natp) (val natp)))
    (:v_label ((val identifier-p)))
    (:v_record ((rec val-imap)))
    (:v_array  ((arr vallist))))
  (fty::deflist vallist :elt-type val :true-listp t)
  (fty::defmap val-imap :key-type identifier :val-type val :true-listp t)
  ///
  (defthm val-imap-p-of-pairlis$
    (implies (and (identifierlist-p keys)
                  (vallist-p vals)
                  (equal (len keys) (len vals)))
             (val-imap-p (pairlis$ keys vals))))

  (defthm vallist-p-of-update-nth
    (implies (and (vallist-p x)
                  (val-p v)
                  (<= (nfix n) (len x)))
             (vallist-p (update-nth n v x)))
    :hints(("Goal" :in-theory (enable update-nth vallist-p))))

  (defthm val-imap-p-of-put-assoc-equal
    (implies (and (val-imap-p x)
                  (identifier-p k)
                  (val-p v))
             (val-imap-p (put-assoc-equal k v x)))
    :hints(("Goal" :in-theory (enable put-assoc-equal)))))

(local
  (defthm alistp-when-val-imap-p-rw
    (implies (val-imap-p x)
             (alistp x))
    :hints(("Goal" :in-theory (enable val-imap-p)))))

(local
 (defthm alistp-when-func-ses-imap-p-rw
   (implies (func-ses-imap-p x)
            (alistp x))
   :hints(("Goal" :in-theory (enable func-ses-imap-p)))))


(define v_of_literal ((x literal-p))
  :returns (v val-p)
  (literal-case x
    :l_int (v_int x.val)
    :l_bool (v_bool x.val)
    :l_real (v_real x.val)
    :l_bitvector (v_bitvector x.len x.val)
    :l_string (v_string x.val)
    :l_label (v_label x.val)))

(fty::defmap int-imap :key-type identifier :val-type integerp :true-listp t)
  
(local
 (defthm alistp-when-int-imap-p-rw
   (implies (int-imap-p x)
            (alistp x))
   :hints(("Goal" :in-theory (enable int-imap-p)))))



(defprod global-env
  ((static static_env_global)
   (storage val-imap)
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
  ((storage val-imap)
   (scope unit)
   (unroll integer-list)
   (declared identifierlist))
  :layout :list)

(define empty-local-env ()
  :returns (empty local-env-p)
  (make-local-env))


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

(defprod func_result ((vals vallist ;; val_read_from-list
                            )
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

(defmacro let*^ (&rest args) (cons 'let** args))

(acl2::def-b*-binder ev
  :body
  `(b* ((evresult ,(car acl2::forms)))
     (eval_result-case evresult
       :ev_normal (b* ((,(car acl2::args) evresult.res))
                    ,acl2::rest-expr)
       :otherwise evresult)))


(defmacro let*> (bindings &rest args)
  (b* (((when (atom bindings)) `(let* () . ,args))
       ((cons (list binder val) rest-bindings) bindings))
    `(let** ((cflow ,val))
            (control_flow_state-case cflow
              :returning (ev_normal cflow)
              :continuing (b* ((,binder cflow.env))
                            (let*> ,rest-bindings . ,args))))))


(acl2::def-b*-binder evs
  :body
  `(b* (((ev cflow) ,(car acl2::forms)))
     (control_flow_state-case cflow
              :returning (ev_normal cflow)
              :continuing (b* ((,(car acl2::args) cflow.env))
                            ,acl2::rest-expr))))

(deftagsum env_result
  (:lk_local ((val)))
  (:lk_global ((val)))
  (:lk_notfound ()))


(defmacro def-env_result (pred res-pred)
  `(define ,pred (x)
     (and (env_result-p x)
          (env_result-case x
            :lk_local (,res-pred x.val)
            :lk_global (,res-pred x.val)
            :otherwise t))
     ///
     (defthm ,(intern-in-package-of-symbol
               (concatenate 'string (symbol-name pred) "-IMPLIES") pred)
       (implies (,pred x)
                (and (env_result-p x)
                     (implies (env_result-case x :lk_local)
                              (,res-pred (lk_local->val x)))
                     (implies (env_result-case x :lk_global)
                              (,res-pred (lk_global->val x))))))

     (defthm ,(intern-in-package-of-symbol
               (concatenate 'string (symbol-name pred) "-WHEN-ENV_RESULT-P") pred)
       (implies (and (env_result-p x)
                     (or (not (env_result-case x :lk_local))
                         (,res-pred (lk_local->val x)))
                     (or (not (env_result-case x :lk_global))
                         (,res-pred (lk_global->val x))))
                (,pred x)))))

(def-env_result val_env_result-p val-p)
(def-env_result env_env_result-p env-p)


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
  :returns (res val_env_result-p)
  (b* (((env env))
       ((local-env env.local))
       (local-look (assoc-equal (identifier-fix x) env.local.storage))
       ((When local-look) (lk_local (cdr local-look)))
       ((global-env env.global))
       (global-look (assoc-equal (identifier-fix x) env.global.storage))
       ((When global-look) (lk_global (cdr global-look))))
    (lk_notfound)))

(define env-assign-local ((name identifier-p)
                          (v val-p)
                          (env env-p))
  :returns (new-env env-p)
  (b* (((env env))
       ((local-env env.local))
       (name (identifier-fix name)))
    (change-env env
                :local (change-local-env
                        env.local
                        :storage (put-assoc-equal name (val-fix v) env.local.storage)))))

(define env-assign-global ((name identifier-p)
                           (v val-p)
                           (env env-p))
  :returns (new-env env-p)
  (b* (((env env))
       ((global-env env.global))
       (name (identifier-fix name)))
    (change-env env
                :global (change-global-env
                         env.global
                         :storage (put-assoc-equal name (val-fix v) env.global.storage)))))

(define env-assign ((name identifier-p)
                    (v val-p)
                    (env env-p))
  :returns (res env_env_result-p)
  (b* (((env env))
       ((local-env env.local))
       (name (identifier-fix name))
       (local-look (assoc-equal name env.local.storage))
       ((When local-look)
        (lk_local (env-assign-local name v env)))
       ((global-env env.global))
       (global-look (assoc-equal name env.global.storage))
       ((When global-look)
        (lk_global (env-assign-global name v env))))
    (lk_notfound)))


(def-eval_result val_result-p val-p)
(def-eval_result vallist_result-p vallist-p)

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
      ((:eq_op :neq)
       (val-case v1
         :v_int (val-case v2 :v_int (ev_normal (v_bool (eql v1.val v2.val)))
                  :otherwise (ev_error "bad binop" (list op v1 v2)))
         :v_bool (val-case v2 :v_bool (ev_normal (v_bool (eq v1.val v2.val)))
                  :otherwise (ev_error "bad binop" (list op v1 v2)))
         :v_real (val-case v2 :v_real (ev_normal (v_bool (equal v1.val v2.val)))
                   :otherwise (ev_error "bad binop" (list op v1 v2)))
         :v_bitvector (val-case v2 :v_bitvector
                        (if (eql v1.len v2.len)
                            (ev_normal (v_bool (eql v1.val v2.val)))
                          (ev_error "bad binop" (list op v1 v2)))
                        :otherwise (ev_error "bad binop" (list op v1 v2)))
         :v_string (val-case v2 :v_string (ev_normal (v_bool (equal v1.val v2.val)))
                     :otherwise (ev_error "bad binop" (list op v1 v2)))
         :v_label (val-case v2 :v_label (ev_normal (v_bool (equal v1.val v2.val)))
                    :otherwise (ev_error "bad binop" (list op v1 v2)))
         :otherwise (ev_error "bad binop" (list op v1 v2))))
      ((:leq :lt :geq :gt)
       (b* (((mv err val1 val2)
             (val-case v1
               :v_int (val-case v2 :v_int (mv nil v1.val v2.val) :otherwise (mv t nil nil))
               :v_real (val-case v2 :v_real (mv nil v1.val v2.val) :otherwise (mv t nil nil))
               :otherwise (mv t nil nil)))
            ((when err)
             (ev_error "bad binop" (list op v1 v2))))
         (ev_normal (v_bool (case op
                              (:leq (<= val1 val2))
                              (:lt (< val1 val2))
                              (:geq (>= val1 val2))
                              (t (> val1 val2)))))))
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
      ((:band :bor :beq :impl)
       (val-case v1 :v_bool
         (val-case v2 :v_bool
           (ev_normal (v_bool (case op
                                (:band (and v1.val v2.val))
                                (:bor (or v1.val v2.val))
                                (:beq (eq v1.val v2.val))
                                (t    (implies v1.val v2.val)))))
           :otherwise (ev_error "bad binop" (list op v1 v2)))
         :otherwise (ev_error "bad binop" (list op v1 v2))))
      (t (ev_error "undefined binop" (list op v1 v2))))))

(defines lexpr-count*
  (define lexpr_desc-count* ((x lexpr_desc-p))
    :measure (lexpr_desc-count x)
    :returns (count posp :rule-classes :type-prescription)
    (lexpr_desc-case x
      :le_slice (+ 3
                   (lexpr-count* x.base)
                   (slicelist-count x.slices))
      :le_setarray (+ 3 (lexpr-count* x.base)
                      (expr-count x.index))
      :le_setenumarray (+ 3 (lexpr-count* x.base)
                          (expr-count x.index))
      :le_setfield (+ 3 (lexpr-count* x.base))
      :le_setfields (+ 3 (lexpr-count* x.base))
      :le_destructuring (+ 2 (lexprlist-count* x.elts))
      :otherwise 1))

  (define lexpr-count* ((x lexpr-p))
    :measure (lexpr-count x)
    :returns (count posp :rule-classes :type-prescription)
    (+ 2 (lexpr_desc-count* (lexpr->val x))))

  (define lexprlist-count* ((x lexprlist-p))
    :measure (lexprlist-count x)
    :returns (count posp :rule-classes :type-prescription)
    (if (atom x)
        1
      (+ 1 (lexpr-count* (car x))
         (lexprlist-count* (cdr x)))))
  ///
  (defthm lexpr_desc-count*-le_slice
    (implies (lexpr_desc-case x :le_slice)
             (b* (((le_slice x)))
               (< (+ (lexpr-count* x.base)
                     (slicelist-count x.slices))
                  (lexpr_desc-count* x))))
    :hints (("goal" :expand ((lexpr_desc-count* x))))
    :rule-classes :linear)

  (defthm lexpr_desc-count*-le_setarray
    (implies (lexpr_desc-case x :le_setarray)
             (b* (((le_setarray x)))
               (< (+ (lexpr-count* x.base)
                     (expr-count x.index))
                  (lexpr_desc-count* x))))
    :hints (("goal" :expand ((lexpr_desc-count* x))))
    :rule-classes :linear)

  (defthm lexpr_desc-count*-le_setenumarray
    (implies (lexpr_desc-case x :le_setenumarray)
             (b* (((le_setenumarray x)))
               (< (+ (lexpr-count* x.base)
                     (expr-count x.index))
                  (lexpr_desc-count* x))))
    :hints (("goal" :expand ((lexpr_desc-count* x))))
    :rule-classes :linear)

  (defthm lexpr_desc-count*-le_setfield
    (implies (lexpr_desc-case x :le_setfield)
             (b* (((le_setfield x)))
               (< (lexpr-count* x.base)
                  (lexpr_desc-count* x))))
    :hints (("goal" :expand ((lexpr_desc-count* x))))
    :rule-classes :linear)

  (defthm lexpr_desc-count*-le_setfields
    (implies (lexpr_desc-case x :le_setfields)
             (b* (((le_setfields x)))
               (< (lexpr-count* x.base)
                  (lexpr_desc-count* x))))
    :hints (("goal" :expand ((lexpr_desc-count* x))))
    :rule-classes :linear)

  (defthm lexpr_desc-count*-le_destructuring
    (implies (lexpr_desc-case x :le_destructuring)
             (b* (((le_destructuring x)))
               (< (lexprlist-count* x.elts)
                  (lexpr_desc-count* x))))
    :hints (("goal" :expand ((lexpr_desc-count* x))))
    :rule-classes :linear)

  (defthm lexpr-count*-lexpr->val
    (< (lexpr_desc-count* (lexpr->val x))
       (lexpr-count* x))
    :hints (("goal" :expand ((lexpr-count* x))))
    :rule-classes :linear)

  (defthm lexprlist-count*-strong
    (implies (consp x)
             (< (+ (lexpr-count* (car x))
                   (lexprlist-count* (cdr x)))
                (lexprlist-count* x)))
    :hints (("goal" :expand ((lexprlist-count* x))))
    :rule-classes :linear))


(defines expr_of_lexpr
  :ruler-extenders (expr)
  (define expr_of_lexpr ((x lexpr-p))
    :returns (res expr-p)
    :measure (lexpr-count x)
    :verify-guards nil
    (b* ((x (lexpr->val x)))
      (expr
       (lexpr_desc-case x
         :le_var (e_var x.name)
         :le_slice (e_slice (expr_of_lexpr x.base) x.slices)
         :le_setarray (e_getarray (expr_of_lexpr x.base) x.index)
         :le_setenumarray (e_getenumarray (expr_of_lexpr x.base) x.index)
         :le_setfield (e_getfield (expr_of_lexpr x.base) x.field)
         :le_setfields (e_getfields (expr_of_lexpr x.base) x.fields)
         :le_discard (e_var "-") ;; ??? i think this is supposed to be prevented by type safety
         :le_destructuring (e_tuple (exprlist_of_lexprlist x.elts))))))
  (define exprlist_of_lexprlist ((x lexprlist-p))
    :returns (res exprlist-p)
    :measure (lexprlist-count x)
    (if (atom x)
        nil
      (cons (expr_of_lexpr (car x))
            (exprlist_of_lexprlist (cdr x)))))
  ///
  (verify-guards expr_of_lexpr)

  (std::defret-mutual expr-count-of-<fn>
    (defret expr-count-of-<fn>
      (<= (expr-count (expr_of_lexpr x))
          (lexpr-count* x))
      :hints ('(:expand ((expr_of_lexpr x)
                         (lexpr-count* x)
                         (lexpr_desc-count* (lexpr->val x))
                         (:free (x) (expr-count (expr x)))
                         (:free (x) (expr_desc-count (e_var x)))
                         (:free (x y) (expr_desc-count (e_slice x y)))
                         (:free (x y) (expr_desc-count (e_getarray x y)))
                         (:free (x y) (expr_desc-count (e_getenumarray x y)))
                         (:free (x y) (expr_desc-count (e_getfield x y)))
                         (:free (x y) (expr_desc-count (e_getfields x y)))
                         (:free (x) (expr_desc-count (e_tuple x))))))
      :rule-classes :linear
      :fn expr_of_lexpr)
    (defret exprlist-count-of-<fn>
      (<= (exprlist-count (exprlist_of_lexprlist x))
          (lexprlist-count* x))
      :hints ('(:expand ((exprlist_of_lexprlist x)
                         (lexprlist-count* x)
                         (:free (x y) (exprlist-count (cons x y)))
                         (exprlist-count nil))))
      :rule-classes :linear
      :fn exprlist_of_lexprlist)))



(define maybe-expr-count ((x maybe-expr-p))
  :returns (count posp :rule-classes :type-prescription)
  (if x (+ 1 (expr-count x)) 1)
  ///
  (defthm maybe-expr-count-linear
    (implies x
             (< (expr-count x) (maybe-expr-count x)))
    :rule-classes :linear))

(define expr*maybe-ty-count ((x expr*maybe-ty-p))
  :returns (count posp :rule-classes :type-prescription)
  (b* (((expr*maybe-ty x)))
    (+ 1 (expr-count x.expr) (maybe-ty-count x.ty)))
  ///
  (defthm expr*maybe-ty-count-linear
    (b* (((expr*maybe-ty x)))
      (< (+ (expr-count x.expr) (maybe-ty-count x.ty))
         (expr*maybe-ty-count x)))
    :rule-classes :linear))

(define maybe-[expr*maybe-ty]-count ((x maybe-[expr*maybe-ty]-p))
  :returns (count posp :rule-classes :type-prescription)
  (if x (+ 1 (expr*maybe-ty-count x)) 1)
  ///
  (defthm maybe-[expr*maybe-ty]-count-linear
    (implies x
             (< (expr*maybe-ty-count x) (maybe-[expr*maybe-ty]-count x)))
    :rule-classes ((:linear :trigger-terms ((maybe-[expr*maybe-ty]-count x))))))


(defines stmt-count*
  :hints (("goal" :expand ((maybe-stmt-count x)
                           (maybe-stmt-some->val x))))
  (define stmt_desc-count* ((x stmt_desc-p))
    :measure (stmt_desc-count x)
    :returns (count posp :rule-classes :type-prescription)
    (stmt_desc-case x
      :s_seq (+ 1 (stmt-count* x.first)
                (stmt-count* x.second))
      :s_decl (+ 1
                 (maybe-ty-count x.ty)
                 (maybe-expr-count x.expr))
      :s_assign (+ 1 (lexpr-count* x.lexpr)
                   (expr-count x.expr))
      :s_call (+ 1 (call-count x.call))
      :s_return (+ 1 (maybe-expr-count x.expr))
      :s_cond (+ 1 (expr-count x.test)
                 (stmt-count* x.then)
                 (stmt-count* x.else))
      :s_assert (+ 1 (expr-count x.expr))
      :s_for (+ 1 (expr-count x.start_e)
                (expr-count x.end_e)
                (stmt-count* x.body)
                (maybe-expr-count x.limit))
      :s_while (+ 1 (expr-count x.test)
                  (maybe-expr-count x.limit)
                  (stmt-count* x.body))
      :s_repeat (+ 1 (stmt-count* x.body)
                   (expr-count x.test)
                   (maybe-expr-count x.limit))
      :s_throw (+ 1 (maybe-[expr*maybe-ty]-count x.val))
      :s_try (+ 1 (stmt-count* x.body)
                (catcherlist-count* x.catchers)
                (maybe-stmt-count* x.otherwise))
      :s_print (+ 1 (exprlist-count x.args))
      :s_pragma (+ 1 (exprlist-count x.exprs))
      :otherwise 1))

  (define stmt-count* ((x stmt-p))
    :measure (stmt-count x)
    :returns (count posp :rule-classes :type-prescription)
    (+ 1 (stmt_desc-count* (stmt->val x))))

  (define maybe-stmt-count* ((x maybe-stmt-p))
    :measure (maybe-stmt-count x)
    :returns (count posp :rule-classes :type-prescription)
    (if x (+ 1 (stmt-count* x)) 1))

  (define catcher-count* ((x catcher-p))
    :measure (catcher-count x)
    :returns (count posp :rule-classes :type-prescription)
    (b* (((catcher x)))
      (+ 1 (ty-count x.ty) (stmt-count* x.stmt))))

  (define catcherlist-count* ((x catcherlist-p))
    :measure (catcherlist-count x)
    :returns (count posp :rule-classes :type-prescription)
    (if (atom x)
        1
      (+ 1 (catcher-count* (car x))
         (catcherlist-count* (cdr x)))))
  ///
  (local (set-default-hints
          '('(:expand ((stmt_desc-count* x)
                       (stmt-count* x)
                       (maybe-stmt-count* x)
                       (catcher-count* x)
                       (catcherlist-count* x))))))

  (local (in-theory (disable stmt_desc-count*
                             stmt-count*
                             maybe-stmt-count*
                             catcherlist-count*
                             catcher-count*)))
  
  (defthm stmt_desc-count*-s_seq
    (implies (stmt_desc-case x :s_seq)
             (b* (((s_seq x)))
               (< (+ (stmt-count* x.first)
                     (stmt-count* x.second))
                  (stmt_desc-count* x))))
    :rule-classes :linear)

  (defthm stmt_desc-count*-s_decl
    (implies (stmt_desc-case x :s_decl)
             (b* (((s_decl x)))
               (< (+ (maybe-ty-count x.ty)
                 (maybe-expr-count x.expr))
                  (stmt_desc-count* x))))
    :rule-classes :linear)

  (defthm stmt_desc-count*-s_assign
    (implies (stmt_desc-case x :s_assign)
             (b* (((s_assign x)))
               (< (+ (lexpr-count* x.lexpr)
                     (expr-count x.expr))
                  (stmt_desc-count* x))))
    :rule-classes :linear)

  (defthm stmt_desc-count*-s_call
    (implies (stmt_desc-case x :s_call)
             (b* (((s_call x)))
               (< (call-count x.call)
                  (stmt_desc-count* x))))
    :rule-classes :linear)

  (defthm stmt_desc-count*-s_return
    (implies (stmt_desc-case x :s_return)
             (b* (((s_return x)))
               (< (maybe-expr-count x.expr)
                  (stmt_desc-count* x))))
    :rule-classes :linear)

  (defthm stmt_desc-count*-s_cond
    (implies (stmt_desc-case x :s_cond)
             (b* (((s_cond x)))
               (< (+ (expr-count x.test)
                     (stmt-count* x.then)
                     (stmt-count* x.else))
                  (stmt_desc-count* x))))
    :rule-classes :linear)

  (defthm stmt_desc-count*-s_assert
    (implies (stmt_desc-case x :s_assert)
             (b* (((s_assert x)))
               (< (expr-count x.expr)
                  (stmt_desc-count* x))))
    :rule-classes :linear)

  (defthm stmt_desc-count*-s_for
    (implies (stmt_desc-case x :s_for)
             (b* (((s_for x)))
               (< (+ (expr-count x.start_e)
                     (expr-count x.end_e)
                     (stmt-count* x.body)
                     (maybe-expr-count x.limit))
                  (stmt_desc-count* x))))
    :rule-classes :linear)

  (defthm stmt_desc-count*-s_while
    (implies (stmt_desc-case x :s_while)
             (b* (((s_while x)))
               (< (+ (expr-count x.test)
                     (maybe-expr-count x.limit)
                     (stmt-count* x.body))
                  (stmt_desc-count* x))))
    :rule-classes :linear)

  (defthm stmt_desc-count*-s_repeat
    (implies (stmt_desc-case x :s_repeat)
             (b* (((s_repeat x)))
               (< (+ (stmt-count* x.body)
                     (expr-count x.test)
                     (maybe-expr-count x.limit))
                  (stmt_desc-count* x))))
    :rule-classes :linear)

  (defthm stmt_desc-count*-s_throw
    (implies (stmt_desc-case x :s_throw)
             (b* (((s_throw x)))
               (< (maybe-[expr*maybe-ty]-count x.val)
                  (stmt_desc-count* x))))
    :rule-classes :linear)
  
  (defthm stmt_desc-count*-s_try
    (implies (stmt_desc-case x :s_try)
             (b* (((s_try x)))
               (< (+ (stmt-count* x.body)
                     (catcherlist-count* x.catchers)
                     (maybe-stmt-count* x.otherwise))
                  (stmt_desc-count* x))))
    :rule-classes :linear)

  (defthm stmt_desc-count*-s_print
    (implies (stmt_desc-case x :s_print)
             (b* (((s_print x)))
               (< (exprlist-count x.args)
                  (stmt_desc-count* x))))
    :rule-classes :linear)

  (defthm stmt_desc-count*-s_pragma
    (implies (stmt_desc-case x :s_pragma)
             (b* (((s_pragma x)))
               (< (exprlist-count x.exprs)
                  (stmt_desc-count* x))))
    :rule-classes :linear)

  (defthm stmt-count*-linear
    (< (stmt_desc-count* (stmt->val x)) (stmt-count* x))
    :rule-classes :linear)

  (defthm maybe-stmt-count*-linear
    (implies x
             (< (stmt-count* x) (maybe-stmt-count* x)))
    :rule-classes ((:linear :trigger-terms ((maybe-stmt-count* x)))))

  (defthm catcher-count*-linear
    (b* (((catcher x)))
      (< (+ (ty-count x.ty) (stmt-count* x.stmt)) (catcher-count* x)))
    :rule-classes :linear)

  (defthm catcherlist-count*-linear
    (implies (consp x)
             (< (+ (catcher-count* (car x))
                   (catcherlist-count* (cdr x)))
                (catcherlist-count* x)))
    :rule-classes :linear))



(defconst *recursion-limit-upper-bound* (expt 2 40))


(define env-clk-sum-stack-size ((subs func-ses-imap-p)
                                (stk int-imap-p))
  :returns (clk natp :rule-classes :type-prescription)
  (b* (((when (atom subs)) 0)
       ((unless (mbt (and (consp (car subs))
                          (identifier-p (caar subs)))))
        (env-clk-sum-stack-size (cdr subs) stk))
       (fn (caar subs))
       (look (assoc-equal fn stk))
       (val (nfix (- *recursion-limit-upper-bound* (if look (cdr look) 0)))))
    (+ val (env-clk-sum-stack-size (cdr subs) stk))))

(define env-clk ((env env-p))
  :returns (clk natp :rule-classes :type-prescription)
  (b* (((env env))
       ((global-env g) env.global)
       ((static_env_global s) g.static))
    (env-clk-sum-stack-size s.subprograms g.stack_size)))


(def-eval_result env_eval_result-p env-p)

(define env-push-stack ((name identifier-p)
                        (env env-p))
  :returns (new-env env_eval_result-p)
  (b* (((env env))
       ((global-env g) env.global)
       ((static_env_global s) g.static)
       (name (identifier-fix name))
       (look (assoc-equal name s.subprograms))
       ((unless look)
        (ev_error "Unrecognized subprogram" name))
       (look (assoc-equal name g.stack_size))
       (val (lifix (if look (cdr look) 0)))
       ((when (<= *recursion-limit-upper-bound* val))
        (ev_error "Recursion limit overflowed" name))
       (new-g (change-global-env g :stack_size (cons (cons name (+ 1 val)) g.stack_size))))
    (ev_normal (make-env :global new-g :local (empty-local-env))))

  ;; ///
  ;; (local (defthm integerp-+-1
  ;;          (implies (integerp x)
  ;;                   (integerp (+ 1 x)))))

  ;; (local (defthm integerp-minus
  ;;          (implies (and (integerp x) (integerp y))
  ;;                   (integerp (+ x (- y))))))

  ;; (local (defthm env-clk-sum-stack-size-decr-1
  ;;          (implies (and (int-imap-p stack_size)
  ;;                        (hons-assoc-equal name stack_size))
  ;;                   (and (implies (and (hons-assoc-equal name subprograms)
  ;;                                      (identifier-p name)
  ;;                                      (< (cdr (hons-assoc-equal name stack_size))
  ;;                                         *recursion-limit-upper-bound*))
  ;;                                 (< (env-clk-sum-stack-size subprograms (cons (cons name (+ 1 (cdr (hons-assoc-equal name stack_size))))
  ;;                                                                              stack_size))
  ;;                                    (env-clk-sum-stack-size subprograms stack_size)))
  ;;                        (<= (env-clk-sum-stack-size subprograms (cons (cons name (+ 1 (cdr (hons-assoc-equal name stack_size))))
  ;;                                                                      stack_size))
  ;;                            (env-clk-sum-stack-size subprograms stack_size))))
  ;;          :hints(("Goal" :in-theory (enable env-clk-sum-stack-size)))
  ;;          :rule-classes :linear))

  ;; (local (defthm env-clk-sum-stack-size-decr-2
  ;;          (implies (not (hons-assoc-equal name stack_size))
  ;;                   (and (implies (and (hons-assoc-equal name subprograms)
  ;;                                      (identifier-p name))
  ;;                                 (< (env-clk-sum-stack-size subprograms (cons (cons name 1) stack_size))
  ;;                                    (env-clk-sum-stack-size subprograms stack_size)))
  ;;                        (<= (env-clk-sum-stack-size subprograms (cons (cons name 1) stack_size))
  ;;                            (env-clk-sum-stack-size subprograms stack_size))))
  ;;          :hints(("Goal" :in-theory (enable env-clk-sum-stack-size)))
  ;;          :rule-classes :linear))

  ;; (defret env-push-stack-env-clk-decr
  ;;   (implies (eval_result-case new-env :ev_normal)
  ;;            (< (env-clk (ev_normal->res new-env)) (env-clk env)))
  ;;   :hints(("Goal" :in-theory (enable env-clk))))
  )

(define env-pop-stack ((name identifier-p)
                       (prev-env env-p)
                       (call-env global-env-p))
  :returns (new-env env-p)
  ;; Takes the local component of the prev-env
  ;; and combines it with the global component of the call-env, but decrements name's stack size.
  (b* (((env call) call-env)
       ((global-env g) call-env)
       (look (assoc-equal name g.stack_size))
       (val (lifix (if look (cdr look) 0)))
       (new-g (change-global-env g :stack_size (cons (cons name (- val 1)) g.stack_size))))
    (change-env prev-env :global new-g)))

  


(defmacro nats-measure (&rest args)
  `(acl2::nat-list-measure (list . ,args)))


(define read_value_from ((vs val_read_from-list-p))
  :returns (vals vallist-p)
  (if (atom vs)
      nil
    (cons (val_read_from->val (car vs))
          (read_value_from (cdr vs)))))



(define typed_identifierlist->names ((x typed_identifierlist-p))
  :returns (names identifierlist-p)
  (if (atom x)
      nil
    (cons (typed_identifier->name (car x))
          (typed_identifierlist->names (cdr x))))
  ///
  (defret len-of-<fn>
    (equal (len names) (len x))))

(define maybe-typed_identifierlist->names ((x maybe-typed_identifierlist-p))
  :returns (names identifierlist-p)
  (if (atom x)
      nil
    (cons (maybe-typed_identifier->name (car x))
          (maybe-typed_identifierlist->names (cdr x))))
  ///
  (defret len-of-<fn>
    (equal (len names) (len x))))


(define declare_local_identifier ((env env-p)
                                  (name identifier-p)
                                  (val val-p))
  :returns (new-env env-p)
  (b* (((env env))
       ((local-env l) env.local)
       (new-storage (cons (cons (identifier-fix name) (val-fix val))
                          l.storage)))
    (change-env env :local (change-local-env l :storage new-storage))))

(define remove_local_identifier ((env env-p)
                                 (name identifier-p))
  :returns (new-env env-p)
  (b* (((env env))
       ((local-env l) env.local)
       (new-storage (remove-assoc-equal (identifier-fix name) l.storage)))
    (change-env env :local (change-local-env l :storage new-storage))))

(define declare_local_identifiers ((env env-p)
                                   (names identifierlist-p)
                                   (vals vallist-p))
  :guard (eql (len names) (len vals))
  :returns (new-env env-p)
  (b* (((env env))
       ((local-env l) env.local)
       (new-storage (append (pairlis$ (identifierlist-fix names)
                                      (mbe :logic (vallist-fix (take (len names) vals))
                                           :exec vals))
                            l.storage)))
    (change-env env :local (change-local-env l :storage new-storage))))



(define check_recurse_limit ((env env-p)
                             (name identifier-p)
                             (recurse-limit maybe-expr-p))
  :returns (eval eval_result-p)
  (declare (ignorable env name recurse-limit))
  (ev_normal nil))


(defthm call-count-linear
  (b* (((call x)))
    (< (+ (exprlist-count x.params)
          (exprlist-count x.args))
       (call-count x)))
  :hints(("Goal" :in-theory (enable call-count)))
  :rule-classes :linear)


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

(local
 (defthm nth-of-vallist
   (implies (and
             (vallist-p l)
             (<= 0 idx)
             (< idx (len l)))
            (val-p (nth idx l)))))


(define fieldlist->exprs ((x fieldlist-p))
  :returns (exprs exprlist-p)
  (if (atom x)
      nil
    (cons (field->expr (car x))
          (fieldlist->exprs (cdr x))))
  ///
  (defret len-of-<fn>
    (equal (len exprs) (len x)))

  (defret exprlist-count-of-<fn>
    (<= (exprlist-count (fieldlist->exprs x))
        (fieldlist-count x))
    :hints(("Goal" :in-theory (enable fieldlist-count exprlist-count)))
    :rule-classes :linear))

(define fieldlist->names ((x fieldlist-p))
  :returns (names identifierlist-p)
  (if (atom x)
      nil
    (cons (field->name (car x))
          (fieldlist->names (cdr x))))
  ///
  (defret len-of-<fn>
    (equal (len names) (len x))))






(def-eval_result int_eval_result-p integerp)

(define v_to_int ((x val-p))
  :returns (i int_eval_result-p)
  (val-case x
    :v_int (ev_normal x.val)
    :otherwise (ev_error "v_to_int bad type" x)))

(def-eval_result bool_eval_result-p booleanp)

(define v_to_bool ((x val-p))
  :returns (i bool_eval_result-p)
  (val-case x
    :v_bool (ev_normal x.val)
    :otherwise (ev_error "v_to_bool bad type" x)))

(def-eval_result id_eval_result-p identifier-p)

(define v_to_label ((x val-p))
  :returns (i id_eval_result-p)
  (val-case x
    :v_label (ev_normal x.val)
    :otherwise (ev_error "v_to_label bad type" x)))

(local (defthm rationalp-when-integerp-rw
         (implies (integerp x)
                  (rationalp x))))



(define get_field! ((field identifier-p)
                    (rec val-imap-p))
  :returns (v val_result-p)
  (b* ((look (assoc-equal (identifier-fix field)
                          (val-imap-fix rec)))
       ((unless look) (ev_error "get_field not found" field)))
    (ev_normal (cdr look))))

(define get_field ((field identifier-p)
                   (rec val-p))
  :returns (v val_result-p)
  (val-case rec
    :v_record (get_field! field rec.rec)
    :otherwise (ev_error "get_field non record" rec)))

(define map-get_field! ((fields identifierlist-p)
                        (rec val-imap-p))
  :returns (v vallist_result-p)
  (b* (((when (atom fields)) (ev_normal nil))
       ((ev val1) (get_field! (car fields) rec))
       ((ev rest) (map-get_field! (cdr fields) rec)))
    (ev_normal (cons val1 rest))))

(define map-get_field ((fields identifierlist-p)
                       (rec val-p))
  :returns (v vallist_result-p)
  (val-case rec
    :v_record (map-get_field! fields rec.rec)
    :otherwise (ev_error "map-get_field non record" rec)))

(define concat_bitvectors ((vals vallist-p))
  ;; Check order?
  :returns (v val_result-p)
  :verify-guards nil
  (B* (((when (atom vals))
        (ev_normal (v_bitvector 0 0)))
       ((ev (v_bitvector rest)) (concat_bitvectors (cdr vals)))
       (v1 (car vals)))
    (val-case v1
      :v_bitvector (ev_normal
                    (v_bitvector (+ v1.len rest.len)
                                 (logapp rest.len rest.val v1.val)))
      :otherwise (ev_error "concat_bitvectors non bitvector" v1)))
  ///
  (defret kind-of-<fn>
    (implies (eval_result-case v :ev_normal)
             (equal (val-kind (ev_normal->res v))
                    :v_bitvector)))
  
  (verify-guards concat_bitvectors))

(local (in-theory (disable loghead logtail)))

(define bitvec_fields_to_record! ((fields identifierlist-p)
                                  (slices intpairlist-p)
                                  (rec val-imap-p)
                                  (bv integerp)
                                  (width acl2::maybe-integerp))
  :guard (eql (len fields) (len slices))
  :returns (v val_result-p)
  (b* (((when (atom fields)) (ev_normal (v_record rec)))
       (field (identifier-fix (car fields)))
       ((unless (assoc-equal field (val-imap-fix rec)))
        (ev_error "bitvec_fields_to_record!: field not in record" field))
       ((intpair s) (car slices))
       (start s.first)
       (length s.second)
       ((unless (and (<= 0 start)
                     (<= 0 length)
                     (or (not width)
                         (<= (+ start length) width))))
        (ev_error "bitvec_fields_to_record!: out of bounds slice" (car slices)))
       (fieldval (loghead length (logtail start bv)))
       (new-rec (put-assoc-equal field (v_bitvector length fieldval) (val-imap-fix rec))))
    (bitvec_fields_to_record! (cdr fields) (cdr slices) new-rec bv width)))
       
       

(define bitvec_fields_to_record ((fields identifierlist-p)
                                 (slices intpairlist-p)
                                 (rec val-p)
                                 (bv val-p))
  :guard (eql (len fields) (len slices))
  :returns (v val_result-p)
  (b* (((unless (val-case rec :v_record))
        (ev_error "bitvec_fields_to_record non record" rec))
       ((unless (or (val-case bv :v_bitvector)
                    (val-case bv :v_int)))
        (ev_error "bitvec_fields_to_record non bitvec/integer" bv))
       ((v_record rec))
       ((mv bv-val bv-len) (val-case bv
                             :v_bitvector (mv bv.val bv.len)
                             :otherwise (mv (v_int->val bv) nil))))
    (bitvec_fields_to_record! fields slices rec.rec bv-val bv-len)))
       

(define for_loop-test ((v_start integerp)
                       (v_end integerp)
                       (dir for_direction-p))
  ;; says whether we terminate
  (if (eq (for_direction-fix dir) :up)
      (< (lifix v_end) (lifix v_start))
    (> (lifix v_end) (lifix v_start))))

(define for_loop-measure ((v_start integerp)
                          (v_end integerp)
                          (dir for_direction-p))
  :returns (meas natp :rule-classes :type-prescription)
  (nfix (+ 3 (if (eq (for_direction-fix dir) :up)
                 (- (lifix v_end) (lifix v_start))
               (- (lifix v_start) (lifix v_end)))))
  ///
  (defthm for_loop-measure-when-not-test
    (implies (not (for_loop-test v_start v_end dir))
             (<= 2 (for_loop-measure v_start v_end dir)))
    :hints(("Goal" :in-theory (enable for_loop-test)))
    :rule-classes :linear))



(define for_loop-step ((v_start integerp)
                       (dir for_direction-p))
  ;; says whether we terminate
  (+ (lifix v_start)
     (if (eq (for_direction-fix dir) :up) 1 -1))
  ///
  (defthm for_loop-step-decreases-measure
    (implies (not (for_loop-test v_start v_end dir))
             (< (for_loop-measure (for_loop-step v_start dir) v_end dir)
                (for_loop-measure v_start v_end dir)))
    :hints(("Goal" :in-theory (e/d (for_loop-measure
                                    for_loop-test))))
    :otf-flg t
    :rule-classes :linear))

  


(define eval_for_step ((env env-p)
                       (index_name identifier-p)
                       ;; missing limit
                       (v_start integerp)
                       (dir for_direction-p))
  :returns (mv (v_step integerp)
               (new-env env-p))
  (b* ((v_step (for_loop-step v_start dir)))
    (mv v_step (env-assign-local index_name (v_int v_step) env)))
  ///
  (defret v_step-of-eval_for_step
    (equal v_step
           (for_loop-step v_start dir))))


(define pop_scope ((parent env-p)
                   (child env-p))
  :Returns (new-env env-p)
  :prepwork ((local (include-book "std/alists/hons-assoc-equal" :dir :system))
             (local (defthm fal-extract-of-val-imap
                      (implies (val-imap-p x)
                               (val-imap-p (acl2::fal-extract keys x)))
                      :hints(("Goal" :in-theory (enable acl2::fal-extract))))))
  (b* (((env child))
       ((env parent))
       ((local-env parent.local))
       ((local-env child.local))
       (dom (acl2::alist-keys parent.local.storage)))
    (change-env child
                :local
                (change-local-env child.local
                                  :storage (acl2::fal-extract dom child.local.storage)))))



;;substitute slices from srcval to dstval
(define slice_sub ((srcval integerp)
                   (vslice intpair-p)
                   (dstval integerp))
  :returns (val (implies val (integerp val)))

    (b* (((intpair vslice))
         (start vslice.first)
         (len   vslice.second)
         (srcpart (bitops::part-select srcval :low (nfix start) :width (nfix len)))
         )
      (bitops::part-install srcpart dstval :low (nfix start) :width (nfix len)))
      )

(define slices_sub ((srcval  integerp)
                    (vslices intpairlist-p)
                    (dstval  integerp))
  :returns (resval (implies resval (integerp resval)))
                
  :guard-debug t
  (if (atom vslices) (ifix dstval)
    (b* ((first (car vslices))
         (rest  (cdr vslices))
         (new_dstval (slice_sub srcval first dstval))
         ((unless new_dstval) nil))
      (slices_sub srcval rest new_dstval))))

(defprod intpair/env
  ((pair intpair-p)
   (env  env-p))
  :layout :fulltree)

(def-eval_result slice_eval_result-p intpair/env-p)

(defprod intpairlist/env
  ((pairlist intpairlist-p)
   (env  env-p))
  :layout :fulltree)

(def-eval_result slices_eval_result-p intpairlist/env-p)

(with-output
  ;; makes it so it won't take forever to print the induction scheme
  :evisc (:gag-mode (evisc-tuple 3 4 nil nil))
  :off (event)
  (defines eval_expr
    (define eval_expr ((env env-p)
                       (e expr-p)
                       &key
                       ((clk natp) 'clk))
      :verify-guards nil
      :returns (eval expr_eval_result-p)
      :measure (nats-measure clk 0 (expr-count e) 0)
      (b* ((desc (expr->desc e)))
        (expr_desc-case desc
          :e_literal (ev_normal (expr_result (v_of_literal desc.val) env)) ;; SemanticsRule.ELit
          :e_var (b* ((look (env-find desc.name env)))
                   (env_result-case look
                     :lk_local (ev_normal (expr_result look.val env))
                     :lk_global (ev_normal (expr_result look.val env))
                     :lk_notfound (ev_error "Variable not found" desc))) ;; SemanticsRule.EVar
          :e_pattern (let**
                      (((expr_result v1) (eval_expr env desc.expr))
                       (val (eval_pattern v1.env v1.val desc.pattern)))
                      (ev_normal (expr_result val v1.env)))
          :e_unop ;; anna
          (let**
           (((expr_result v) (eval_expr env desc.arg))
            (val (eval_unop desc.op v.val))) ;;SemanticsRule.Unop
           (ev_normal (expr_result val v.env)))
          :e_binop ;;
          (b* (((ev (expr_result v1)) (eval_expr env desc.arg1))
               ((ev (expr_result v2)) (eval_expr v1.env desc.arg2))
               ((ev val) (eval_binop desc.op v1.val v2.val)))
            (ev_normal (expr_result val v2.env)))
          :e_call ;; sol
          (b* (((call c) desc.call)
               ((ev (exprlist_result e))
                (eval_call c.name env c.params c.args))
               (v (if (and (consp e.val)
                           (atom (cdr e.val)))
                      (car e.val)
                    (v_array e.val))))
            (ev_normal (expr_result v e.env)))
          :e_slice ;; anna
          (b* (((ev (expr_result vexpr)) (eval_expr env desc.expr))
               ((ev (intpairlist/env vslices)) (eval_slice_list vexpr.env desc.slices))
               (srcval vexpr.val)
               )
            (val-case srcval
              :v_int (b* ((res (slices_sub srcval.val vslices.pairlist 0)))
                       (if res (ev_normal (expr_result (v_int res) vslices.env))
                         (ev_error "Error in evaluation of e_slice" desc)))
              :v_bitvector (b* ((res (slices_sub srcval.val vslices.pairlist 0))
                                (len srcval.len))
                             (if res (ev_normal (expr_result
                                                 (v_bitvector len (loghead len res))
                                                 vslices.env))
                               (ev_error "Error in evaluation of e_slice" desc)))
              :otherwise (ev_error "Unexpected result of evaluation of desc.expr" desc)))
          :e_cond  ;; anna
          (let**
           (((expr_result test) (eval_expr env desc.test))
            (choice (val-case test.val
                      :v_bool (ev_normal (if test.val.val desc.then desc.else))
                      :otherwise (ev_error "bad test in e_cond" test.val))))
           (eval_expr test.env choice))
          :e_getarray ;; sol
          (b* (((ev (expr_result arr)) (eval_expr env desc.base))
               ((ev (expr_result idx)) (eval_expr arr.env desc.index))
               ((ev idxv) (val-case idx.val
                            :v_int (ev_normal idx.val.val)
                            :otherwise (ev_error "getarray non-integer index" desc)))
               ((ev arrv) (val-case arr.val
                            :v_array (ev_normal arr.val.arr)
                            :otherwise (ev_error "getarray non-array value" desc))))
            (if (and (<= 0 idxv)
                     (< idxv (len arrv)))
                (ev_normal (expr_result (nth idxv arrv) idx.env))
              (ev_error "getarray index out of range" desc)))
          :e_getenumarray ;; sol
          (b* (((ev (expr_result arr)) (eval_expr env desc.base))
               ((ev (expr_result idx)) (eval_expr arr.env desc.index))
               ((ev idxv) (val-case idx.val
                            :v_label (ev_normal idx.val.val)
                            :otherwise (ev_error "getenumarray non-label index" desc)))
               ((ev arrv) (val-case arr.val
                            :v_record (ev_normal arr.val.rec)
                            :otherwise (ev_error "getenumarray non-record value" desc)))
               (look (assoc-equal idxv arrv)))
            (if look
                (ev_normal (expr_result (cdr look) idx.env))
              (ev_error "getenumarray index not found" desc)))
          :e_getfield ;; anna
          (ev_error "Unsupported expression" desc)
          :e_getfields ;; sol
          (b* (((ev (expr_result recres)) (eval_expr env desc.base))
               ((ev fieldvals) (map-get_field desc.fields recres.val))
               ((ev val) (concat_bitvectors fieldvals)))
            (ev_normal (expr_result val recres.env)))
          :e_getitem ;; anna
          (let**
           (((expr_result varr) (eval_expr env desc.base)))
           (val-case varr.val
             :v_array (if (or (< desc.index 0) (<= (len varr.val.arr) desc.index))
                          (ev_error "index out of bounds" desc)
                        (ev_normal (expr_result (nth desc.index varr.val.arr) varr.env)))
             :otherwise (ev_error "evaluation of the base did not return v_array as expected" desc)))
          :e_record ;; sol
          (b* ((exprs (fieldlist->exprs desc.fields))
               (names (fieldlist->names desc.fields))
               ((ev (exprlist_result e)) (eval_expr_list env exprs)))
            (ev_normal (expr_result (v_record (pairlis$ names e.val)) e.env)))
          :e_tuple ;; anna
          (let**
           (((exprlist_result vals) (eval_expr_list env desc.exprs)))
           (ev_normal (expr_result (v_array vals.val) vals.env)))
          :e_array ;; sol
          (b* (((ev (expr_result v)) (eval_expr env desc.value))
               ((ev (expr_result len)) (eval_expr v.env desc.length))
               ((ev lenv) (val-case len.val
                            :v_int (if (<= 0 len.val.val)
                                       (ev_normal len.val.val)
                                     (ev_error "array negative length" desc))
                            :otherwise (ev_error "array non-integer length" desc))))
            (ev_normal (expr_result (v_array (make-list lenv :initial-element v.val)) len.env)))
          :e_enumarray ;; anna
          (ev_error "Unsupported expression" desc)
          :e_arbitrary ;; sol
          (ev_error "Unsupported expression" desc)
          :otherwise (ev_error "Unsupported expression" desc))))

    (define eval_pattern ((env env-p)
                          (val val-p)
                          (p pattern-p)
                          &key
                          ((clk natp) 'clk))
      :measure (nats-measure clk 0 (pattern-count p) 0)
      ;; :returns (val val-p)
      ;; Note: this isn't supposed to produce any side effects so we'll omit
      ;; the environment and just return the value
      :returns (eval val_result-p)
      (b* ((desc (pattern->val p)))
        (pattern_desc-case desc
          :pattern_all (ev_normal (v_bool t)) ;; SemanticsRule.PAll
          :pattern_any (eval_pattern-any env val desc.patterns)
          :pattern_geq (b* (((ev (expr_result v1)) (eval_expr env desc.expr)))
                         (eval_binop :geq val v1.val))
          :pattern_leq (b* (((ev (expr_result v1)) (eval_expr env desc.expr)))
                         (eval_binop :leq val v1.val))
          :pattern_mask (ev_error "Unsupported pattern" desc)
          :pattern_not (b* (((ev v1) (eval_pattern env val desc.pattern)))
                         (eval_unop :bnot v1))
          :pattern_range (b* (((ev (expr_result v1)) (eval_expr env desc.lower))
                              ((ev (expr_result v2)) (eval_expr env desc.upper))
                              ((ev lower) (eval_binop :geq val v1.val))
                              ((ev upper) (eval_binop :leq val v2.val)))
                           (eval_binop :band lower upper))
          :pattern_single (b* (((ev (expr_result v1)) (eval_expr env desc.expr)))
                            (eval_binop :eq_op val v1.val))
          :pattern_tuple (b* ((len (len desc.patterns))
                              ((ev vs) (val-case val
                                         :v_array (if (eql (len val.arr) len)
                                                      (ev_normal val.arr)
                                                    (ev_error "pattern tuple length mismatch" p))
                                         :otherwise (ev_error "pattern tuple type mismatch" p))))
                           (eval_pattern_tuple env vs desc.patterns)))))

    (define eval_pattern_tuple ((env env-p)
                                (vals vallist-p)
                                (p patternlist-p)
                                &key
                                ((clk natp) 'clk))
      :guard (eql (len vals) (len p))
      :measure (nats-measure clk 0 (patternlist-count p) 0)
      :returns (eval val_result-p)
      (b* (((when (atom p)) (ev_normal (v_bool t)))
           ((ev first) (eval_pattern env (car vals) (car p)))
           ;; short circuit?
           ((when (val-case first :v_bool (not first.val) :otherwise nil))
            (ev_normal first))
           ((ev rest) (eval_pattern_tuple env (cdr vals) (cdr p))))
        (eval_binop :band first rest)))
        
    
    (define eval_pattern-any ((env env-p)
                              (val val-p)
                              (p patternlist-p)
                              &key
                              ((clk natp) 'clk))
      :measure (nats-measure clk 0 (patternlist-count p) 0)

      :returns (eval val_result-p)
      (if (atom p)
          (ev_normal (v_bool nil))
        (let**
         ((v1 (eval_pattern env val (car p))))
         (val-case v1
           :v_bool (if v1.val
                       (ev_normal v1)
                     (eval_pattern-any env val (cdr p)))
           :otherwise (ev_error "Bad result type from eval_pattern" v1)))))


    (define eval_expr_list ((env env-p)
                            (e exprlist-p)
                            &key
                            ((clk natp) 'clk))
      :returns (eval exprlist_eval_result-p)
      :measure (nats-measure clk 0 (exprlist-count e) 0)
      (b* (((when (atom e))
            (ev_normal (exprlist_result nil env)))
           ((ev (expr_result first)) (eval_expr env (car e)))
           (env first.env)
           ((ev (exprlist_result rest)) (eval_expr_list env (cdr e))))
        (ev_normal (exprlist_result (cons first.val rest.val) rest.env))))
  
    (define eval_call ((name identifier-p)
                       (env env-p)
                       (params exprlist-p)
                       (args exprlist-p)
                       &key
                       ((clk natp) 'clk))
      :measure (nats-measure clk 0 (+ (exprlist-count params)
                                      (exprlist-count args)) 0)
      :returns (eval exprlist_eval_result-p)
      (b* (((ev (exprlist_result vargs)) (eval_expr_list env args))
           ((ev (exprlist_result vparams)) (eval_expr_list vargs.env params))
           (env vparams.env)
           ;; note: we check our fixed recursion limit here because this is where
           ;; the measure will decrease provided that they haven't been exceeded
           ((ev sub-env) (env-push-stack name env))
           ((when (zp clk))
            (ev_error "Recursion limit ran out" name))
           ((ev (func_result subprog-eval)) (eval_subprogram sub-env name vparams.val vargs.val :clk (1- clk)))
           ;; (vals (read_value_from subprog-eval.val))
           (env (env-pop-stack name env subprog-eval.env)))
        (ev_normal (exprlist_result subprog-eval.vals env))))

    (define eval_subprogram ((env env-p)
                             (name identifier-p)
                             (vparams vallist-p)
                             (vargs vallist-p)
                             &key
                             ((clk natp) 'clk))
      :measure (nats-measure clk 1 0 0)
      :returns (eval func_eval_result-p)
      (b* ((look (assoc-equal (identifier-fix name)
                              (static_env_global->subprograms
                               (global-env->static
                                (env->global env)))))
           ((unless look)
            (ev_error "Subprogam not found" name))
           ((func f) (func-ses->fn (cdr look)))
           ((unless (subprogram_body-case f.body :sb_asl))
            (ev_error "Primitive subfunctions not supported" name))

           ((unless (and (eql (len vparams) (len f.parameters))
                         (eql (len vargs) (len f.args))))
            (ev_error "Bad arity" (list name (len vparams) (len vargs))))
         
           ;; probably redundant but in the document
           (env1 (change-env env :local (empty-local-env)))
           ((ev ?ign) (check_recurse_limit env1 name f.recurse_limit))

           (arg-names (typed_identifierlist->names f.args))
           (param-names (maybe-typed_identifierlist->names f.parameters))
           (env2 (declare_local_identifiers env1 arg-names vargs))
           (env3 (declare_local_identifiers env2 param-names vparams))

           ((ev bodyres) (eval_stmt env3 (sb_asl->stmt f.body))))
        (control_flow_state-case bodyres
          :returning (ev_normal (func_result bodyres.vals bodyres.env))
          :continuing (ev_normal (func_result nil (env->global bodyres.env))))))


    (define eval_lexpr ((env env-p)
                        (lx lexpr-p)
                        (v val-p)
                        &key
                        ((clk natp) 'clk))
      :returns (eval env_eval_result-p)
      :measure (nats-measure clk 0 (lexpr-count* lx) 0)
      (b* ((lx (lexpr->val lx)))
        (lexpr_desc-case lx
          :le_discard (ev_normal (env-fix env))
          :le_var (b* ((envres (env-assign lx.name v env)))
                    (env_result-case envres
                      :lk_local (ev_normal envres.val)
                      :lk_global (ev_normal envres.val)
                      :lk_notfound (ev_error "assign to undeclared variable" lx)))
          :le_slice ;; (b* ((rbase (expr_of_lexpr lx.base))
                    ;;      ((ev (expr_result rbv)) (eval_expr env rbase))
          (ev_error "unimplemented lexpr" lx)
          :le_setarray (b* ((rbase (expr_of_lexpr lx.base))
                            ((ev (expr_result rbv)) (eval_expr env rbase))
                            ((ev (expr_result idx)) (eval_expr rbv.env lx.index))
                            ((ev idxv) (v_to_int idx.val))
                            ((ev newarray)
                             (val-case rbv.val
                               :v_array (if (and (<= 0 idxv)
                                                 (< idxv (len rbv.val.arr)))
                                            (ev_normal (v_array (update-nth idxv v rbv.val.arr)))
                                          (ev_error "le_setarray index out of obunds" lx))
                               :otherwise (ev_error "le_setarray non array base" lx))))
                         (eval_lexpr idx.env lx.base newarray))
          :le_setenumarray (b* ((rbase (expr_of_lexpr lx.base))
                                ((ev (expr_result rbv)) (eval_expr env rbase))
                                ((ev (expr_result idx)) (eval_expr rbv.env lx.index))
                                ((ev idxv) (v_to_label idx.val))
                                ((ev newarray)
                                 (val-case rbv.val
                                   :v_record (if (assoc-equal idxv rbv.val.rec)
                                                 (ev_normal (v_record (put-assoc-equal idxv v rbv.val.rec)))
                                               (ev_error "le_setenumarray unrecognized index" lx))
                                   :otherwise (ev_error "le_setenumarray non record base" lx))))
                             (eval_lexpr idx.env lx.base newarray))
          :le_setfield (b* ((rbase (expr_of_lexpr lx.base))
                            ((ev (expr_result rbv)) (eval_expr env rbase))
                            ((ev newrec)
                             (val-case rbv.val
                               :v_record (if (assoc-equal lx.field rbv.val.rec)
                                             (ev_normal (v_record (put-assoc-equal lx.field v rbv.val.rec)))
                                           (ev_error "le_setfield unrecognized field" lx))
                               :otherwise (ev_error "le_setfield non record base" lx))))
                         (eval_lexpr rbv.env lx.base newrec))
          :le_setfields (b* (((when (not (eql (len lx.fields) (len lx.pairs))))
                              (ev_error "le_setfields length mismatch" lx))
                             (rbase (expr_of_lexpr lx.base))
                             ((ev (expr_result rbv)) (eval_expr env rbase))
                             ((ev newval) (bitvec_fields_to_record lx.fields lx.pairs rbv.val v)))
                          (eval_lexpr rbv.env lx.base newval))
          :le_destructuring (val-case v
                              :v_array (if (eql (len v.arr) (len lx.elts))
                                           (eval_lexpr_list env lx.elts v.arr)
                                         (ev_error "le_destructuring length mismatch" lx))
                              :otherwise (ev_error "le_destructuring type mismatch" lx)))))

    (define eval_lexpr_list ((env env-p)
                             (lx lexprlist-p)
                             (v vallist-p)
                             &key
                             ((clk natp) 'clk))
      :guard (eql (len lx) (len v))
      :returns (eval env_eval_result-p)
      :measure (nats-measure clk 0 (lexprlist-count* lx) 0)
      (b* (((when (atom lx)) (ev_normal (env-fix env)))
           ((ev env1) (eval_lexpr env (car lx) (car v))))
        (eval_lexpr_list env1 (cdr lx) (cdr v))))

    (define eval_stmt ((env env-p)
                       (s stmt-p)
                       &key
                       ((clk natp) 'clk))
      :measure (nats-measure clk 0 (stmt-count* s) 0)
      :returns (eval stmt_eval_result-p)
      (b* ((s (stmt->val s)))
        (stmt_desc-case s
          :s_pass (ev_normal (continuing env))
          :s_seq (b* (((evs env) (eval_stmt env s.first)))
                   (eval_stmt env s.second))
          :s_decl
          (b* (((unless s.expr) (ev_error "uninitialized declaration" s))
               ((ev (expr_result v)) (eval_expr env s.expr)))
            (local_decl_item-case s.item
              :ldi_var (b* ((env (declare_local_identifier v.env s.item.name v.val)))
                         (ev_normal (continuing env)))
              :ldi_tuple (val-case v.val
                           :v_array (if (eql (len v.val.arr) (len s.item.names))
                                        (b* ((env (declare_local_identifiers v.env s.item.names v.val.arr)))
                                          (ev_normal (continuing env)))
                                      (ev_error "tuple length mismatch" s))
                           :otherwise (ev_error "local declaration type mismatch" s))))
          :s_assign
          (b* (((ev (expr_result v)) (eval_expr env s.expr))
               ((ev new-env) (eval_lexpr v.env s.lexpr v.val)))
            (ev_normal (continuing new-env)))
          :s_call (b* (((call c) s.call)
                       ((ev (exprlist_result cres)) (eval_call c.name env c.params c.args)))
                    (ev_normal (continuing cres.env)))
          :s_return (b* (((unless s.expr)
                          (ev_normal (returning nil (env->global env))))
                         (x (expr->desc s.expr)))
                      (expr_desc-case x
                        :e_tuple (b* (((ev (exprlist_result xr)) (eval_expr_list env x.exprs)))
                                   (ev_normal (returning xr.val (env->global xr.env))))
                        :otherwise (b* (((ev (expr_result xr)) (eval_expr env s.expr)))
                                     (ev_normal (returning (list xr.val) (env->global xr.env))))))
                         
          :s_cond (b* (((ev (expr_result test)) (eval_expr env s.test))
                       ((ev testval) (val-case test.val
                                       :v_bool (ev_normal test.val.val)
                                       :otherwise (ev_error "Non-boolean test result" s.test)))
                       (next (if testval s.then s.else)))
                    (eval_stmt test.env next))
          :s_assert (b* (((ev (expr_result assert)) (eval_expr env s.expr)))
                      (val-case assert.val
                        :v_bool (if assert.val.val
                                    (ev_normal (continuing assert.env))
                                  (ev_error "Assertion failed" s.expr))
                        :otherwise (ev_error "Non-boolean assertion result" s.expr)))
          :s_for (b* (((ev (expr_result startr)) (eval_expr env s.start_e))
                      ((ev (expr_result endr))   (eval_expr env s.end_e))
                      ;;; BOZO FIXME TODO: Add loop limit
                      (env (declare_local_identifier env s.index_name startr.val))
                      ;; Type constraints ensure that start and end are integers,
                      ;; will do this here so we don't have to wrap them in values
                      ((ev startv) (v_to_int startr.val))
                      ((ev endv)   (v_to_int endr.val))
                      ((evs env2)
                       (eval_for env s.index_name ;; missing loop limit
                                      startv s.dir endv s.body))
                      (env3 (remove_local_identifier env2 s.index_name)))
                   (ev_normal (continuing env3)))
                      
          :s_while (eval_loop env t s.test s.body)
          :s_repeat (b* (((evs env1) (eval_block env s.body)))
                      (eval_loop env1 nil s.test s.body))
          :s_throw (ev_error "unsupported statement" s)
          :s_try (ev_error "unsupported statement" s)
          :s_print (ev_error "unsupported statement" s)
          :s_unreachable (ev_error "unreachable" s)
          :s_pragma (ev_error "unsupported statement" s))))
   
     (define eval_slice ((env env-p)
                        (s slice-p)
                        &key
                        ((clk natp) 'clk))
      :returns (eval slice_eval_result-p)
      :measure (nats-measure clk 0 (slice-count s) 0)
      (slice-case s
        :slice_single (let**
                       (((expr_result v) (eval_expr env s.index)))
                       (val-case v.val
                         :v_int (ev_normal (intpair/env (intpair v.val.val 1) v.env))
                         :otherwise (ev_error "Bad single slice" s)))
        :slice_range (let**
                      (((expr_result mend) (eval_expr env s.end))
                       ((expr_result mstart) (eval_expr mend.env s.start)))
                      (val-case mend.val
                        :v_int (val-case mstart.val
                                 :v_int (ev_normal
                                         (intpair/env
                                          (intpair mstart.val.val (- mend.val.val mstart.val.val))
                                          mstart.env))
                                 :otherwise (ev_error "Bad start in the slice range" s))
                        :otherwise (ev_error "Bad top/end in the slice range" s)))
        :slice_length (let**
                       (((expr_result mstart) (eval_expr env s.start))
                        ((expr_result mlength) (eval_expr mstart.env s.length)))
                       (val-case mstart.val
                         :v_int (val-case mlength.val
                                  :v_int (ev_normal
                                          (intpair/env (intpair mstart.val.val mlength.val.val) mstart.env))
                                  :otherwise (ev_error "Bad start in the slice range" s))
                         :otherwise (ev_error "Bad top/end in the slice range" s)))
        :slice_star (let**
                     (((expr_result mfactor) (eval_expr env s.factor))
                      ((expr_result mlength) (eval_expr mfactor.env s.length)))
                     (val-case mfactor.val
                       :v_int (val-case mlength.val
                                :v_int (ev_normal
                                        (intpair/env
                                         (intpair (* mfactor.val.val mlength.val.val) mlength.val.val)
                                         mlength.env))
                                :otherwise (ev_error "Bad length in factor slice" s))
                       :otherwise (ev_error "Bad factor in factor slice" s)))
        ))
     
    (define eval_slice_list ((env env-p)
                             (sl slicelist-p)
                            &key
                            ((clk natp) 'clk))
      :returns (eval slices_eval_result-p)
      :measure (nats-measure clk 0 (slicelist-count sl) 0)
      (b* (((when (atom sl))
            (ev_normal (intpairlist/env nil env)))
           ((ev (intpair/env first)) (eval_slice env (car sl)))
           (env first.env)
           ((ev (intpairlist/env rest)) (eval_slice_list env (cdr sl))))
        (ev_normal (intpairlist/env (cons first.pair rest.pairlist) rest.env))))

    (define eval_for ((env env-p)
                      (index_name identifier-p)
                      ;; missing loop limit
                      (v_start integerp)
                      (dir for_direction-p)
                      (v_end   integerp)
                      (body stmt-p)
                      &key
                      ((clk natp) 'clk))
      :measure (nats-measure clk 0
                             (stmt-count* body)
                             (for_loop-measure v_start v_end dir))
      :returns (eval stmt_eval_result-p)
      (b* (;; TODO tick loop limit
           ((when (for_loop-test v_start v_end dir))
            (ev_normal (continuing env)))
           ((evs env1) (eval_block env body))
           ((mv v_step env2) (eval_for_step env1 index_name v_start dir)))
        (eval_for env2 index_name v_step dir v_end body)))

    (define eval_loop ((env env-p)
                       (is_while booleanp)
                       ;; missing loop limit
                       (e_cond expr-p)
                       (body stmt-p)
                       &key
                       ((clk natp) 'clk))
      :measure (nats-measure clk 0 (+ (expr-count e_cond)
                                      (stmt-count* body))
                             2)
      :returns (eval stmt_eval_result-p)
      (b* (((ev (expr_result cres)) (eval_expr env e_cond))
           ((ev cbool) (v_to_bool cres.val))
           ((when (xor is_while cbool))
            (ev_normal (continuing cres.env)))
           ((evs env2) (eval_block cres.env body))
           ((when (zp clk))
            (ev_error "Loop limit ran out" body)))
        (eval_loop env2 is_while e_cond body :clk (1- clk))))
           
    (define eval_block ((env env-p)
                        (x stmt-p)
                        &key
                        ((clk natp) 'clk))
      :measure (nats-measure clk 0 (stmt-count* x) 1)
      :returns (eval stmt_eval_result-p)
      (b* (((evs env1) (eval_stmt env x)))
        (ev_normal (continuing (pop_scope env env1)))))
           
                        

    ///
    (local (in-theory (disable eval_expr
                               eval_pattern
                               eval_pattern-any
                               eval_expr_list
                               eval_call
                               eval_subprogram
                               eval_stmt
                               eval_slice
                               eval_slice_list
                               )))
    
    (std::defret-mutual len-of-eval_expr_list
      (defret len-of-eval_expr_list
        (implies (eval_result-case eval :ev_normal)
                 (equal (len (exprlist_result->val (ev_normal->res eval)))
                        (len e)))
        :hints ('(:expand ((eval_expr_list env e))))
        :fn eval_expr_list)
      :skip-others t)

    (local (defthm len-equal-0
             (equal (equal 0 (len x))
                    (not (consp x)))))

    (verify-guards eval_expr-fn :guard-debug t
      :hints (("goal" :do-not-induct t)))))

