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

(include-book "operators")
(include-book "measure")
(include-book "ihs/basic-definitions" :dir :system)

(include-book "centaur/bitops/part-select" :dir :system)
(include-book "centaur/bitops/part-install" :dir :system)
(include-book "oracle")

;; (local (include-book "std/strings/hexify" :dir :system))
(include-book "std/alists/alist-defuns" :dir :system)
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/alists/hons-assoc-equal" :dir :system))
(local (include-book "std/alists/put-assoc-equal" :dir :system))
(local (include-book "centaur/vl/util/default-hints" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))
(local (in-theory (disable floor mod unsigned-byte-p)))
(local (table fty::deftagsum-defaults :short-names t))
(local (in-theory (disable (tau-system))))
(local (in-theory (disable put-assoc-equal)))

(local (xdoc::set-default-parents asl-interpreter-functions))

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
    :l_bitvector (v_bitvector x.len (loghead x.len x.val))
    :l_string (v_string x.val)
    :l_label (v_label x.val)))

;; (fty::defmap int-imap :key-type identifier :val-type integerp :true-listp t)
  
;; (local
;;  (defthm alistp-when-int-imap-p-rw
;;    (implies (int-imap-p x)
;;             (alistp x))
;;    :hints(("Goal" :in-theory (enable int-imap-p)))))




  
(local
 (defthm alistp-when-pos-imap-p-rw
   (implies (pos-imap-p x)
            (alistp x))
   :hints(("Goal" :in-theory (enable pos-imap-p)))))




(defprod expr_result
  :short "Type of the result from evaluating an ASL expression"
  ((val val)
   (env env)))

(def-eval_result expr_eval_result-p expr_result-p)

(defprod exprlist_result
  :short "Type of the result from evaluating a list of ASL expressions"
  ((val vallist)
   (env env)))

(def-eval_result exprlist_eval_result-p exprlist_result-p)

(deftagsum control_flow_state
  :short "Type of result from evaluating a statement"
  (:returning ((vals vallist)
               (env global-env))
   :short "Indicates that a return has been encountered")
  (:continuing ((env env))
   :short "Indicates that no return has been encountered and execution of the current
function continues"))

(def-eval_result stmt_eval_result-p control_flow_state-p)

(defprod func_result ((vals vallist ;; val_read_from-list
                            )
                      (env global-env))
  :short "Type of result from evaluating a function call: a list of return values and an
updated global environment")

(def-eval_result func_eval_result-p func_result-p)




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


(defmacro let*> (bindings &rest args)
  (b* (((when (atom bindings)) `(let* () . ,args))
       ((cons (list binder val) rest-bindings) bindings))
    `(let** ((cflow ,val))
            (control_flow_state-case cflow
              :returning (ev_normal cflow)
              :continuing (b* ((,binder cflow.env))
                            (let*> ,rest-bindings . ,args))))))

(deftagsum env_result
  :short "Type of result from searching an env for a variable, indicating it's bound
locally, globally, or not at all"
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

(define val-imaplist-assoc ((key identifier-p) (stack val-imaplist-p))
  :short "Look up a variable in a stack of local storage scopes."
  :returns (pair)
  (if (atom stack)
      nil
    (or (hons-assoc-equal (identifier-fix key) (val-imap-fix (car stack)))
        (val-imaplist-assoc key (cdr stack))))
  ///
  (defret cdr-pair-of-<fn>
    (implies pair
             (val-p (cdr pair))))

  (defthm val-imaplist-assoc-of-cons
    (equal (val-imaplist-assoc key (cons imap stack))
           (or (hons-assoc-equal (identifier-fix key) (val-imap-fix imap))
               (val-imaplist-assoc key stack))))

  (defthm val-imaplist-assoc-of-nil
    (equal (val-imaplist-assoc key nil) nil))
  
  (fty::deffixequiv val-imaplist-assoc))

(define env-find ((x identifier-p)
                  (env env-p))
  :short "Look up a variable in the environment, checking both local and global scopes."
  :returns (res val_env_result-p)
  (b* (((env env))
       ((local-env env.local))
       (local-look (val-imaplist-assoc (identifier-fix x) env.local.storage))
       ((When local-look) (lk_local (cdr local-look)))
       ((global-env env.global))
       (global-look (assoc-equal (identifier-fix x) env.global.storage))
       ((When global-look) (lk_global (cdr global-look))))
    (lk_notfound)))

(define env-find-global ((x identifier-p)
                         (env env-p))
  :short "Look up a variable in the global storage of the environment"
  ;; Gets the value of global variable x if exists, error otherwise
  :returns (res val_result-p)
  (b* (((env env))
       ((global-env env.global))
       (global-look (assoc-equal (identifier-fix x) env.global.storage))
       ((When global-look) (ev_normal (cdr global-look))))
    (ev_error "Global variable not found" x nil)))

(define val-imaplist-assign ((name identifier-p)
                             (v val-p)
                             (stack val-imaplist-p))
  :short "Assign a new value to a variable in a stack of local storage scopes. Looks for
the scope in which it is stored and updates it in place. Does not store the
value if the variable was not already present."
  :returns (new-stack val-imaplist-p)
  (if (atom stack)
      nil
    (if (hons-assoc-equal (identifier-fix name) (val-imap-fix (car stack)))
        (cons (put-assoc-equal (identifier-fix name) (val-fix v) (val-imap-fix (car stack)))
              (val-imaplist-fix (cdr stack)))
      (cons (val-imap-fix (car stack))
            (val-imaplist-assign name v (cdr stack)))))
  ///
  (defthm val-imaplist-assoc-of-val-imaplist-assign
    (equal (val-imaplist-assoc n1 (val-imaplist-assign n2 v stack))
           (if (equal (identifier-fix n1) (identifier-fix n2))
               (and (val-imaplist-assoc n1 stack)
                    (cons (identifier-fix n1) (val-fix v)))
             (val-imaplist-assoc n1 stack)))
    :hints(("Goal" :in-theory (enable val-imaplist-assoc))))

  (defthm val-imaplist-assign-of-cons
    (equal (val-imaplist-assign name v (cons imap stack))
           (if (hons-assoc-equal (identifier-fix name) (val-imap-fix imap))
               (cons (put-assoc-equal (identifier-fix name) (Val-fix v)
                                      (val-imap-fix imap))
                     (val-imaplist-fix stack))
             (cons (val-imap-fix imap)
                   (val-imaplist-assign name v stack)))))

  (defthm val-imaplist-assign-of-nil
    (equal (val-imaplist-assign name v nil) nil))

  (defthm val-imaplist-assign-redundant
    (equal (val-imaplist-assign k1 v1 (val-imaplist-assign k1 v2 x))
           (val-imaplist-assign k1 v1 x)))

  (defthm val-imaplist-assign-identity
    (implies (equal v (cdr (val-imaplist-assoc k x)))
             (equal (val-imaplist-assign k v x)
                    (val-imaplist-fix x)))
    :hints(("Goal" :in-theory (enable val-imaplist-assoc))))

  (fty::deffixequiv val-imaplist-assign)

  (local
   
   (defthm put-assoc-equal-normalize
     (implies (and ;; (syntaxp (and (not (equal k k1))
               ;;               (member-equal k (put-assoc-equal-term-keys x))))
               (hons-assoc-equal k x)
               (not (equal k k1)))
              (equal (put-assoc-equal k v (put-assoc-equal k1 v1 x))
                     (put-assoc-equal k1 v1 (put-assoc-equal k v x))))
     :hints(("Goal" :in-theory (enable put-assoc-equal)))))
  
  (defthm val-imaplist-assign-alternate
    (implies (val-imaplist-assoc k1 x)
             (equal (val-imaplist-assign k1 v1 (val-imaplist-assign k2 v2 (val-imaplist-assign k1 v3 x)))
                    (val-imaplist-assign k1 v1 (val-imaplist-assign k2 v2 x)))))

  (defthm val-imaplist-assign-normalize
    (implies (and (val-imaplist-assoc k x)
                  (not (equal (identifier-fix k) (identifier-fix k1))))
             (equal (val-imaplist-assign k v (val-imaplist-assign k1 v1 x))
                    (val-imaplist-assign k1 v1 (val-imaplist-assign k v x))))))

(define env-assign-local ((name identifier-p)
                          (v val-p)
                          (env env-p))
  :short "Update the value of a variable in the local scope of the environment. If the
variable is not already declared locally, this has no effect."
  :returns (new-env env-p)
  (b* (((env env))
       ((local-env env.local))
       (name (identifier-fix name)))
    (change-env env
                :local (change-local-env
                        env.local
                        :storage (val-imaplist-assign name v env.local.storage)))))

(define env-assign-global ((name identifier-p)
                           (v val-p)
                           (env env-p))
  :short "Set the value of a variable in the global scope of the environment."
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
  :short "Assign a new value to a variable in the environment, if it is either locally or
globally declared. If not, produce a NOTFOUND object to indicate the error."
  :returns (res env_env_result-p)
  (b* (((env env))
       ((local-env env.local))
       (name (identifier-fix name))
       (local-look (val-imaplist-assoc name env.local.storage))
       ((When local-look)
        (lk_local (env-assign-local name v env)))
       ((global-env env.global))
       (global-look (assoc-equal name env.global.storage))
       ((When global-look)
        (lk_global (env-assign-global name v env))))
    (lk_notfound)))


(def-eval_result vallist_result-p vallist-p)



(def-eval_result env_eval_result-p env-p)

(define stack_size-lookup ((name identifier-p)
                           (stack_size pos-imap-p))
  :short "Look up the stack size (number of current nested invocations) of the given
function in the environment's stack_size field."
  :returns (val natp :rule-classes :type-prescription)
  :hooks (:fix)
  (b* ((name (identifier-fix name))
       (stack_size (pos-imap-fix stack_size))
       (look (assoc-equal name stack_size)))
    (if look (cdr look) 0)))
  

(define increment-stack ((name identifier-p)
                         (stack_size pos-imap-p))
  :short "Increment the stack size entry (number of current nested invocations) for the given function."
  :returns (res pos-imap-p)
  (b* ((name (identifier-fix name))
       (stack_size (pos-imap-fix stack_size))
       (val (stack_size-lookup name stack_size)))
    (put-assoc-equal name (+ 1 val) stack_size))
  ///
  
  (defret stack_size-lookup-of-increment-stack
    (equal (stack_size-lookup name2 res)
           (if (identifier-equiv name name2)
               (+ 1 (stack_size-lookup name stack_size))
             (stack_size-lookup name2 stack_size)))
    :hints(("Goal" :in-theory (enable stack_size-lookup))))

  (local (include-book "std/lists/sets" :dir :system))
  (local (include-book "std/alists/alist-keys" :dir :system))
  
  (local (defthm no-duplicatesp-equal-of-append
           (implies (and (no-duplicatesp-equal x)
                         (no-duplicatesp-equal y)
                         (not (intersectp-equal x y)))
                    (no-duplicatesp-equal (append x y)))
           :hints(("Goal" :in-theory (e/d (intersectp-equal))))))

  (local (defthm intersectp-singleton
           (iff (intersectp-equal x (list k))
                (member-equal k x))
           :hints(("Goal" :in-theory (enable intersectp-equal)))))
  
  (defret no-duplicate-keys-of-<fn>
    (implies (no-duplicatesp-equal (acl2::alist-keys (pos-imap-fix stack_size)))
             (no-duplicatesp-equal (acl2::alist-keys res)))
    :hints(("Goal" :in-theory (enable acl2::alist-keys-member-hons-assoc-equal)))))

(define decrement-stack ((name identifier-p)
                         (stack_size pos-imap-p))
  :short "Decrement the stack size entry (number of current nested invocations) for the given function."
  :returns (res pos-imap-p)
  (b* ((name (identifier-fix name))
       (stack_size (pos-imap-fix stack_size))
       (val (- (stack_size-lookup name stack_size) 1)))
    (if (posp val)
        (put-assoc-equal name val stack_size)
      (remove-assoc-equal name stack_size)))
  ///
  (local (defthm posp-lookup-when-pos-impa-p
           (implies (and (pos-imap-p x)
                         (hons-assoc-equal k x))
                    (posp (cdr (hons-assoc-equal k x))))
           :rule-classes :type-prescription))
  
  (defthm decrement-stack-of-increment-stack
    (b* ((incr-result (increment-stack name stack_size)))
      (implies (pos-imap-p stack_size)
               (equal (decrement-stack name incr-result)
                      stack_size)))
    :hints(("Goal" :in-theory (enable increment-stack stack_size-lookup)))))
             
       

(define env-push-stack ((name identifier-p)
                        (env env-p))
  :short "Prepare to call a given function: produce a new env in which the function's
stack size entry is incremented and the local environment is empty. Fails if
the function is not a declared subprogram."
  :returns (new-env env_eval_result-p)
  (b* (((env env))
       ((global-env g) env.global)
       ((static_env_global s) g.static)
       (name (identifier-fix name))
       (look (assoc-equal name s.subprograms))
       ((unless look)
        (ev_error "Unrecognized subprogram" name nil))
       (stack_size (increment-stack name g.stack_size))
       (new-g (change-global-env g :stack_size stack_size)))
    (ev_normal (make-env :global new-g :local (empty-local-env)))))

(define env-pop-stack ((name identifier-p)
                       (prev-env env-p)
                       (call-env global-env-p))
  :short "Undo the operation of @(see env-push-stack) by returning an env where the
global scope is that of @('call-env') (the environment resulting from the
subprogram call) with the function's stack size entry decremented, and the
local scope is that of @('prev-env') (the environment before the subprogram
call)."
  :returns (new-env env-p)
  ;; Takes the local component of the prev-env
  ;; and combines it with the global component of the call-env, but decrements name's stack size.
  (b* (((env call) call-env)
       ((global-env g) call-env)
       (new-g (change-global-env g
                                 :stack_size
                                 (decrement-stack name g.stack_size))))
    (change-env prev-env :global new-g)))


(define get_stack_size ((name identifier-p)
                        (env env-p))
  :short "Look up the stack_size entry for the given function in the env"
  :returns (sz natp :rule-classes :type-prescription)
  (b* (((env env))
       ((global-env g) env.global))
    (stack_size-lookup name g.stack_size)))
    
       
    
    

  




;; (define read_value_from ((vs val_read_from-list-p))
;;   :returns (vals vallist-p)
;;   (if (atom vs)
;;       nil
;;     (cons (val_read_from->val (car vs))
;;           (read_value_from (cdr vs)))))



(define maybe-typed_identifierlist->names ((x maybe-typed_identifierlist-p))
  :parents (maybe-typed_identifierlist)
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
  :short "Declare a variable in the local environment, associating it with the given
value in the topmost scope."
  :returns (new-env env-p)
  (b* (((env env))
       ((local-env l) env.local)
       (new-storage (cons (cons (cons (identifier-fix name) (val-fix val)) (car l.storage))
                          (cdr l.storage))))
    (change-env env :local (change-local-env l :storage new-storage))))

(define remove_local_identifier ((env env-p)
                                 (name identifier-p))
  :short "Remove a variable binding from the top scope of the local environment."
  :long "<p>Currently only used in @(see eval_catchers)</p>"
  :returns (new-env env-p)
  (b* (((env env))
       ((local-env l) env.local)
       (new-storage (cons (remove-assoc-equal (identifier-fix name) (car l.storage))
                          (cdr l.storage))))
    (change-env env :local (change-local-env l :storage new-storage))))

(define declare_local_identifiers ((env env-p)
                                   (names identifierlist-p)
                                   (vals vallist-p))
  :short "Declare a list of variables in the local environment, associating them with the
corresponding values in the topmost scope."
  :guard (eql (len names) (len vals))
  :returns (new-env env-p)
  (b* (((env env))
       ((local-env l) env.local)
       (new-storage (cons (append (pairlis$ (identifierlist-fix names)
                                            (mbe :logic (vallist-fix (take (len names) vals))
                                                 :exec vals))
                                  (car l.storage))
                          (cdr l.storage))))
    (change-env env :local (change-local-env l :storage new-storage))))



(define check_recurse_limit ((env env-p)
                             (name identifier-p)
                             (recurse-limit acl2::maybe-integerp))
  :short "Produce an error if the given function is at or above its given recursion limit."
  :returns (eval eval_result-p)
  (declare (ignorable env name recurse-limit))
  (if (and recurse-limit
           (< (lifix recurse-limit) (get_stack_size name env)))
      (ev_error "Recursion limit ran out" name nil)
    (ev_normal nil)))
       


(defthm call-count-linear
  (b* (((call x)))
    (< (+ (exprlist-count x.params)
          (exprlist-count x.args))
       (call-count x)))
  :hints(("Goal" :in-theory (enable call-count)))
  :rule-classes :linear)


(local
 (defthm nth-of-vallist
   (implies (and
             (vallist-p l)
             (<= 0 idx)
             (< idx (len l)))
            (val-p (nth idx l)))))


(define named_exprlist->exprs ((x named_exprlist-p))
  :parents (named_exprlist)
  :returns (exprs exprlist-p)
  (if (atom x)
      nil
    (cons (named_expr->expr (car x))
          (named_exprlist->exprs (cdr x))))
  ///
  (defret len-of-<fn>
    (equal (len exprs) (len x)))

  (defret exprlist-count-of-<fn>
    (<= (exprlist-count (named_exprlist->exprs x))
        (named_exprlist-count x))
    :hints(("Goal" :in-theory (enable named_exprlist-count exprlist-count)))
    :rule-classes :linear))

(define named_exprlist->names ((x named_exprlist-p))
  :parents (named_exprlist)
  :returns (names identifierlist-p)
  (if (atom x)
      nil
    (cons (named_expr->name (car x))
          (named_exprlist->names (cdr x))))
  ///
  (defret len-of-<fn>
    (equal (len names) (len x))))






(def-eval_result int_eval_result-p integerp)

(define v_to_int ((x val-p))
  :short "Extract the integer value from a v_int type value, or produce an error if it's
the wrong type."
  :returns (i int_eval_result-p)
  (val-case x
    :v_int (ev_normal x.val)
    :otherwise (ev_error "v_to_int bad type" x nil)))

(def-eval_result bool_eval_result-p booleanp)

(define v_to_bool ((x val-p))
  :short "Extract a Boolean from a v_bool type value, or produce an error if
 it's the wrong type."
  :returns (i bool_eval_result-p)
  (val-case x
    :v_bool (ev_normal x.val)
    :otherwise (ev_error "v_to_bool bad type" x nil)))

(def-eval_result id_eval_result-p identifier-p)

(define v_to_label ((x val-p))
  :short "Extract the identifier from a v_label type value, or produce an error if it's
the wrong type."
  :returns (i id_eval_result-p)
  (val-case x
    :v_label (ev_normal x.val)
    :otherwise (ev_error "v_to_label bad type" x nil)))

(local (defthm rationalp-when-integerp-rw
         (implies (integerp x)
                  (rationalp x))))



(define get_field! ((field identifier-p)
                    (rec val-imap-p))
  :short "Get a named field from a record alist, producing an error if it's not present"
  :returns (v val_result-p)
  (b* ((look (assoc-equal (identifier-fix field)
                          (val-imap-fix rec)))
       ((unless look) (ev_error "get_field not found" field nil)))
    (ev_normal (cdr look))))

(define get_field ((field identifier-p)
                   (rec val-p))
  :returns (v val_result-p)
  :short "Get the named field from a v_record type value, or produce an error if it's not
a v_record or the field isn't present"
  (val-case rec
    :v_record (get_field! field rec.rec)
    :otherwise (ev_error "get_field non record" rec nil)))

(define map-get_field! ((fields identifierlist-p)
                        (rec val-imap-p))
  :short "Get the values for a list of named fields from a record alist,
 producing an error if any are not present."
  :returns (v vallist_result-p)
  (b* (((when (atom fields)) (ev_normal nil))
       ((ev val1) (get_field! (car fields) rec))
       ((ev rest) (map-get_field! (cdr fields) rec)))
    (ev_normal (cons val1 rest))))

(define map-get_field ((fields identifierlist-p)
                       (rec val-p))
  :short "Get the values for a list of named fields from a v_record type value, or
produce an error if it's not a v_record or if any field isn't present"
  :returns (v vallist_result-p)
  (val-case rec
    :v_record (map-get_field! fields rec.rec)
    :otherwise (ev_error "map-get_field non record" rec nil)))

(define concat_bitvectors ((vals vallist-p))
  :short "Concatenate the given list of bitvectors together, producing a single bitvector
whose width is the sum of their widths, where the first value in the list
determines the MSBs of the resulting vector. Produce an error if any of the
values are not of v_bitvector type."
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
      :otherwise (ev_error "concat_bitvectors non bitvector" v1 nil)))
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
  :short "For the given list of record fields and corresponding list of bitvector slice specifiers
 (pairs of integers where the first is the LSB and second is the width of the
 slice), extract each bitslice from the given bitvector (integer) and store it
 in the corresponding record field. Error if any of the fields is not present
 in the record, or if any of the slices is out of bounds for the bitvector
 width."
  :guard (eql (len fields) (len slices))
  :returns (v val_result-p)
  (b* (((when (atom fields)) (ev_normal (v_record rec)))
       (field (identifier-fix (car fields)))
       ((unless (assoc-equal field (val-imap-fix rec)))
        (ev_error "bitvec_fields_to_record!: field not in record" field nil))
       ((intpair s) (car slices))
       (start s.first)
       (length s.second)
       ((unless (and (<= 0 start)
                     (<= 0 length)
                     (or (not width)
                         (<= (+ start length) width))))
        (ev_error "bitvec_fields_to_record!: out of bounds slice" (car slices) nil))
       (fieldval (loghead length (logtail start bv)))
       (new-rec (put-assoc-equal field (v_bitvector length fieldval) (val-imap-fix rec))))
    (bitvec_fields_to_record! (cdr fields) (cdr slices) new-rec bv width)))
       
       

(define bitvec_fields_to_record ((fields identifierlist-p)
                                 (slices intpairlist-p)
                                 (rec val-p)
                                 (bv val-p))
  :short "For the given list of record fields and corresponding list of bitvector slice specifiers
 (pairs of integers where the first is the LSB and second is the width of the
 slice), extract each bitslice from @('bv'), which should be of v_bitvector or
 v_int type, and store it in the corresponding field of @('rec'), which should
 be of v_record type. Error if any of the fields is not present in the record,
 any of the slices is out of bounds for the bitvector width, or if @('bv') or
 @('rec') are of wrong value types."
  :guard (eql (len fields) (len slices))
  :returns (v val_result-p)
  (b* (((unless (val-case rec :v_record))
        (ev_error "bitvec_fields_to_record non record" rec nil))
       ((unless (or (val-case bv :v_bitvector)
                    (val-case bv :v_int)))
        (ev_error "bitvec_fields_to_record non bitvec/integer" bv nil))
       ((v_record rec))
       ((mv bv-val bv-len) (val-case bv
                             :v_bitvector (mv bv.val bv.len)
                             :otherwise (mv (v_int->val bv) nil))))
    (bitvec_fields_to_record! fields slices rec.rec bv-val bv-len)))
       

(define for_loop-test ((v_start integerp)
                       (v_end integerp)
                       (dir for_direction-p))
  :short "Test for termination of a for loop. @('v_start') is the iteration index (which
is initiially the starting value) and @('v_end') is the final value. Terminate (return t)
if @('v_start') is past @('v_end') in the direction indicated."
  (if (eq (for_direction-fix dir) :up)
      (< (lifix v_end) (lifix v_start))
    (> (lifix v_end) (lifix v_start))))

(define for_loop-measure ((v_start integerp)
                          (v_end integerp)
                          (dir for_direction-p))
  :short "Measure for termination of for loop iterations, based on the difference between
start and end indices."
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
  :short "Return the next value for the iteration index based on the direction."
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
  :short "Step the for loop iteration index value, store it under the appropriate local
variable in the env (must already be declared), and return the new value."
  :returns (mv (v_step integerp)
               (new-env env-p))
  (b* ((v_step (for_loop-step v_start dir)))
    (mv v_step (env-assign-local index_name (v_int v_step) env)))
  ///
  (defret v_step-of-eval_for_step
    (equal v_step
           (for_loop-step v_start dir))))


(define pop_scope ((env env-p))
  :short "Exit a local block scope by throwing out the topmost scope of the
 env's local storage stack."
  :Returns (new-env env-p)
  (b* (((env env))
       ((local-env env.local)))
    (change-env env
                :local
                (change-local-env env.local
                                  :storage (cdr env.local.storage)))))

(define push_scope ((env env-p))
  :short "Enter a new local block scope by consing an empty scope onto the
 env's local storage stack."
  :Returns (new-env env-p)
  (b* (((env env))
       ((local-env env.local)))
    (change-env env
                :local
                (change-local-env env.local
                                  :storage (cons nil env.local.storage)))))


(define check-bad-slices ((width acl2::maybe-natp)
                          (slices intpairlist-p))
  :short "For the given list of bitvector slices (pairs of integers where the first is
the LSB and second is the width of the slice), produce an error if any are out
of bounds for the given width. If the width is nil, only produce an error
if either the LSB or width is negative."
  :returns (res eval_result-p)
  (b* (((when (atom slices)) (ev_normal nil))
       ((intpair s1) (car slices))
       (start s1.first)
       (len s1.second)
       ((when (or (< start 0)
                  (< len 0)))
        (ev_error "Bad slice" s1 nil))
       ((when (and width
                   (< (lnfix width) (+ start len))))
        (ev_error "Slice out of range of width" (list s1 width) nil)))
    (check-bad-slices width (cdr slices))))


(define slices_sub ((srcval  integerp)
                    (vslices intpairlist-p)
                    )
  :returns (res (and (intpair-p res)
                     (integerp (intpair->first res))
                     (<= 0 (intpair->first res))
                     (integerp (intpair->second res))
                     (<= 0 (intpair->second res)))
                "(length . value)")
  :short "For the given list of bitvector slices (pairs of integers where the first is
the LSB and second is the width of the slice) and integer source value, produce
the value concatenating all the slices of that source value, where the first
slice corresponds to the MSBs of the result.  The result is a pair of integers
where the first is the total width and the second is the concatenated value."
  :guard-debug t
  (if (atom vslices) (intpair 0 0)
    (b* (((intpair first_vslice) (car vslices))
         (rest  (cdr vslices))
         ((intpair dstval_rest) (slices_sub srcval rest))
         (start (nfix first_vslice.first))
         (len   (nfix first_vslice.second))
         (srcpart (bitops::part-select srcval :low start :width len))
         (val (logapp dstval_rest.first dstval_rest.second srcpart)) 
         )
      (intpair (+ len dstval_rest.first) val))))


(define eval_primitive ((name identifier-p)
                        (params vallist-p)
                        (args vallist-p))
  :short "Evaluate the given named primitive on the given parameters and arguments."
  :long "<p>Note that all these primitives are defined in the ASL standard library. If you use
@('aslref') with the @('--no-primitives') command line option to dump the typed
AST read by ACL2, then the stdlib definitions will be used instead and this
function shouldn't be called.</p>"
  :returns (res vallist_result-p)
  :prepwork ((local (defthm character-listp-of-explode-nonnegative-integer
                      (implies (character-listp acc)
                               (character-listp (explode-nonnegative-integer x pb acc)))
                      :hints(("Goal" :in-theory (enable explode-nonnegative-integer))))))
  (fty::multicase
    ((fty::case*-equal name)
     ((list val-case p0 p1) params)
     ((list val-case a0 a1 a2) args))

    (("Real" nil (:v_int))       (ev_normal (list (v_real a0.val))))
    (("SInt" (-) (:v_bitvector)) (ev_normal (list (v_int (logext (acl2::pos-fix a0.len) a0.val)))))
    (("UInt" (-) (:v_bitvector)) (ev_normal (list (v_int a0.val))))
    (("RoundUp" nil (:v_real))   (ev_normal (list (v_int (ceiling a0.val 1)))))
    (("RoundDown" nil (:v_real)) (ev_normal (list (v_int (floor a0.val 1)))))
    (("RoundTowardsZero" nil (:v_real)) (ev_normal (list (v_int (truncate a0.val 1)))))

    ;; (("AsciiStr" nil (:v_int))   (if (and (<= 0 a0.val)
    ;;                                       (<= a0.val 127))
    ;;                                  (ev_normal (list (v_string (coerce (list (code-char a0.val)) 'string))))
    ;;                                (ev_error "AsciiStr argument out of bounds" a0)))
    (("DecStr"   nil (:v_int))   (ev_normal (list (v_string (coerce (explode-atom a0.val 10) 'string)))))
    ;; (("HexStr"   nil (:v_int))   (ev_normal (list (v_string (coerce (explode-atom a0.val 16) 'string)))))
    (("FloorLog2" nil (:v_int))  (if (< 0 a0.val)
                                     (ev_normal (list (v_int (1- (integer-length a0.val)))))
                                   (ev_error "Nonpositive argument to FloorLog2" a0 nil)))

    (-                           (ev_error "Bad primitive" (list name params args) nil)))
  )





(define check_two_ranges_non_overlapping ((x intpair-p)
                                          (y intpair-p))
  :short "Check that two bitvector slices (pairs of integers where the first is
the LSB and second is the width of the slice) are non-overlapping, producing an
error if they do overlap."
  :returns (err eval_result-p)
  (b* (((intpair x))
       (xstart (nfix x.first))
       (xlen   (nfix x.second))
       (xend   (+ xstart xlen))
       ((intpair y))
       (ystart (nfix y.first))
       (ylen   (nfix y.second))
       (yend   (+ ystart ylen))
       (xend-<=-ystart (<= xend ystart))
       (yend-<=-xstart (<= yend xstart)))
    (if (or xend-<=-ystart yend-<=-xstart)
        (ev_normal nil)
      (ev_error "Dynamic error: overlapping slice assignment" (list x y) nil))))


(define check_non_overlapping_slices-1 ((x intpair-p)
                                       (y intpairlist-p))
  :short "Check whether any of the bitvector slices (pairs of integers where the first is
the LSB and second is the width of the slice) in the list y overlap with slice x, producing an
error if so."
  :returns (err eval_result-p)
  (B* (((when (atom y)) (ev_normal nil))
       ((ev -) (check_two_ranges_non_overlapping x (car y))))
    (check_non_overlapping_slices-1 x (cdr y))))

(define check_non_overlapping_slices ((x intpairlist-p))
  :short "Check whether any of the bitvector slices (pairs of integers where the first is
the LSB and second is the width of the slice) in the list x overlap with any in
the list y, producing an error if so."
  :returns (err eval_result-p)
  (B* (((when (atom x)) (ev_normal nil))
       ((ev -) (check_non_overlapping_slices-1 (car x) (cdr x))))
    (check_non_overlapping_slices (cdr x))))


(define vbv-to-int ((x val-p))
  :short "Extract the integer value of a value of v_int or v_bitvector type, or produce
an error if the input is of neither type."
  :returns (res int_eval_result-p)
  (val-case x
    :v_int (ev_normal x.val)
    :v_bitvector (ev_normal x.val)
    :otherwise (ev_error "vbv-to-int type error" x nil)))

(define slices-width ((slices intpairlist-p))
  :short "Return the sum of the widths (second elements) of the given bitvector
 slices."
  :returns (width natp :rule-classes :type-prescription)
  (if (atom slices)
      0
    (+ (nfix (intpair->second (car slices)))
       (slices-width (cdr slices)))))

(define write_to_bitvector-aux ((width)
                                (slices intpairlist-p)
                                (src integerp)
                                (dst integerp))
  :short "Install bits from @('src') into locations in @('dst') given by the bitvector
slices. The total width of the slices determines the number of bits of @('src')
that are used.  The first slice determines where in @('dst') the most
significant set of bits of @('src') will be placed, and similarly the last
slice in the list gives the location in @('dst') where the LSBs of @('src') are
to go."
  :guard (eql width (slices-width slices))
  :guard-hints (("goal" :expand ((slices-width slices))))
  :returns (res integerp :rule-classes :type-prescription)
  (b* (((when (atom slices)) (lifix dst))
       (width (mbe :logic (slices-width slices)
                   :exec width))
       ((intpair x) (car slices))
       (xstart (nfix x.first))
       (xlen   (nfix x.second))
       (next-width (- width xlen))
       (next-dst (bitops::part-install (logtail next-width src) dst :width xlen :low xstart)))
    (write_to_bitvector-aux next-width (cdr slices) src next-dst)))




(define write_to_bitvector ((slices intpairlist-p)
                            (src val-p)
                            (dst val-p))
  :short "Install bits from @('src'), which must be a v_int or v_bitvector value, into
@('dst'), which must be a v_bitvector (otherwise we produce an error). The
 total width of @('slices') determines the number of bits of @('src') that are
 used; the first slice determines where in @('dst') the MSBs of this range of
 bits of @('src') are placed, and similarly the last slice determines where
 in @('dst') the LSBs are placed."
  :long "<p>We produce errors in the following cases:</p>
<ul>
<li> @('dst') is not a bitvector</li>
<li> @('src') is not either a bitvector or integer</li>
<li> any slice has a negative index or ranges past the width of @('dst').</li>
</ul>

<p>Note ASL type checking (and runtime checks) actually requires that @('src')
is a bitvector with width equal to the total width of @('slices'). We might
consider checking this as well.</p>"
  :returns (res val_result-p)
  (b* (((unless (val-case dst :v_bitvector))
        (ev_error "write_to_bitvector type error" dst nil))
       ((v_bitvector dst))
       ((ev src.val) (vbv-to-int src))
       ((ev &) (check-bad-slices dst.len slices))
       (width (slices-width slices)))
    (ev_normal (v_bitvector dst.len (loghead dst.len (write_to_bitvector-aux width slices src.val dst.val)))))
  ///
  (assert-event
   (equal (write_to_bitvector '((28 . 4) (20 . 4) (12 . 4) (4 . 4))
                              (v_int #xabcd)
                              (v_bitvector 32 0))
          (ev_normal (v_bitvector 32 #xa0b0c0d0)))))

(define eval_pattern_mask ((val val-p)
                           (mask bitvector_mask-p))
  :short "<p>Checks whether the given value (which must be of v_bitvector type, or an
error results) satisfies the given bitvector mask. That is, every 1-bit in the
@('set') field of the mask must be 1 in @('val'), and every 1-bit in the
@('unset') field must be 0 in @('val').</p>"
  :returns  (res val_result-p)
  :guard-hints (("goal" :in-theory (enable eval_binop)))
  (b* (((bitvector_mask mask)))
    (val-case val
      :v_bitvector (b* ((set_bv   (v_bitvector mask.length (loghead mask.length mask.set)))
                        (unset_bv (v_bitvector mask.length (loghead mask.length mask.unset)))
                        ((ev val/set) (eval_binop :and val set_bv))
                        ((ev set-ok)  (eval_binop :eq_op val/set set_bv))
                        ((unless (v_bool->val set-ok)) (ev_normal (v_bool nil)))
                        ((ev val_inv) (eval_unop :not val))
                        ((ev val/unset) (eval_binop :and val_inv unset_bv)))
                     (eval_binop :eq_op val/unset unset_bv))
      :otherwise (ev_error "Unsupported pattern_mask case" (cons val mask) nil))))




(defmacro evo_normal (arg)
  `(mv (ev_normal ,arg) orac))


;; This is just a convenient function to hang rewrite rules on for FGL.
(define pass-error (val orac)
  :short "This function is just the @('mv') of its two arguments, but it is only called
when the resulting value is an error. It is a convenience for FGL rewriting so
that the @('orac') can be found for counterexample generation when we detect an
error has been reached. Arguably unnecessary given FGL's backtrace capability."
  :inline t
  :enabled t
  (mv val orac))

(defmacro evo_error (&rest args)
  `(pass-error (ev_error . ,args) orac))

(acl2::def-b*-binder evo
  :parents (asl-interpreter-functions)
  :short "Binds an eval_result object. If it is an ev_error or ev_throwing,
 returns it immediately along with the @('orac'). If it is an @('ev_normal'),
 bind the argument to the @('res') field of the object and continue to
 evaluate."
  :body
  `(b* ((evresult ,(car acl2::forms)))
     (eval_result-case evresult
       :ev_normal (b* ,(and (not (eq (car acl2::args) '&))
                           `((,(car acl2::args) evresult.res)))
                    ,acl2::rest-expr)
       :otherwise (mv evresult orac))))

(defxdoc evo
  :short "@(csee B*) binder: see @(see patbind-evo)")


(define init-backtrace ((x eval_result-p) (pos posn-p))
  :short "If @('x') is of ev_error or ev_throwing type (not ev_normal), set the backtrace
field to a list containing the given position to initialize the
backtrace. Called from the interpreter in cases where an error/throw may have
occurred where a position wasn't available (especially from the @('evob')
binder)."
  :returns (new-x eval_result-p)
  (eval_result-case x
    :ev_normal   (eval_result-fix x)
    :ev_throwing (change-ev_throwing x :backtrace (list pos))
    :ev_error    (change-ev_error x :backtrace (list pos)))
  ///
  (defret eval_result-kind-of-<fn>
    (equal (eval_result-kind new-x)
           (eval_result-kind x)))
  (defret <fn>-when-ev_normal
    (implies (eval_result-case x :ev_normal)
             (equal new-x (eval_result-fix x))))

  (defret val_result-p-of-<fn>
    (implies (val_result-p x)
             (val_result-p new-x))))

(acl2::def-b*-binder evob
  :parents (asl-interpreter-functions)
  :short "Binds an eval_result object. If it is an ev_error or ev_throwing,
 initializes its backtrace with the variable @('pos') (which must already be
 bound) and returns it immediately along with the @('orac'). If it is an
 @('ev_normal'), bind the argument to the @('res') field of the object and
 continue to evaluate."
  :long "<p>This is almost the same as @(see patbind-evo) but @('evob') should be used
when the backtrace hasn't been properly initialized, i.e. when the error was
passed down from a context where a code position wasn't available.</p>"
  :body
  `(b* ((evresult ,(car acl2::forms)))
     (eval_result-case evresult
       :ev_normal (b* ,(and (not (eq (car acl2::args) '&))
                           `((,(car acl2::args) evresult.res)))
                    ,acl2::rest-expr)
       
       :otherwise (pass-error (init-backtrace evresult pos) orac))))

(defxdoc evob
  :short "@(csee B*) binder: see @(see patbind-evob)")



(acl2::def-b*-binder evs
  :parents (asl-interpreter-functions)
  :short "The given form is expected to return an @(see eval_result) object which in the
@('ev_normal') case contains a @(see control_flow_state) result, as well as an
@('orac'). Deals with @('ev_error') and @('ev_throwing') results the same way
as @(see patbind-evo), but additionally if the control_flow_state result is of
@('returning') type, returns it; otherwise, in the @('continuing') case,
evaluates the rest of the bindings/body."
  :body
  `(b* (((mv (evo cflow) orac) ,(car acl2::forms)))
     (control_flow_state-case cflow
              :returning (evo_normal cflow)
              :continuing (b* ,(and (not (eq (car acl2::args) '&))
                                    `((,(car acl2::args) cflow.env)))
                            ,acl2::rest-expr))))

(defxdoc evs
  :short "@(csee B*) binder: see @(see patbind-evs)")


(encapsulate nil
  (local (in-theory (enable nfix)))
  ;; Note: if the subtypes map is malformed, this function won't terminate.
  (defxdoc subtypes_names
    :short "Checks the subtypes map of the given @(see static_env_global) to
 see if @('name1') is a subtype of @('name2'). That is, it checks whether
 either the two names are equal, or else the supertype of @('name1') according
 to the subtypes map is transitively a subtype of @('name2')."
    :long "<p>This is defined with @('acl2::def-tr') to create a function that doesn't
necessarily terminate, e.g. if we encounter a cycle in the subtypes
relation. In this case it returns NIL (not a subtype).</p>")
  
  (acl2::def-tr subtypes_names (tenv name1 name2)
    (declare (xargs :guard (and (static_env_global-p tenv)
                                (identifier-p name1)
                                (identifier-p name2))))
    (b* ((name1 (identifier-fix name1))
         (name2 (identifier-fix name2))
         ((when (equal name1 name2)) t)
         (look (hons-assoc-equal name1 (static_env_global->subtypes tenv)))
         ((unless look) nil))
      (subtypes_names tenv (cdr look) name2))
    :diverge nil))

(define subtypes ((tenv static_env_global-p)
                  (ty1 ty-p)
                  (ty2 ty-p))
  :short "Checks whether @('ty1') is a subtype of @('ty2') according to the subtypes
map. Following ASLRef, this only is the case if both types are named and
@('ty2') is among the chain of supertypes of @('ty1') in the static
environment's subtypes map (according to @(see subtypes_names))."
  (b* ((ty1 (ty->desc ty1))
       (ty2 (ty->desc ty2)))
    (fty::multicase ((type_desc-case ty1)
                     (type_desc-case ty2))
      ((:t_named :t_named) (subtypes_names tenv ty1.name ty2.name))
      (- nil))))


(fty::defoption maybe-catcher catcher)

(define find_catcher ((tenv static_env_global-p)
                      (ty ty-p)
                      (catchers catcherlist-p))
  :short "Looks for an element of @('catchers') that accepts an exception of type
@('ty'); that is, @('ty') must be a subtype (see @(see subtypes)) of the type
accepted by the catcher."
  :returns (catcher maybe-catcher-p)
  (b* (((when (atom catchers)) nil)
       ((catcher c) (car catchers))
       ((when (subtypes tenv ty c.ty))
        (catcher-fix c)))
    (find_catcher tenv ty (cdr catchers)))
  ///
  (defret catcher-count*-of-<fn>
    (implies catcher
             (< (catcher-count* catcher)
                (catcherlist-count* catchers)))
    :hints (("goal" :induct (len catchers)
             :expand ((catcherlist-count* catchers))))
    :rule-classes :linear))
    

(define rethrow_implicit ((throw throwdata-p)
                          (blkres stmt_eval_result-p)
                          (backtrace))
  :short "This supports the empty @('throw') statement inside catcher blocks. If the
result of evaluating a catcher (the @('blkres') argument) is an
@('ev_throwing') with empty throwdata, then we re-throw the original exception,
i.e. return an @('ev_throwing') with the given throwdata and backtrace from the
original exception."
  :returns (res stmt_eval_result-p
                :hyp (stmt_eval_result-p blkres))
  (b* (((when (eval_result-case blkres
                :ev_throwing (not blkres.throwdata)
                :otherwise nil))
        (ev_throwing throw (ev_throwing->env blkres) backtrace)))
    blkres))


(define tick_loop_limit ((x acl2::maybe-integerp))
  :short "The given loop limit is either an integer or nil (signifying no limit.) If nil,
just returns @('(ev_normal nil)'). Otherwise returns (normal) the decremented
value unless it's zero or less, in which case the loop limit has run out and we
return an error."
  :returns (res (and (eval_result-p res)
                     (implies (eval_result-case res :ev_normal)
                              (acl2::maybe-integerp (ev_normal->res res)))))
  (if x
      (if (< 0 (lifix x))
          (ev_normal (1- (lifix x)))
        (ev_error "Loop limit ran out" nil nil))
    (ev_normal nil)))

(defmacro trace-eval_expr ()
  '(trace$ (eval_expr-fn :entry (list 'eval_expr e)
                         :exit (cons 'eval_expr
                                     (let ((value (car values)))
                                       (eval_result-case value
                                         :ev_normal (list 'ev_normal (expr_result->val value.res))
                                         :ev_error value
                                         :ev_throwing (list 'ev_throwing value.throwdata)))))))

(defmacro trace-eval_stmt (&key locals)
  `(trace$ (eval_stmt-fn :entry (list 'eval_stmt s
                                      . ,(and locals '((local-env->storage (env->local env)))))
                         :exit (cons 'eval_stmt
                                     (let ((value (car values)))
                                       (eval_result-case value
                                         :ev_normal (cons 'ev_normal
                                                          (control_flow_state-case value.res
                                                            :returning `(:returning ,value.res.vals)
                                                            :continuing ,(if locals
                                                                             `(list :continuing (local-env->storage (env->local value.res.env)))
                                                                           ''(:continuing))))
                                         :ev_error value
                                         :ev_throwing (list 'ev_throwing
                                                            value.throwdata
                                                            . ,(and locals '((local-env->storage (env->local value.env)))))))))))


(defmacro trace-eval_subprogram ()
  '(trace$ (eval_subprogram-fn :entry (list 'eval_subprogram name vparams vargs)
                               :exit (list 'eval_subprogram
                                           name
                                           (let ((value (car values)))
                                             (eval_result-case value
                                               :ev_normal (b* (((func_result value.res)))
                                                            (list 'ev_normal value.res.vals))
                                               :otherwise value))))))


(local
 (defthm constraint_kind-count-parametrized-reduction
   (IMPLIES
    (EQUAL (CONSTRAINT_KIND-KIND X)
           :PARAMETRIZED)
    (<
     (CONSTRAINT_KIND-COUNT
      (WELLCONSTRAINED (list (CONSTRAINT_EXACT (EXPR (E_VAR name) pos))) prec))
     (CONSTRAINT_KIND-COUNT X)))
   :hints(("Goal" :in-theory (enable constraint_kind-count
                                     int_constraintlist-count
                                     int_constraint-count
                                     expr-count
                                     expr_desc-count)))))

(defconst *dummy-position* (make-posn :fname "<none>" :lnum 0 :bol 0 :cnum 0))

(with-output
  ;; makes it so it won't take forever to print the induction scheme
  :evisc (:gag-mode (evisc-tuple 3 4 nil nil))
  :off (event)
  (defines asl-interpreter-mutual-recursion
    :short "Mutual recursion defining the ASL interpreter"
    :parents (asl-interpreter-main-functions asl-interpreter-functions)
    :prepwork ((local (in-theory (disable xor not)))
               (local (xdoc::set-default-parents asl-interpreter-functions asl-interpreter-mutual-recursion)))
    (define eval_expr ((env env-p)
                       (e expr-p)
                       &key
                       ((clk natp) 'clk)
                       (orac 'orac))
      :parents (asl-interpreter-main-functions asl-interpreter-functions asl-interpreter-mutual-recursion)
      :short "Evaluate an ASL expression @('e') under the given environment @('env'). Returns
an @(see eval_result) and an @('orac'). The eval_result in the @('ev_normal')
case contains an @(see expr_result) object, consisting of the value resulting
from evaluating the expression and a new @('env'). The global environment may
be updated since expressions can include function calls."
      :long "@(def eval_expr-fn)"
      :verify-guards nil
      :returns (mv (eval expr_eval_result-p)
                   new-orac)
      :measure (nats-measure clk 0 (expr-count e) 0)
      (b* ((desc (expr->desc e))
           (pos (expr->pos_start e)))
        (expr_desc-case desc
          :e_literal (evo_normal (expr_result (v_of_literal desc.val) env)) ;; SemanticsRule.ELit
          :e_var (b* ((look (env-find desc.name env)))
                   (env_result-case look                    ;; SemanticsRule.EVar
                     :lk_local (evo_normal (expr_result look.val env))
                     :lk_global (evo_normal (expr_result look.val env))
                     :lk_notfound (evo_error "Variable not found" desc (list (list pos
                                                                                   (local-env->storage (env->local env))
                                                                                   (global-env->storage (env->global env)))))))
          :e_pattern (b* (((mv (evo (expr_result v1)) orac) (eval_expr env desc.expr))
                          ((mv (evo val) orac) (eval_pattern v1.env v1.val desc.pattern)))
                      (evo_normal (expr_result val v1.env)))
          :e_unop ;; anna
          (b* (((mv (evo (expr_result v)) orac) (eval_expr env desc.arg))
               ((evob val) (eval_unop desc.op v.val))) ;;SemanticsRule.Unop
           (evo_normal (expr_result val v.env)))
          :e_binop ;;
          ;;shortcuts first
          (case desc.op
            (:band (b* (((mv (evo (expr_result v1)) orac) (eval_expr env desc.arg1)))
                    (val-case v1.val
                      :v_bool (if v1.val.val
                                  (b* (((mv (evo (expr_result v2)) orac) (eval_expr v1.env desc.arg2))
                                       ((evob val) (eval_binop desc.op v1.val v2.val)))
                                    (evo_normal (expr_result val v2.env)))
                                (evo_normal (expr_result (v_bool nil) v1.env)))
                      :otherwise (evo_error "First argument of && evaluated to non-boolean" desc (list pos)))))
            (:bor (b* (((mv (evo (expr_result v1)) orac) (eval_expr env desc.arg1)))
                   (val-case v1.val
                     :v_bool (if v1.val.val
                                 (evo_normal (expr_result (v_bool t) v1.env))
                               (b* (((mv (evo (expr_result v2)) orac) (eval_expr v1.env desc.arg2))
                                    ((evob val) (eval_binop desc.op v1.val v2.val)))
                                 (evo_normal (expr_result val v2.env))))
                     :otherwise (evo_error "First argument of || evaluated to non-boolean" desc (list pos)))))
            (:impl (b* (((mv (evo (expr_result v1)) orac) (eval_expr env desc.arg1)))
                    (val-case v1.val
                      :v_bool (if v1.val.val
                                  (b* (((mv (evo (expr_result v2)) orac) (eval_expr v1.env desc.arg2))
                                       ((evob val) (eval_binop desc.op v1.val v2.val)))
                                    (evo_normal (expr_result val v2.env)))
                                (evo_normal (expr_result (v_bool t) v1.env)))
                      :otherwise (evo_error "First argument of ==> evaluated to non-boolean" desc (list pos)))))
            ;;all other ops
            (otherwise 
             (b* (((mv (evo (expr_result v1)) orac) (eval_expr env desc.arg1))
                  ((mv (evo (expr_result v2)) orac) (eval_expr v1.env desc.arg2))
                  ((evob val) (eval_binop desc.op v1.val v2.val)))
               (evo_normal (expr_result val v2.env)))))
          :e_call ;; sol
          (b* (((call c) desc.call)
               ((mv (evo (exprlist_result e)) orac)
                (eval_call c.name env c.params c.args (expr->pos_start e)))
               (v (if (and (consp e.val)
                           (atom (cdr e.val)))
                      (car e.val)
                    (v_array e.val))))
            (evo_normal (expr_result v e.env)))
          :e_slice ;; anna
          (b* (((mv (evo (expr_result vexpr)) orac) (eval_expr env desc.expr))
               ((mv (evo (intpairlist/env vslices)) orac) (eval_slice_list vexpr.env desc.slices))
               (srcval vexpr.val)
               )
            (val-case srcval
              :v_int (b* (((evob &) (check-bad-slices nil vslices.pairlist))
                          ((intpair res) (slices_sub srcval.val vslices.pairlist)))
                       (evo_normal
                        (expr_result
                         (v_bitvector res.first (loghead res.first res.second))
                         vslices.env)))
              :v_bitvector (b* (((evob &) (check-bad-slices srcval.len vslices.pairlist))
                                ((intpair res) (slices_sub srcval.val vslices.pairlist)))
                             (evo_normal
                              (expr_result
                               (v_bitvector res.first (loghead res.first res.second))
                               vslices.env)))
              :otherwise (evo_error "Unexpected result of evaluation of desc.expr" desc (list pos))))
          :e_cond  ;; anna
          (b* (((mv (evo (expr_result test)) orac) (eval_expr env desc.test))
               ((evo choice) (val-case test.val
                              :v_bool (ev_normal (if test.val.val desc.then desc.else))
                              :otherwise (ev_error "bad test in e_cond" test.val (list pos)))))
           (eval_expr test.env choice))
          :e_getarray ;; sol
          (b* (((mv (evo (expr_result arr)) orac) (eval_expr env desc.base))
               ((mv (evo (expr_result idx)) orac) (eval_expr arr.env desc.index))
               ((evo idxv) (val-case idx.val
                            :v_int (ev_normal idx.val.val)
                            :otherwise (ev_error "getarray non-integer index" desc (list pos))))
               ((evo arrv) (val-case arr.val
                            :v_array (ev_normal arr.val.arr)
                            :otherwise (ev_error "getarray non-array value" desc (list pos)))))
            (if (and (<= 0 idxv)
                     (< idxv (len arrv)))
                (evo_normal (expr_result (nth idxv arrv) idx.env))
              (evo_error "getarray index out of range" desc (list pos))))
          :e_getenumarray ;; sol
          (b* (((mv (evo (expr_result arr)) orac) (eval_expr env desc.base))
               ((mv (evo (expr_result idx)) orac) (eval_expr arr.env desc.index))
               ((evo idxv) (val-case idx.val
                             :v_label (ev_normal idx.val.val)
                            :otherwise (ev_error "getenumarray non-label index" desc (list pos))))
               ((evo arrv) (val-case arr.val
                             :v_record (ev_normal arr.val.rec)
                             :otherwise (ev_error "getenumarray non-record value" desc (list pos))))
               (look (assoc-equal idxv arrv)))
            (if look
                (evo_normal (expr_result (cdr look) idx.env))
              (evo_error "getenumarray index not found" desc (list pos))))
          :e_getfield ;; anna
          (b* (((mv (evo (expr_result recres)) orac) (eval_expr env desc.base))
               ((evob fieldval) (get_field desc.field recres.val)))
            (evo_normal (expr_result fieldval recres.env)))
          :e_getfields ;; sol
          (b* (((mv (evo (expr_result recres)) orac) (eval_expr env desc.base))
               ((evob fieldvals) (map-get_field desc.fields recres.val))
               ((evob val) (concat_bitvectors fieldvals)))
            (evo_normal (expr_result val recres.env)))
          :e_getcollectionfields
          (b* (((evo gval) (env-find-global desc.base env))
               ((evob fieldvals) (map-get_field desc.fields gval))
               ((evob val) (concat_bitvectors fieldvals)))
            (evo_normal (expr_result val env)))
          :e_getitem ;; anna
          (b* (((mv (evo (expr_result varr)) orac) (eval_expr env desc.base)))
           (val-case varr.val
             :v_array (if (or (< desc.index 0) (<= (len varr.val.arr) desc.index))
                          (evo_error "index out of bounds" desc (list pos))
                        (evo_normal (expr_result (nth desc.index varr.val.arr) varr.env)))
             :otherwise (evo_error "evaluation of the base did not return v_array as expected" desc (list pos))))
          :e_record ;; sol
          (b* ((exprs (named_exprlist->exprs desc.fields))
               (names (named_exprlist->names desc.fields))
               ((mv (evo (exprlist_result e)) orac) (eval_expr_list env exprs)))
            (evo_normal (expr_result (v_record (pairlis$ names e.val))) e.env))
          :e_tuple ;; anna
          (b* (((mv (evo (exprlist_result vals)) orac) (eval_expr_list env desc.exprs)))
            (evo_normal (expr_result (v_array vals.val) vals.env)))
          :e_array ;; sol
          (b* (((mv (evo (expr_result v)) orac) (eval_expr env desc.value))
               ((mv (evo (expr_result len)) orac) (eval_expr v.env desc.length))
               ((evo lenv) (val-case len.val
                            :v_int (if (<= 0 len.val.val)
                                       (ev_normal len.val.val)
                                     (ev_error "array negative length" desc (list pos)))
                            :otherwise (ev_error "array non-integer length" desc (list pos)))))
            (evo_normal (expr_result (v_array (make-list lenv :initial-element v.val)) len.env)))
          :e_enumarray ;; anna
          (b* (((mv (evo (expr_result v)) orac) (eval_expr env desc.value))
               (len (len desc.labels))
               (vals (make-list len :initial-element v.val)) 
               (rec (pairlis$ desc.labels vals))
               )
            (evo_normal (expr_result (v_record rec) v.env)))
          :e_arbitrary ;; sol
          (b* (((mv (evo ty) orac) (resolve-ty env desc.type))
               ((mv val orac) (ty-oracle-val ty orac))
               ((unless val)
                (evo_error "Unsatisfiable type in e_arbitrary" desc (list pos))))
            (evo_normal (expr_result val env)))
          :e_atc ;;anna
          (b* (((mv (evo (expr_result v)) orac) (eval_expr env desc.expr))
               ((mv (evo b) orac) (is_val_of_type v.env v.val desc.type)))
            (if b (evo_normal v) (evo_error "DynError(DETAF" desc (list pos))))
          )))

    (define resolve-int_constraints ((env env-p)
                                     (x int_constraintlist-p)
                                     &key ((clk natp) 'clk) (orac 'orac))
      :short "Resolve subexpressions in the given @(see int_constraintlist) @('x') to integer
literal expressions (satisfying @(see int-literal-expr-p)), or produce an error
if this can't be done."
      :returns (mv (res (and (eval_result-p res)
                             (implies (eval_result-case res :ev_normal)
                                      (int_constraintlist-p (ev_normal->res res)))))
                   new-orac)
      :measure (nats-measure clk 0 (int_constraintlist-count x) 0)
      (if (atom x)
          (evo_normal nil)
        (b* ((constr (car x)))
          (int_constraint-case constr
            :constraint_exact (b* (((mv (evo (expr_result c)) orac) (eval_expr env constr.val)))
                                (val-case c.val
                                  :v_int (b* ((first  (constraint_exact (expr (e_literal (l_int c.val.val)) (expr->pos_start constr.val))))
                                              ((mv (evo (expr_result rest)) orac)
                                               (resolve-int_constraints env (cdr x))))
                                           (evo_normal (cons first rest)))
                                  :otherwise (evo_error "Constraint_exact evaluated to unexpected type" constr nil)))
            :constraint_range (b* (((mv (evo (expr_result from)) orac) (eval_expr env constr.from))
                                   ((mv (evo (expr_result to)) orac) (eval_expr env constr.to)))
                                (fty::multicase
                                  ((val-case from.val)
                                   (val-case to.val))
                                  ((:v_int :v_int)
                                   (b* ((first (constraint_range
                                                (expr (e_literal (l_int from.val.val)) (expr->pos_start constr.from))
                                                (expr (e_literal (l_int to.val.val)) (expr->pos_start constr.to))))
                                        ((mv (evo (expr_result rest)) orac)
                                         (resolve-int_constraints env (cdr x))))
                                     (evo_normal (cons first rest))))
                                  (- (evo_error "Constraint_range evaluated to unexpected type" constr nil))))))))

    (define resolve-constraint_kind ((env env-p)
                                     (x constraint_kind-p)
                                     &key ((clk natp) 'clk) (orac 'orac))
      :short "Resolve subexpressions in the given @(see constraint_kind) @('x') to integer
literal expressions (satisfying @(see int-literal-expr-p)), or produce an error
if this can't be done."
      :returns (mv (res (and (eval_result-p res)
                             (implies (eval_result-case res :ev_normal)
                                      (constraint_kind-p (ev_normal->res res)))))
                   new-orac)
      :measure (nats-measure clk 0 (constraint_kind-count x) 0)
      (constraint_kind-case x
        :unconstrained (evo_normal (unconstrained))
        :wellconstrained (b* (((mv (evo (expr_result constrs)) orac)
                               (resolve-int_constraints env x.constraints)))
                           (evo_normal (wellconstrained constrs x.flag)))
        :parametrized (b* ((new-x (wellconstrained (list (constraint_exact (expr (e_var x.name) *dummy-position*)))
                                                   (precision_full))))
                        (resolve-constraint_kind env new-x))
        :otherwise (evo_error "Can't resolve constraint_kind" x nil)))

    (define resolve-tylist ((env env-p)
                            (x tylist-p)
                            &key ((clk natp) 'clk) (orac 'orac))
      :short "Resolve subexpressions in the given list of types (@(see tylist)) @('x') to
integer literal expressions (satisfying @(see int-literal-expr-p)), or produce
an error if this can't be done."
      :returns (mv (res (and (eval_result-p res)
                             (implies (eval_result-case res :ev_normal)
                                      (tylist-p (ev_normal->res res)))))
                   new-orac)
      :measure (nats-measure clk 0 (tylist-count x) 0)
      (if (atom x)
          (evo_normal nil)
        (b* (((mv (evo first) orac) (resolve-ty env (car x)))
             ((mv (evo rest) orac) (resolve-tylist env (cdr x))))
          (evo_normal (cons first rest)))))

    (define resolve-typed_identifierlist ((env env-p)
                                          (x typed_identifierlist-p)
                                          &key ((clk natp) 'clk) (orac 'orac))
      :short "Resolve subexpressions in the given @(see typed_identifierlist)
@('x') to integer literal expressions (satisfying @(see int-literal-expr-p)),
or produce an error if this can't be done."
      :returns (mv (res (and (eval_result-p res)
                             (implies (eval_result-case res :ev_normal)
                                      (typed_identifierlist-p (ev_normal->res res)))))
                   new-orac)
      :measure (nats-measure clk 0 (typed_identifierlist-count x) 0)
      (b* (((when (atom x)) (evo_normal nil))
           ((typed_identifier x1) (car x))
           ((mv (evo first) orac) (resolve-ty env x1.type))
           ((mv (evo rest) orac) (resolve-typed_identifierlist env (cdr x))))
        (evo_normal (cons (typed_identifier x1.name first) rest))))
    
    (define resolve-ty ((env env-p)
                        (x ty-p)
                        &key ((clk natp) 'clk) (orac 'orac))
      :short "Resolve subexpressions in the given type (@(see ty)) @('x') to
integer literal expressions (satisfying @(see int-literal-expr-p)), or produce
an error if this can't be done. Used in @(see eval_expr) as part of the
evaluation of @('e_arbitrary') expressions."
      :returns (mv (res (and (eval_result-p res)
                             (implies (eval_result-case res :ev_normal)
                                      (ty-p (ev_normal->res res)))))
                   new-orac)
      :measure (nats-measure clk 0 (ty-count x) 0)
      (b* ((pos (ty->pos_start x))
           (ty (ty->desc x)))
        (type_desc-case ty
          :t_int (b* (((mv (evob cnstr) orac) (resolve-constraint_kind env ty.constraint)))
                   (evo_normal (ty (t_int cnstr) pos)))
          :t_bits (b* (((mv (evo (expr_result width)) orac) (eval_expr env ty.expr)))
                    (val-case width.val
                      :v_int ;;(if (<= 0 width.val.val)
                      (evo_normal (ty (t_bits
                                       (expr (e_literal (l_int width.val.val)) pos)
                                       ty.fields)
                                      pos))
                      ;; NOTE -- separation of concerns: we once threw an error if we resolved
                      ;; the bitvector width to a negative value. But instead we'll
                      ;; rely on the consumer of this type to deal with it.
                      ;; (evo_error "Negative bitvector width resolving type" x))
                      :otherwise (evo_error "Unexpected type of bitvector width type" x (list pos))))
          :t_tuple (b* (((mv (evo tys) orac) (resolve-tylist env ty.types)))
                     (evo_normal (ty (t_tuple tys) pos)))
          :t_array (b* (((mv (evo base) orac) (resolve-ty env ty.type)))
                     (array_index-case ty.index
                       :arraylength_expr (b* (((mv (evo (expr_result len)) orac) (eval_expr env ty.index.length)))
                                           (val-case len.val
                                             :v_int ;;(if (<= 0 len.val.val)
                                             (evo_normal (ty (t_array
                                                              (arraylength_expr
                                                               (expr (e_literal (l_int len.val.val)) pos))
                                                              base)
                                                             pos))
                                             ;; (evo_error "Negative array length resolving type" x))
                                             :otherwise (evo_error "Unexpected type of array length" x (list pos))))
                       :arraylength_enum (evo_normal (ty (t_array ty.index base) pos))))
          :t_record (b* (((mv (evo fields) orac)
                          (resolve-typed_identifierlist env ty.fields)))
                      (evo_normal (ty (t_record fields) pos)))
          :t_exception (b* (((mv (evo fields) orac)
                             (resolve-typed_identifierlist env ty.fields)))
                         (evo_normal (ty (t_exception fields) pos)))
          :t_collection (b* (((mv (evo fields) orac)
                             (resolve-typed_identifierlist env ty.fields)))
                         (evo_normal (ty (t_collection fields) pos)))
          :t_named  (b* ((decl_types (static_env_global->declared_types
                                      (global-env->static (env->global env))))
                         (look (hons-assoc-equal ty.name decl_types))
                         ((unless look)
                          (evo_error "Named type not found" x (list pos)))
                         ((when (zp clk))
                          (evo_error "Clock ran out resolving named type" x (list pos)))
                         (type (ty-timeframe->ty (cdr look))))
                      (resolve-ty env type :clk (1- clk)))
          :otherwise (evo_normal (ty ty pos)))))

    
    (define eval_pattern ((env env-p)
                          (val val-p)
                          (p pattern-p)
                          &key
                          ((clk natp) 'clk)
                          (orac 'orac))
      :short "Evaluate whether the @(see pattern) @('p') matches the value @('val')."
      :measure (nats-measure clk 0 (pattern-count p) 0)
      ;; :returns (val val-p)
      ;; Note: this isn't supposed to produce any side effects so we'll omit
      ;; the environment and just return the value
      :returns (mv (eval val_result-p) new-orac)
      (b* ((desc (pattern->desc p))
           (pos (pattern->pos_start p)))
        (pattern_desc-case desc
          :pattern_all (evo_normal (v_bool t)) ;; SemanticsRule.PAll
          :pattern_any (eval_pattern-any env val desc.patterns)
          :pattern_geq (b* (((mv (evo (expr_result v1)) orac) (eval_expr env desc.expr)))
                         (mv (init-backtrace (eval_binop :geq val v1.val) pos) orac))
          :pattern_leq (b* (((mv (evo (expr_result v1)) orac) (eval_expr env desc.expr)))
                         (mv (init-backtrace (eval_binop :leq val v1.val) pos) orac))
          :pattern_mask  ;;We are not checking whether set/unset are consistent
          (val-case val
            :v_bitvector (mv (eval_pattern_mask val desc.mask) orac)
            :otherwise (evo_error "Unsupported pattern_mask case" desc (list pos)))
          :pattern_not (b* (((mv (evo v1) orac) (eval_pattern env val desc.pattern)))
                         (mv (init-backtrace (eval_unop :bnot v1) pos) orac))
          :pattern_range (b* (((mv (evo (expr_result v1)) orac) (eval_expr env desc.lower))
                              ((mv (evo (expr_result v2)) orac) (eval_expr env desc.upper))
                              ((evob lower) (eval_binop :geq val v1.val))
                              ((evob upper) (eval_binop :leq val v2.val)))
                           (mv (init-backtrace (eval_binop :band lower upper) pos) orac))
          :pattern_single (b* (((mv (evo (expr_result v1)) orac) (eval_expr env desc.expr)))
                            (mv (init-backtrace (eval_binop :eq_op val v1.val) pos) orac))
          :pattern_tuple (b* ((len (len desc.patterns))
                              ((evo vs) (val-case val
                                         :v_array (if (eql (len val.arr) len)
                                                      (ev_normal val.arr)
                                                    (ev_error "pattern tuple length mismatch" p (list pos)))
                                         :otherwise (ev_error "pattern tuple type mismatch" p (list pos)))))
                           (eval_pattern_tuple env vs desc.patterns)))))

    (define eval_pattern_tuple ((env env-p)
                                (vals vallist-p)
                                (p patternlist-p)
                                &key
                                ((clk natp) 'clk)
                                (orac 'orac))
      :short "Evaluate whether the @(see patternlist) @('p') matches the values @('vals')."
      :guard (eql (len vals) (len p))
      :measure (nats-measure clk 0 (patternlist-count p) 0)
      :returns (mv (eval val_result-p) new-orac)
      (b* (((when (atom p)) (evo_normal (v_bool t)))
           ((mv (evo first) orac) (eval_pattern env (car vals) (car p)))
           ;; short circuit?
           ((when (val-case first :v_bool (not first.val) :otherwise nil))
            (evo_normal first))
           ((mv (evo rest) orac) (eval_pattern_tuple env (cdr vals) (cdr p))))
        (mv (eval_binop :band first rest) orac)))
        
    
    (define eval_pattern-any ((env env-p)
                              (val val-p)
                              (p patternlist-p)
                              &key
                              ((clk natp) 'clk)
                              (orac 'orac))
      :short "Evaluate whether any pattern in @(see patternlist) @('p') matches the value @('val')."
      :measure (nats-measure clk 0 (patternlist-count p) 0)
      :returns (mv (eval val_result-p) new-orac)
      (if (atom p)
          (evo_normal (v_bool nil))
        (b* (((mv (evo v1) orac) (eval_pattern env val (car p))))
         (val-case v1
           :v_bool (if v1.val
                       (evo_normal v1)
                     (eval_pattern-any env val (cdr p)))
           :otherwise (evo_error "Bad result type from eval_pattern" v1 (list (pattern->pos_start (car p))))))))


    (define eval_expr_list ((env env-p)
                            (e exprlist-p)
                            &key
                            ((clk natp) 'clk)
                            (orac 'orac))
      :short "Evaluate a list of expressions. Produces an eval_result and @('orac'), where in
the @('ev_normal') case the eval_result contains an @(see exprlist_result)
containing the list of values of the expressions and the final env resulting
from the evaluations."
      :returns (mv (eval exprlist_eval_result-p) new-orac)
      :measure (nats-measure clk 0 (exprlist-count e) 0)
      (b* (((when (atom e))
            (evo_normal (exprlist_result nil env)))
           ((mv (evo (expr_result first)) orac) (eval_expr env (car e)))
           (env first.env)
           ((mv (evo (exprlist_result rest)) orac) (eval_expr_list env (cdr e))))
        (evo_normal (exprlist_result (cons first.val rest.val) rest.env))))
  
    (define eval_call ((name identifier-p)
                       (env env-p)
                       (params exprlist-p)
                       (args exprlist-p)
                       (pos posn-p)
                       &key
                       ((clk natp) 'clk)
                       (orac 'orac))
      :short "Evaluate the parameter and argument expressions of a call expression or
statement, and subsequently call the given subprogram on them using @(see
eval_subprogram). The process of calling a subprogram is divided somewhat
arbitrarily between this function and @(see eval_subprogram). In addition to
evaluating the parameters and arguments, this function also checks the function
recursion limit and global recursion limit @('clk'), and pushes/pops the new
local scope from the environment."
      :measure (nats-measure clk 0 (+ (exprlist-count params)
                                      (exprlist-count args)) 0)
      :returns (mv (eval exprlist_eval_result-p) new-orac)
      (b* (((mv (evo (exprlist_result vargs)) orac) (eval_expr_list env args))
           ((mv (evo (exprlist_result vparams)) orac) (eval_expr_list vargs.env params))
           (env vparams.env)
           ;; note: we check our fixed recursion limit here because this is where
           ;; the measure will decrease provided that they haven't been exceeded
           ((evo sub-env) (env-push-stack name env))
           ((when (zp clk))
            (evo_error "Recursion limit ran out" name (list pos)))
           ((mv sub-res orac)
            (eval_subprogram sub-env name vparams.val vargs.val :clk (1- clk))))
        (eval_result-case sub-res
          :ev_normal (b* (((func_result subprog-eval) sub-res.res)
                          ;; (vals (read_value_from subprog-eval.val))
                          (env (env-pop-stack name env subprog-eval.env)))
                       (evo_normal (exprlist_result subprog-eval.vals env)))
          :ev_throwing (b* ((env (env-pop-stack name env (env->global sub-res.env))))
                         (mv (ev_throwing sub-res.throwdata env (cons (list pos
                                                                            (local-env->storage (env->local vparams.env))
                                                                            (global-env->storage (env->global vparams.env)))
                                                                      sub-res.backtrace)) orac))
          :ev_error (mv (change-ev_error sub-res :backtrace (cons (list pos
                                                                        (local-env->storage (env->local env))
                                                                        (global-env->storage (env->global env)))
                                                                  sub-res.backtrace)) orac))))

    (define eval_subprogram ((env env-p)
                             (name identifier-p)
                             (vparams vallist-p)
                             (vargs vallist-p)
                             &key
                             ((clk natp) 'clk)
                             (orac 'orac))
      :parents (asl-interpreter-main-functions asl-interpreter-functions asl-interpreter-mutual-recursion)
      :short "Evaluate a subprogram, calling the function named @('name') (either an ASL
function or a primitive) on the given parameter and argument values
@('vparams'), @('vargs')."
      :long "<p>When proving theorems about an ASL function we typically target the
@('eval_subprogram') of that function, since the interface is relatively
clean (mainly, parameters and arguments are passed in as values, not
expressions).</p>

<p>One slight departure from ASLRef semantics is that we strip out the local
environment when we produce an @('ev_throwing') result. This is done anyway by
@(see eval_call), but we do it here to clean the interface further: no need to
see the local environment in any returned object.</p>

@(def eval_subprogram-fn)"
      :measure (nats-measure clk 1 0 0)
      :returns (mv (eval func_eval_result-p) new-orac)
      (b* ((look (assoc-equal (identifier-fix name)
                              (static_env_global->subprograms
                               (global-env->static
                                (env->global env)))))
           ((unless look)
            (evo_error "Subprogam not found" name nil))
           ((func f) (func-ses->fn (cdr look)))
           ;; ((unless (subprogram_body-case f.body :sb_asl))
           ;;  (evo_error "Primitive subfunctions not supported" name))

           ((unless (and (eql (len vparams) (len f.parameters))
                         (eql (len vargs) (len f.args))))
            (evo_error "Bad arity" (cons name
                                         (if (eql (len vparams) (len f.parameters))
                                             (list (len vargs) (len f.args))
                                           (list (len vparams) (len f.parameters))))
                       (list name vparams vargs)))
         
           ;; probably redundant but in the document
           (env1 (change-env env :local (empty-local-env)))
           ((mv (evo limit) orac) (eval_limit env1 f.recurse_limit))
           ((evo &) (check_recurse_limit env1 name limit)))
        (subprogram_body-case f.body
          :sb_asl (b* ((arg-names (typed_identifierlist->names f.args))
                       (param-names (maybe-typed_identifierlist->names f.parameters))
                       (env2 (declare_local_identifiers env1 arg-names vargs))
                       (env3 (declare_local_identifiers env2 param-names vparams))
                       ((mv bodyres orac) (eval_stmt env3 f.body.stmt)))
                    ;;; NOTE: To strictly comply with the ASL reference manual
                    ;;; we should leave the throwing env alone. But it gets
                    ;;; stripped out by env-pop-stack in eval_call, and it's
                    ;;; convenient for reasoning to be able to prove what a
                    ;;; throwing result equals without including the entire
                    ;;; local environment.
                    (eval_result-case bodyres
                      :ev_normal (let ((bodyres bodyres.res))
                                   (control_flow_state-case bodyres
                                     :returning (evo_normal (func_result bodyres.vals bodyres.env))
                                     :continuing (evo_normal (func_result nil (env->global bodyres.env)))))
                      :ev_error (mv (change-ev_error bodyres :backtrace (cons (list name vparams vargs) bodyres.backtrace))
                                    orac)
                      :ev_throwing (mv (change-ev_throwing bodyres
                                                           :env
                                                           (change-env bodyres.env :local (empty-local-env))
                                                           :backtrace (cons (list name vparams vargs) bodyres.backtrace))
                                       orac)))
          :sb_primitive (b* (((evo primres) (eval_primitive name vparams vargs)))
                          (evo_normal (func_result primres (env->global env)))))))


    (define eval_lexpr ((env env-p)
                        (lx lexpr-p)
                        (v val-p)
                        &key
                        ((clk natp) 'clk)
                        (orac 'orac))
      :short "Evaluate an assignment of a value @('v') to a left-hand side (@(see lexpr)) @('lx')."
      :long "<p>LHS expressions include various field/slot/slice accesses. The typical
pattern for assigning @('<base>.<field>') is:</p>
<nl>
<li>Transform @('<base>') (another lexpr) into an expression @('rbase') using @(see expr_of_lexpr)</li>
<li>Evaluate @('rbase') using @(see eval_expr), resuting in value @('rbv')</li>
<li>Modify @('rbv') to replace its @('<field>') field with @('v'), resulting in value @('newbase')</li>
<li>Recursively call @('eval_lexpr') to assign @('<base>') the value @('newbase').</li></nl>"
      :returns (mv (eval env_eval_result-p) new-orac)
      :measure (nats-measure clk 0 (lexpr-count* lx) 0)
      (b* ((pos (lexpr->pos_start lx))
           (lx (lexpr->desc lx)))
        (lexpr_desc-case lx
          :le_discard (evo_normal (env-fix env))
          :le_var (b* ((envres (env-assign lx.name v env)))
                    (env_result-case envres
                      :lk_local (evo_normal envres.val)
                      :lk_global (evo_normal envres.val)
                      :lk_notfound (evo_error "assign to undeclared variable" lx (list pos))))
          :le_slice (b* ((rbase (expr_of_lexpr lx.base))
                         ((mv (evo (expr_result rbv)) orac) (eval_expr env rbase))
                         ((mv (evo (intpairlist/env vslices)) orac) (eval_slice_list rbv.env lx.slices))
                         ((evob &) (check_non_overlapping_slices vslices.pairlist))
                         ((evob newbase) (write_to_bitvector vslices.pairlist v rbv.val)))
                      (eval_lexpr vslices.env lx.base newbase))
          :le_setarray (b* ((rbase (expr_of_lexpr lx.base))
                            ((mv (evo (expr_result rbv)) orac) (eval_expr env rbase))
                            ((mv (evo (expr_result idx)) orac) (eval_expr rbv.env lx.index))
                            ((evob idxv) (v_to_int idx.val))
                            ((evo newarray)
                             (val-case rbv.val
                               :v_array (if (and (<= 0 idxv)
                                                 (< idxv (len rbv.val.arr)))
                                            (ev_normal (v_array (update-nth idxv v rbv.val.arr)))
                                          (ev_error "le_setarray index out of obunds" lx (list pos)))
                               :otherwise (ev_error "le_setarray non array base" lx (list pos)))))
                         (eval_lexpr idx.env lx.base newarray))
          :le_setenumarray (b* ((rbase (expr_of_lexpr lx.base))
                                ((mv (evo (expr_result rbv)) orac) (eval_expr env rbase))
                                ((mv (evo (expr_result idx)) orac) (eval_expr rbv.env lx.index))
                                ((evob idxv) (v_to_label idx.val))
                                ((evo newarray)
                                 (val-case rbv.val
                                   :v_record (if (assoc-equal idxv rbv.val.rec)
                                                 (ev_normal (v_record (put-assoc-equal idxv v rbv.val.rec)))
                                               (ev_error "le_setenumarray unrecognized index" lx (list pos)))
                                   :otherwise (ev_error "le_setenumarray non record base" lx (list pos)))))
                             (eval_lexpr idx.env lx.base newarray))
          :le_setfield (b* ((rbase (expr_of_lexpr lx.base))
                            ((mv (evo (expr_result rbv)) orac) (eval_expr env rbase))
                            ((evo newrec)
                             (val-case rbv.val
                               :v_record (if (assoc-equal lx.field rbv.val.rec)
                                             (ev_normal (v_record (put-assoc-equal lx.field v rbv.val.rec)))
                                           (ev_error "le_setfield unrecognized field" lx (list pos)))
                               :otherwise (ev_error "le_setfield non record base" lx (list pos)))))
                         (eval_lexpr rbv.env lx.base newrec))
          :le_setfields (b* (((when (not (eql (len lx.fields) (len lx.pairs))))
                              (evo_error "le_setfields length mismatch" lx (list pos)))
                             (rbase (expr_of_lexpr lx.base))
                             ((mv (evo (expr_result rbv)) orac) (eval_expr env rbase))
                             ((evob newval) (bitvec_fields_to_record lx.fields lx.pairs rbv.val v)))
                          (eval_lexpr rbv.env lx.base newval))
          :le_setcollectionfields (b* (((when (not (eql (len lx.fields) (len lx.pairs))))
                                        (evo_error "le_setfields length mismatch" lx (list pos)))
                                       ((evo rbv) (env-find-global lx.base env))
                                       ((evo newval) (bitvec_fields_to_record lx.fields lx.pairs rbv v))
                                       (newenv (env-assign-global lx.base newval env)))
                                    (evo_normal newenv))
          :le_destructuring (val-case v
                              :v_array (if (eql (len v.arr) (len lx.elts))
                                           (eval_lexpr_list env lx.elts v.arr)
                                         (evo_error "le_destructuring length mismatch" lx (list pos)))
                              :otherwise (evo_error "le_destructuring type mismatch" lx (list pos))))))

    (define eval_lexpr_list ((env env-p)
                             (lx lexprlist-p)
                             (v vallist-p)
                             &key
                             ((clk natp) 'clk)
                             (orac 'orac))
      :short "Assign a list of LHS expressions (@(see lexprlist)) @('lx') a corresponding
list of values @('v') using @('eval_lexpr')."
      :guard (eql (len lx) (len v))
      :returns (mv (eval env_eval_result-p) new-orac)
      :measure (nats-measure clk 0 (lexprlist-count* lx) 0)
      (b* (((when (atom lx)) (evo_normal (env-fix env)))
           ((mv (evo env1) orac) (eval_lexpr env (car lx) (car v))))
        (eval_lexpr_list env1 (cdr lx) (cdr v))))

    (define eval_limit ((env env-p)
                        (x maybe-expr-p)
                        &key
                        ((clk natp) 'clk)
                        (orac 'orac))
      :short "Evaluate a loop or recursion limit, producing either an error, an integer if
there was a limit, or nil if there was no limit."
      :measure (nats-measure clk 0 (maybe-expr-count x) 0)
      :returns (mv (res (and (eval_result-p res)
                             (implies (eval_result-case res :ev_normal)
                                      (acl2::maybe-integerp (ev_normal->res res)))))
                   new-orac)
      (b* (((unless x) (evo_normal nil))
           ((mv (evo (expr_result res)) orac) (eval_expr env x))
           (pos (expr->pos_start x))
           ((evob val) (v_to_int res.val)))
        (evo_normal val)))

    (define eval_stmt ((env env-p)
                       (s stmt-p)
                       &key
                       ((clk natp) 'clk)
                       (orac 'orac))
      :parents (asl-interpreter-main-functions asl-interpreter-functions asl-interpreter-mutual-recursion)
      :short "Evaluate a statement @('s') under environment @('env'). Results in an @(see
eval_result) and an @('orac'), where in the @('ev_normal') case the eval_result
contains a @(see <control_flow_state) object. This object records whether a
return was encountered; if so, it gives the returned list of values and global
environment, otherwise if not returning it gives the updated (full, local and
global) environment."
      :long "@(def eval_stmt-fn)"
      :measure (nats-measure clk 0 (stmt-count* s) 0)
      :returns (mv (eval stmt_eval_result-p) new-orac)
      (b* ((pos (stmt->pos_start s))
           (s (stmt->desc s)))
        (stmt_desc-case s
          :s_pass (evo_normal (continuing env))
          :s_seq (b* (((evs env) (eval_stmt env s.first)))
                   (eval_stmt env s.second))
          :s_decl
          (b* (((unless s.expr) (evo_error "uninitialized declaration" s (list pos)))
               ((mv (evo (expr_result v)) orac) (eval_expr env s.expr)))
            (local_decl_item-case s.item
              :ldi_var (b* ((env (declare_local_identifier v.env s.item.name v.val)))
                         (evo_normal (continuing env)))
              :ldi_tuple (val-case v.val
                           :v_array (if (eql (len v.val.arr) (len s.item.names))
                                        (b* ((env (declare_local_identifiers v.env s.item.names v.val.arr)))
                                          (evo_normal (continuing env)))
                                      (evo_error "tuple length mismatch" s (list pos)))
                           :otherwise (evo_error "local declaration type mismatch" s (list pos)))))
          :s_assign
          (b* (((mv (evo (expr_result v)) orac) (eval_expr env s.expr))
               ((mv (evo new-env) orac) (eval_lexpr v.env s.lexpr v.val)))
            (evo_normal (continuing new-env)))
          :s_call (b* (((call c) s.call)
                       ((mv (evo (exprlist_result cres)) orac) (eval_call c.name env c.params c.args pos)))
                    (evo_normal (continuing cres.env)))
          :s_return (b* (((unless s.expr)
                          (evo_normal (returning nil (env->global env))))
                         (x (expr->desc s.expr)))
                      (expr_desc-case x
                        :e_tuple
                        ;; NOTE / WARNING: This is a deviation from the aslref/herd
                        ;; semantics: we return a single value here for now even though
                        ;; the official semantics is to return multiple values. This
                        ;; distinction is important for concurrent semantics but not for
                        ;; sequential.  The reason we made this change is that it is
                        ;; problematic to reason about functions that might return either
                        ;; one value or multiple. We hope to come up with a solution that
                        ;; results in a function being consistent in the number of values
                        ;; returned -- right now in ASL semantics a n-tuple-valued
                        ;; function may return either N values or 1, depending on the form
                        ;; of return statement that it reached.
                        (b* (((mv (evo (exprlist_result xr)) orac) (eval_expr_list env x.exprs)))
                          (evo_normal (returning (list (v_array xr.val)) (env->global xr.env))))
                        :otherwise (b* (((mv (evo (expr_result xr)) orac) (eval_expr env s.expr)))
                                     (evo_normal (returning (list xr.val) (env->global xr.env))))))
                         
          :s_cond (b* (((mv (evo (expr_result test)) orac) (eval_expr env s.test))
                       ((evo testval) (val-case test.val
                                       :v_bool (ev_normal test.val.val)
                                       :otherwise (ev_error "Non-boolean test result" s.test (list pos))))
                       (next (if testval s.then s.else)))
                    (eval_block test.env next))
          :s_assert (b* (((mv (evo (expr_result assert)) orac) (eval_expr env s.expr)))
                      (val-case assert.val
                        :v_bool (if assert.val.val
                                    (evo_normal (continuing assert.env))
                                  (evo_error "Assertion failed" s.expr (list pos)))
                        :otherwise (evo_error "Non-boolean assertion result" s.expr (list pos))))
          :s_for (b* (((mv (evo (expr_result startr)) orac) (eval_expr env s.start_e))
                      ((mv (evo (expr_result endr)) orac)   (eval_expr env s.end_e))
                      ((mv (evo limit) orac)                (eval_limit env s.limit))
                      (env (push_scope env))
                      ;;; BOZO FIXME TODO: Add loop limit
                      (env (declare_local_identifier env s.index_name startr.val))
                      ;; Type constraints ensure that start and end are integers,
                      ;; will do this here so we don't have to wrap them in values
                      ((evob startv) (v_to_int startr.val))
                      ((evob endv)   (v_to_int endr.val))
                      ((evs env2)
                       (eval_for env s.index_name limit
                                      startv s.dir endv s.body))
                      (env3 (pop_scope env2)))
                   (evo_normal (continuing env3)))
                      
          :s_while (b* (((mv (evo limit) orac) (eval_limit env s.limit)))
                     (eval_loop env t limit s.test s.body))
          :s_repeat (b* (((mv (evo limit) orac) (eval_limit env s.limit))
                         ((evob limit2) (tick_loop_limit limit))
                         ((evs env1) (eval_block env s.body)))
                      (eval_loop env1 nil limit2 s.test s.body))
          :s_throw (b* (((unless s.val)
                         (mv (ev_throwing nil env (list pos)) orac))
                        ((expr*maybe-ty s.val))
                        ((unless s.val.ty)
                         (evo_error "Throw with untyped exception" s (list pos)))
                        ((mv (evo (expr_result ex)) orac) (eval_expr env s.val.expr)))
                     (mv (ev_throwing (throwdata ex.val s.val.ty) ex.env (list pos)) orac))
          :s_try (b* (((mv try orac) (eval_block env s.body))
                      ((when (eval_result-case try
                               :ev_throwing (not try.throwdata)
                               :otherwise t))
                       (mv try orac))
                      ((ev_throwing try)))
                   ;; NOTE: The eval_catchers semantics rule takes the original env (from before the eval_block above!)
                   ;; but then uses it just for the static env, combining its static env with the dynamic env from the throw.
                   ;; But it seems the static env shouldn't ever change so why bother?
                   (eval_catchers try.env s.catchers s.otherwise try.throwdata try.backtrace))
                      
          :s_print (b* (((mv (evo (exprlist_result e)) orac) (eval_expr_list env s.args))
                        (str (vallist-to-string e.val))
                        (- (cw (if s.newline "~s0~%" "~s0") str)))
                     (evo_normal (continuing e.env)))
          :s_unreachable (evo_error "unreachable" s (list pos))
          :s_pragma (evo_error "unsupported statement" s (list pos)))))

     (define eval_catchers ((env env-p)
                            (catchers catcherlist-p)
                            (otherwise maybe-stmt-p)
                            (throw throwdata-p)
                            (backtrace)
                            &key
                            ((clk natp) 'clk)
                            (orac 'orac))
       :short "Given data from a thrown exception, determines whether any of the catchers or
otherwise block from a try statement apply and calls the appropriate block."
      :returns (mv (eval stmt_eval_result-p) new-orac)
      :measure (nats-measure clk 0 (+ (catcherlist-count* catchers)
                                      (maybe-stmt-count* otherwise))
                             0)
      (b* (((throwdata throw))
           (catcher? (find_catcher (global-env->static (env->global env)) throw.ty catchers))
           ((unless catcher?)
            (b* (((unless otherwise)
                  (mv (ev_throwing throw env backtrace) orac))
                 ((mv blkres orac) (eval_block env otherwise)))
              (mv (rethrow_implicit throw blkres backtrace) orac)))
           ((catcher c) catcher?)
           ((unless c.name)
            (b* (((mv blkres orac) (eval_block env c.stmt)))
              (mv (rethrow_implicit throw blkres backtrace) orac)))
           (env2 (declare_local_identifier env c.name throw.val))
           ((mv blkres orac)
            (b* (((evs blkenv) (eval_block env2 c.stmt))
                 (env3 (remove_local_identifier blkenv c.name)))
              (evo_normal (continuing env3)))))
        (mv (rethrow_implicit throw blkres backtrace) orac)))
           
    
   
     (define eval_slice ((env env-p)
                        (s slice-p)
                        &key
                        ((clk natp) 'clk)
                        (orac 'orac))
       :short "Evaluates a @(see slice) @('s'), producing an @(see eval_result) which in the
@('ev_normal') case contains an @(see intpair/env) object: an @(see intpair)
where the first element gives the LSB of the slice and the second gives the
width of the slice, and an updated environment."
      :returns (mv (eval slice_eval_result-p) new-orac)
      :measure (nats-measure clk 0 (slice-count s) 0)
      (slice-case s
        :slice_single (b* (((mv (evo (expr_result v)) orac) (eval_expr env s.index)))
                       (val-case v.val
                         :v_int (evo_normal (intpair/env (intpair v.val.val 1) v.env))
                         :otherwise (evo_error "Bad single slice" s (list (expr->pos_start s.index)))))
        :slice_range (b* (((mv (evo (expr_result mend)) orac) (eval_expr env s.end))
                          ((mv (evo (expr_result mstart)) orac) (eval_expr mend.env s.start)))
                      (val-case mend.val
                        :v_int (val-case mstart.val
                                 :v_int (evo_normal
                                         (intpair/env
                                          (intpair mstart.val.val (+ 1 (- mend.val.val mstart.val.val)))
                                          mstart.env))
                                 :otherwise (evo_error "Bad start in the slice range" s (list (expr->pos_start s.start))))
                        :otherwise (evo_error "Bad top/end in the slice range" s (list (expr->pos_start s.end)))))
        :slice_length (b* (((mv (evo (expr_result mstart)) orac) (eval_expr env s.start))
                           ((mv (evo (expr_result mlength)) orac) (eval_expr mstart.env s.length)))
                       (val-case mstart.val
                         :v_int (val-case mlength.val
                                  :v_int (evo_normal
                                          (intpair/env (intpair mstart.val.val mlength.val.val) mstart.env))
                                  :otherwise (evo_error "Bad start in the slice range" s (list (expr->pos_start s.start))))
                         :otherwise (evo_error "Bad length in the slice range" s (list (expr->pos_start s.length)))))
        :slice_star (b* (((mv (evo (expr_result mfactor)) orac) (eval_expr env s.factor))
                         ((mv (evo (expr_result mlength)) orac) (eval_expr mfactor.env s.length)))
                     (val-case mfactor.val
                       :v_int (val-case mlength.val
                                :v_int (evo_normal
                                        (intpair/env
                                         (intpair (* mfactor.val.val mlength.val.val) mlength.val.val)
                                         mlength.env))
                                :otherwise (evo_error "Bad length in factor slice" s (list (expr->pos_start s.length))))
                       :otherwise (evo_error "Bad factor in factor slice" s (list (expr->pos_start s.factor)))))
        ))
     
    (define eval_slice_list ((env env-p)
                             (sl slicelist-p)
                            &key
                            ((clk natp) 'clk)
                            (orac 'orac))
      :short "Evaluate a list of slices with @(see eval_slice). Produces a list of @(see
intpair) objects and a final environment."
      :returns (mv (eval slices_eval_result-p) new-orac)
      :measure (nats-measure clk 0 (slicelist-count sl) 0)
      (b* (((when (atom sl))
            (evo_normal (intpairlist/env nil env)))
           ((mv (evo (intpair/env first)) orac) (eval_slice env (car sl)))
           (env first.env)
           ((mv (evo (intpairlist/env rest)) orac) (eval_slice_list env (cdr sl))))
        (evo_normal (intpairlist/env (cons first.pair rest.pairlist) rest.env))))

    (define eval_for ((env env-p)
                      (index_name identifier-p)
                      (limit acl2::maybe-integerp)
                      (v_start integerp)
                      (dir for_direction-p)
                      (v_end   integerp)
                      (body stmt-p)
                      &key
                      ((clk natp) 'clk)
                      (orac 'orac))
      :short "Evaluate a for loop. ASL semantics say the starting and ending indices are
evaluated once, and while the index variable is set to each consecutive value
it can't be modified, so the number of runs of the body is fixed at the
beginning (except for the cases of returns and exceptions/errors)."
      :measure (nats-measure clk 0
                             (stmt-count* body)
                             (for_loop-measure v_start v_end dir))
      :returns (mv (eval stmt_eval_result-p) new-orac)
      (b* (((evo limit1) (tick_loop_limit limit))
           ((when (for_loop-test v_start v_end dir))
            (evo_normal (continuing env)))
           ((evs env1) (eval_block env body))
           ((mv v_step env2) (eval_for_step env1 index_name v_start dir)))
        (eval_for env2 index_name limit1 v_step dir v_end body)))

    (define eval_loop ((env env-p)
                       (is_while booleanp)
                       (limit acl2::maybe-integerp)
                       (e_cond expr-p)
                       (body stmt-p)
                       &key
                       ((clk natp) 'clk)
                       (orac 'orac))
      :short "Evaluate a while or repeat loop. Until the limit runs out or the @('e_cond')
expression evaluates to false (for while) or true (for repeat/until), evaluate
the body and then call the loop again."
      :measure (nats-measure clk 0 (+ (expr-count e_cond)
                                      (stmt-count* body))
                             2)
      :returns (mv (eval stmt_eval_result-p) new-orac)
      (b* (((mv (evo (expr_result cres)) orac) (eval_expr env e_cond))
           (pos (expr->pos_start e_cond))
           ((evob cbool) (v_to_bool cres.val))
           ((when (xor is_while cbool))
            (evo_normal (continuing cres.env)))
           ((evob limit1) (tick_loop_limit limit))
           ((evs env2) (eval_block cres.env body))
           ((when (zp clk))
            (evo_error "Loop limit ran out" body (list (stmt->pos_start body)))))
        (eval_loop env2 is_while limit1 e_cond body :clk (1- clk))))
           
    (define eval_block ((env env-p)
                        (x stmt-p)
                        &key
                        ((clk natp) 'clk)
                        (orac 'orac))
      :short "Evaluate a statement in a new local scope frame. Local variables declared
within this statement will then disappear after the statement is completed."
      :measure (nats-measure clk 0 (stmt-count* x) 1)
      :returns (mv (eval stmt_eval_result-p) new-orac)
      (b* ((env (push_scope env))
           ((mv stmtres orac) (eval_stmt env x)))
        (eval_result-case stmtres
          :ev_normal (control_flow_state-case stmtres.res
                       :returning (evo_normal stmtres.res)
                       :continuing (evo_normal (continuing (pop_scope stmtres.res.env))))
          :ev_throwing (mv (ev_throwing stmtres.throwdata
                                        (pop_scope stmtres.env)
                                        stmtres.backtrace)
                           orac)
          :otherwise (mv stmtres orac))))
           
    
    (define is_val_of_type_tuple ((env env-p) (vals vallist-p) (types tylist-p)
                                  &key ((clk natp) 'clk)
                                  (orac 'orac))
      :short "Check whether values @('vals') each satisfy the corresponding @('types') using
@(see is_val_of_type)."
      :guard (eql (len vals) (len types))
      :returns (mv (res bool_eval_result-p) new-orac)
      :measure (nats-measure clk 0 (tylist-count types) 0);;(vallist-count vals)
      :guard-debug t
      :verify-guards nil
      (if (atom types)
          (evo_normal t)
        (b* ((v (car vals))
             (ty (car types))
             ((mv (evo first-ok) orac) (is_val_of_type env v ty))
             ((unless first-ok) (evo_normal nil))
             ((mv (evo rest_ok) orac) (is_val_of_type_tuple env (cdr vals) (cdr types)))
             )
          (evo_normal rest_ok))))
                        
      
    
    (define check_int_constraints ((env env-p) (i integerp) (constrs int_constraintlist-p)
                                   &key ((clk natp) 'clk) (orac 'orac))
      :short "At least one constraint needs to be satisfied"
      :long "<p>We assume that any expr eval is side-effect free, therefore there is no need to return env</p>"
      :returns (mv (sat bool_eval_result-p) new-orac)
      :measure (nats-measure clk 0 (int_constraintlist-count constrs) 0)
      (if (atom constrs)
          (evo_normal nil)
        (b* ((constr (car constrs)))
          (int_constraint-case constr
            :constraint_exact (b* (((mv (evo (expr_result c)) orac) (eval_expr env constr.val)))
                                (val-case c.val
                                  :v_int (if (equal c.val.val i)
                                             (evo_normal t)
                                           (check_int_constraints env i (cdr constrs)))
                                  :otherwise (evo_error "Constraint_exact evaluated to unexpected type" constr (list (expr->pos_start constr.val)))))
            :constraint_range (b* (((mv (evo (expr_result from)) orac) (eval_expr env constr.from))
                                   ((mv (evo (expr_result to)) orac) (eval_expr env constr.to)))
                                (fty::multicase
                                  ((val-case from.val)
                                   (val-case to.val))
                                  ((:v_int :v_int) (if (and (<= from.val.val i)
                                                            (<= i to.val.val))
                                                       (evo_normal t)
                                                     (check_int_constraints env i (cdr constrs))))
                                  (- (evo_error "Constraint_range evaluated to unexpected type" constr (list (expr->pos_start constr.from))))))
           ))))
    
    (define is_val_of_type ((env env-p) (v val-p) (ty ty-p)
                            &key ((clk natp) 'clk)
                            (orac 'orac))
      :short "Check whether the given value @('v') satisfies type @('ty'). Used
 in @(see eval_expr) for the evaluation of @('e_atc') (asserting type
 conversion) expressions."
      :long "<p>Expressions within types are typechecked to be pure/immutable, so following
ASLRef we don't return the environment.</p>"
      :returns (mv (res bool_eval_result-p) new-orac)
      :measure (nats-measure clk 0 (ty-count ty) 0);;(val-count v)
      :guard-debug t
      :verify-guards nil
      (b* ((pos (ty->pos_start ty))
           (ty (ty->desc ty)))
        (fty::multicase
          ((val-case v)
           (type_desc-case ty))
          ((:v_int :t_int) (constraint_kind-case ty.constraint
                             :unconstrained (evo_normal t)        ;;INT_UNCONSTRAINED
                             :wellconstrained (check_int_constraints env v.val ty.constraint.constraints) ;;INT_WELLCONSTRAINED
                             :otherwise ;;pendingconstraines and parametrized are not mentioned in ASLRef????
                             (evo_error "is_val_of_type failed - cases of int constrained not covered in ASLRef" (cons v ty) (list pos))))
          ((-      :t_int) (constraint_kind-case ty.constraint
                             :unconstrained (evo_normal t)        ;;INT_UNCONSTRAINED
                             :otherwise (evo_error "is_val_of_type failed T_INT with other than v_int" (cons v ty) (list pos))))
          ((:v_bitvector :t_bits) (b* (((mv (evo (expr_result n)) orac) (eval_expr env ty.expr)))
                                    (val-case n.val
                                      :v_int (evo_normal (equal n.val.val v.len))   ;;BITS
                                      :otherwise (evo_error "is_val_of_type failed - unexpected value of e in (T_BITS e,-)" (cons v ty) (list pos)))))
          ((:v_array :t_tuple) (b* (((unless (and (consp v.arr)
                                                  (consp ty.types)))
                                     (evo_error "For the case of tuple, both v-arr and ty.types must be non-empty lists" (cons v ty) (list pos)))
                                    ((unless (eql (len v.arr) (len ty.types)))
                                     (evo_error "is_val_of_type: value tuple of different length than type tuple" (cons v ty) (list pos))))
                                 (is_val_of_type_tuple env v.arr ty.types)))
          (- (evo_normal t)) ;;TYPE_EQUAL
        )))

    ///
    (local (make-event
            `(in-theory (disable . ,(fgetprop 'eval_expr-fn 'acl2::recursivep nil (w state))))))
    
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


    (std::defret-mutual resolved-p-of-resolve-ty
      (defret resolved-p-of-<fn>
        (implies (eval_result-case res :ev_normal)
                 (int_constraintlist-resolved-p (ev_normal->res res)))
        :hints ('(:expand (<call>)
                  :in-theory (enable int_constraintlist-resolved-p
                                     int_constraint-resolved-p
                                     int-literal-expr-p)))
        :fn resolve-int_constraints)
      (defret resolved-p-of-<fn>
        (implies (eval_result-case res :ev_normal)
                 (constraint_kind-resolved-p (ev_normal->res res)))
        :hints ('(:expand (<call>)
                  :in-theory (enable constraint_kind-resolved-p)))
        :fn resolve-constraint_kind)

      (defret resolved-p-of-<fn>
        (implies (eval_result-case res :ev_normal)
                 (tylist-resolved-p (ev_normal->res res)))
        :hints ('(:expand (<call>)
                  :in-theory (enable tylist-resolved-p)))
        :fn resolve-tylist)

      (defret resolved-p-of-<fn>
        (implies (eval_result-case res :ev_normal)
                 (typed_identifierlist-resolved-p (ev_normal->res res)))
        :hints ('(:expand (<call>)
                  :in-theory (enable typed_identifierlist-resolved-p
                                     typed_identifier-resolved-p)))
        :fn resolve-typed_identifierlist)

      (defret resolved-p-of-<fn>
        (implies (eval_result-case res :ev_normal)
                 (ty-resolved-p (ev_normal->res res)))
        :hints ('(:expand (<call>)
                  :in-theory (enable ty-resolved-p
                                     array_index-resolved-p
                                     int-literal-expr-p))
                (and stable-under-simplificationp
                     '(:expand ((ty-resolved-p x)))))
        :fn resolve-ty)
      :skip-others t)

    
    (verify-guards eval_expr-fn :guard-debug t
      :hints (("goal" :do-not-induct t)))
    ))








