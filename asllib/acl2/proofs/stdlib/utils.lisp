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
(define loop-induct ((env env-p) (whilep) (limit acl2::maybe-integerp) (test expr-p) (body stmt-p)
                     &key ((clk natp) 'clk) (orac 'orac))
  :verify-guards nil
  :non-executable t
  :measure (nfix clk)
  (b* (((mv (ev_normal cev) orac) (eval_expr env test))
       ((expr_result cev.res))
       ((unless (iff (ev_normal->res (v_to_bool cev.res.val)) whilep))
        env)
       (limit (ev_normal->res (tick_loop_limit limit)))
       ((mv (ev_normal blkev) orac) (eval_block cev.res.env body))
       ((continuing blkev.res))
       ((when (zp clk))
        blkev.res.env))
    (loop-induct blkev.res.env whilep limit test body :clk (1- clk))))
(in-theory (enable (:i loop-induct)))


(define for-induct ((env env-p) (index_name identifier-p) (limit acl2::maybe-integerp) (start integerp) (dir for_direction-p) (end integerp) (body stmt-p) &key ((clk natp) 'clk) (orac 'orac))
  :verify-guards nil
  :non-executable t
  :measure (for_loop-measure start end dir)
  (b* (((when (for_loop-test start end dir))
        env)
       (limit (ev_normal->res (tick_loop_limit limit)))
       ((mv (ev_normal blkev) orac) (eval_block env body))
       ((continuing blkev.res))
       ((mv step env2) (eval_for_step blkev.res.env index_name start dir)))
    (for-induct env2 index_name limit step dir end body)))
(in-theory (enable (:i for-induct)))

    

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





                    
                       
(program)

(defun loop-local-var-bindings (local-vars)
  (if (atom local-vars)
      nil
    (let* ((rest (loop-local-var-bindings (cdr local-vars)))
           (first (car local-vars)))
      (case-match first
        (((ctor name) str . &)
         (if (and (stringp str)
                  (member ctor '(v_int v_bool v_real v_string v_bitvector v_label v_record v_array))
                  (symbolp name))
             (append (acl2::template-subst '((<name>-look (hons-assoc-equal <str> env.local.storage))
                                             ((<ctor> <name>) (cdr <name>-look)))
                                           :atom-alist `((<ctor> . ,ctor)
                                                         (<name> . ,name)
                                                         (<str> . ,str))
                                           :str-alist `(("<NAME>" . ,(symbol-name name)))
                                           :pkg-sym 'asl-pkg)
                     rest)
           (er hard? 'loop-local-var-bindings "Bad local-vars entry: ~x0" first)))
        (& (er hard? 'loop-local-var-bindings "Bad local-vars entry: ~x0" first))))))

;; (loop-local-var-bindings '(((v_bitvector x) "__stdlib_local_x") ((v_int n) "__stdlib_local_N")))

(defun loop-local-var-hyps (local-vars)
  (if (atom local-vars)
      nil
    (let* ((rest (loop-local-var-hyps (cdr local-vars)))
           (first (car local-vars)))
      (case-match first
        (((ctor name) & . &)
         (append (acl2::template-subst '(<name>-look
                                         (val-case <name> <kind>))
                                       :atom-alist `((<kind> . ,(intern-in-package-of-symbol
                                                                 (symbol-name ctor) :keyword-pkg))
                                                     (<name> . ,name))
                                       :str-alist `(("<NAME>" . ,(symbol-name name)))
                                       :pkg-sym 'asl-pkg)
                 rest))
        (& rest)))))

(defun loop-local-vars-final-env (local-vars)
  (if (atom local-vars)
      'env.local.storage
    (let* ((rest (loop-local-vars-final-env (cdr local-vars)))
           (first (car local-vars)))
      (case-match first
        ((& str final-val)
         `(put-assoc-equal ,str ,final-val ,rest))
        (& rest)))))

;; (loop-local-var-hyps '(((v_bitvector x) "__stdlib_local_x") ((v_int n) "__stdlib_local_N")))



(defconst *defloop-template*
  '(defsection <name>
     (defconst *<name>*
       (find-nth-form <nth> <looptype>
                      (hons-assoc-equal <fn>
                                        (static_env_global->subprograms <static-env>))))

     (:@ (not :s_for)
      (defconst *<name>-test*
        (<looptype>->test *<name>*)))

     (defconst *<name>-body*
       (<looptype>->body *<name>*))

     <prepwork>
     
     (local (in-theory (acl2::e/d* (<defloop-enables>
                                    <user-enables>)
                                   (<defloop-disables>
                                    <user-disables>))))
     (defthm <name>-correct
       (b* (((env env))
            ((local-env env.local))
            <local-var-bindings>
            <user-bindings>)
         (implies (and <local-var-hyps>
                       ;; <measure-hyps>
                       <invariants>
                       (no-duplicatesp-equal (acl2::alist-keys env.local.storage)))
                  (b* (((mv (ev_normal res) &) <loop-form>))
                    <concl>)))
       :hints (;; copied from just-induct-and-expand
               (if (equal (car id) '(0))
                   (let* ((expand-hints (acl2::just-expand-cp-parse-hints
                                         '(<loop-form-expand>) (w state)))
                          (cproc `(acl2::mark-expands-cp clause '(nil t ,expand-hints))))
                     `(:computed-hint-replacement
                       ((and (equal (car id) '(0)) '(:clause-processor acl2::clause-to-term))
                        (and (equal (car id) '(0)) '(:induct <induction>)))
                       :clause-processor ,cproc))
                 (and (equal (car id) '(0 1))
                      (acl2::expand-marked :last-only t)))
               <user-hints>))))





(define defloop-fn (name args state)
  (b* (((std::extract-keyword-args
         :other-args bad-args
         ;; :kwd-alist kwd-alist
         function
         (looptype :while)
         (nth 0)

         ;; format: ((val_type acl2-varname) "asl-varname" [ final value ] )* --
         ;; e.g. (((v_bitvector x) "__stdlib_local_x" x-final-value) ((v_int n) "__stdlib_local_N"))
         ;; For loop index is separately listed as index-var
         local-vars
         index-var
         (start-var 'start)
         (end-var 'end)

         ;; For now we just support loops that execute normally (no
         ;; throw/error) -- eventually add conditions for throwing/erroring.

         ;; When loop finishes (continuing), then the local-vars above give the
         ;; final values stored in the updated environment. If it returns
         ;; early, we need to know the return condition and return values.
         (return-cond 'nil)
         return-values
         
         enable
         disable
         hints
         prepwork
         
         (invariants 't)
         bindings
         (static-env '(stdlib-static-env)))
        args)
       ((when bad-args)
        (er soft 'defloop "Bad arguments: ~x0" bad-args))
       ((unless (stringp function))
        (er soft 'defloop "Function should be a string: ~x0" function))
       (orig-looptype looptype)
       (looptype (case orig-looptype
                   ((:while :s_while) :s_while)
                   ((:for :s_for) :s_for)
                   ((:repeat :s_repeat) :s_repeat)
                   (t nil)))
       ((unless looptype)
        (er soft 'defloop "Bad looptype: ~x0" orig-looptype))
       ((unless (natp nth))
        (er soft 'defloop "Bad nth: ~x0" nth))
       ((acl2::er (cons & static-env-val))
        (acl2::simple-translate-and-eval static-env nil nil
                                         (msg "static env ~x0" static-env)
                                         'defloop (w state) state t))
       ((unless (static_env_global-p static-env-val))
        (er soft 'defloop "Bad static env (evaluation of ~x0): doesn't satisfy static_env_global-p" static-env))
       (fn-struct (hons-assoc-equal function
                                    (static_env_global->subprograms static-env-val)))
       ((unless fn-struct)
        (er soft 'defloop "Bad function ~x0: not found in static env" function))
       ;; if found, then it's the right type
       (form (find-nth-form nth looptype fn-struct))
       ((unless form)
        (er soft 'defloop "Loop not found: function ~x0 looptype ~x1 nth ~x2" function looptype nth))

       ((when (and (eq looptype :s_for)
                   (not index-var)))
        (er soft 'defloop "Index var must be specified for for loops"))
       ((when (and index-var (not (eq looptype :s_for))))
        (er soft 'defloop "Index var specified for non-for loop"))
       
       (local-vars (if (eq looptype :s_for)
                       (cons `((v_int ,index-var)
                               ,(s_for->index_name form)
                               (v_int
                                ,(if (eq (s_for->dir form) :up)
                                     `(+ 1 ,end-var)
                                   `(+ -1 ,end-var))))
                             local-vars)
                     local-vars))
                               
       (local-var-bindings (loop-local-var-bindings local-vars))
       (local-var-hyps (loop-local-var-hyps local-vars))
       (local-var-hyps (if (eq looptype :s_for)
                           (append local-var-hyps
                                   `((equal (v_int->val ,index-var) ,start-var)
                                     (integerp ,end-var)
                                     ,(if (eq (s_for->dir form) :up)
                                          `(<= ,start-var (+ 1 ,end-var))
                                        `(<= (+ -1 ,end-var) ,start-var))))
                         local-var-hyps))
        
       (local-var-final-env (loop-local-vars-final-env local-vars))

       (continuing-concl
        `(and (equal (control_flow_state-kind res.res) :continuing)
              (b* (((continuing res.res)))
                (equal res.res.env
                       (change-env env
                                   :local
                                   (change-local-env
                                    env.local
                                    :storage ,local-var-final-env))))))
       (returning-concl
        `(and (equal (control_flow_state-kind res.res) :returning)
              (b* (((returning res.res)))
                (and (equal res.res.vals ,return-values)
                     (equal res.res.env env.global)))))

       (normal-concl
        `(and (equal (eval_result-kind res) :ev_normal)
              ,@(and (not (eq return-cond t))
                     `(,(if (eq return-cond nil)
                            continuing-concl
                          `(implies (not ,return-cond)
                                    ,continuing-concl))))
              ,@(and (not (eq return-cond nil))
                     `(,(if (eq return-cond t)
                            returning-concl
                          `(implies ,return-cond
                                    ,returning-concl))))))
                       
              
       ((acl2::tmplsubst template)
        (acl2::make-tmplsubst
         :atoms `((<name> . ,name)
                  (<nth> . ,nth)
                  (<looptype> . ,looptype)
                  (<fn> . ,function)
                  (<static-env> . ,static-env)
                  (<invariants> . ,invariants)
                  (<concl> . ,normal-concl))
         :splices `((<defloop-enables> . (defloop-enables))
                    (<defloop-disables> . (defloop-disables))
                    (<user-enables> . ,enable)
                    (<user-disables> . ,disable)
                    (<local-var-bindings> . ,local-var-bindings)
                    (<local-var-hyps> . ,local-var-hyps)
                    (<user-hints> . ,hints)
                    (<user-bindings> . ,bindings)
                    (<prepwork> . ,prepwork))
         :strs `(("<NAME>" . ,(symbol-name name))
                 ("<LOOPTYPE>" . ,(symbol-name looptype)))
         :features (list looptype)
         :pkg-sym 'asl-pkg))

       (body-const (acl2::template-subst-top '*<name>-body* template))
       (test-const (acl2::template-subst-top '*<name>-test* template))
       
       ((mv loop-form expand induction)
        (case looptype
          (:s_for
           (let ((args `(env ,(s_for->index_name form)
                             ,(and (s_for->limit form) 'limit)
                             ,start-var ,(s_for->dir form) ,end-var
                             ,body-const)))
             (mv `(eval_for  . ,args)
                 `(:free (limit ,start-var ,end-var)
                   (eval_for . ,args))
                 `(for-induct . ,args))))
          (t
           (let ((args `(env ,(eq looptype :s_while)
                             ,(and (if (eq looptype :s_while)
                                       (s_while->limit form)
                                     (s_repeat->limit form))
                                   'limit)
                             ,test-const ,body-const)))
             (mv `(eval_loop . ,args)
                 `(:free (limit) (eval_loop . ,args))
                 `(loop-induct . ,args))))))

       (template (acl2::change-tmplsubst
                  template :atoms `((<loop-form> . ,loop-form)
                                    (<induction> . ,induction)
                                    (<loop-form-expand> . ,expand)
                                    . ,template.atoms)))
                      
                      
       (event
        (acl2::template-subst-top *defloop-template* template)))
    (value event)))

(defmacro defloop (name &rest args)
  `(make-event (defloop-fn ',name ',args state)))




(acl2::def-ruleset! defloop-enables '(check_recurse_limit
                                      declare_local_identifiers
                                      declare_local_identifier
                                      env-find
                                      env-assign
                                      env-assign-local
                                      env-assign-global
                                      env-push-stack
                                      env-pop-stack
                                      pop_scope
                                      tick_loop_limit
                                      v_to_bool
                                      eval_for_step
                                      for_loop-step
                                      for_loop-test
                                      check-bad-slices
                                      slices_sub
                                      check_non_overlapping_slices
                                      check_non_overlapping_slices-1
                                      slices-width
                                      write_to_bitvector
                                      write_to_bitvector-aux
                                      vbv-to-int))

(acl2::def-ruleset defloop-disables nil)
