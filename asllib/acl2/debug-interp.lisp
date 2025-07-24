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
(include-book "std/util/defconsts" :dir :system)
(include-book "clause-processors/just-expand" :dir :System)
(local (include-book "interp-theory"))

;; Define a new version of the interpreter that additionally collects
;; debug/trace information according to a trace specification.

;; First exercise: just collect a trace of all subprogram calls.


(defxdoc asl-tracing
  :parents (asl)
  :short "Versions of the ASL interpreter that produce a trace of the evaluation"
  :long "<p>The main ASL interpreter (see @(see asl-interpreter-mutual-recursion)) only
produces the final result of the evaluation; in some cases we want to see (and
reason about) what happened internally. Subtopics of this doc topic include
derived versions of the ASL interpreter that produce trace objects. See @(see
asl-trace) for the format of these objects.</p>")

(deftypes asl-trace
  (defprod asl-trace
    :parents (asl-tracing)
    :short "Describes an ASL subprogram call, including inputs, result, and sub-calls."
    ((fn identifier-p)
     (params vallist-p)
     (args vallist-p)
     (globals-in val-imap-p
                 "The global storage state at the time this function was called. The resulting
                 state is part of the result, for a normal result.")
     (calls asl-tracelist "The list of subroutine calls within this call, in sequential order.")
     (result eval_result-p
             :reqfix (eval_result-case result
                       :ev_normal (ev_normal (func_result-fix result.res))
                       :otherwise result))
     (pos posn))
    :require (eval_result-case result
               :ev_normal (func_result-p result.res)
               :otherwise t)
    :measure (acl2::two-nats-measure (acl2-count x) 1)
    :layout :list)
  (deflist asl-tracelist :elt-type asl-trace :true-listp t :elementp-of-nil nil
    :parents (asl-tracing)
    :short "A list of @(see asl-trace) elements."
    :measure (acl2::two-nats-measure (acl2-count x) 0)))

(local
 (defthm true-listp-when-asl-tracelist-p
   (implies (asl-tracelist-p x)
            (true-listp x))
   :rule-classes ((:rewrite :backchain-limit-lst 1))))

(defthm asl-tracelist-p-of-append
  (implies (and (asl-tracelist-p x)
                (asl-tracelist-p y))
           (asl-tracelist-p (append x y))))


(local
 (mutual-recursion
  (defun find-form-by-car (car x)
    (declare (xargs :mode :program))
    (if (atom x)
        nil
      (if (equal (car x) car)
          x
        (find-form-by-car-list car x))))
  (defun find-form-by-car-list (car x)
    (if (atom x)
        nil
      (or (find-form-by-car car (car x))
          (find-form-by-car-list car (cdr x)))))))

(local (defun keep-define-forms-in-list (x)
         (if (atom x)
             nil
           (if (and (consp (car x))
                    (eq (caar x) 'define))
               (cons (car x) (keep-define-forms-in-list (cdr x)))
             (keep-define-forms-in-list (cdr x))))))

(local (defun strip-post-/// (x)
         (declare (xargs :mode :program))
         (if (atom x)
             x
           (if (eq (car x) '///)
               '(///)
             (cons (strip-post-/// (car x))
                   (strip-post-/// (cdr x)))))))

(local (defun strip-xdoc (x)
         (if (atom x)
             x
           (if (member-eq (car x) '(:short :long :parents))
               (strip-xdoc (cddr x))
             (cons (strip-xdoc (car x))
                   (strip-xdoc (cdr x)))))))



(defconsts *asl-interp-fns*
  (acl2::strip-cadrs
   (keep-define-forms-in-list
    (find-form-by-car
     'defines *asl-interpreter-mutual-recursion-command*))))


(defmacro evo_normal-*ft (arg)
  `(mv (ev_normal ,arg) orac trace))

(define pass-error-*ft (val &optional (orac 'orac) (trace 'trace))
  :inline t
  :enabled t
  (mv val orac trace))

(defmacro evo_error-*ft (&rest args)
  `(pass-error-*ft (ev_error . ,args) orac trace))

(defmacro evo_throwing-*ft (&rest args)
  `(mv (ev_throwing . ,args) orac trace))

(defmacro evo-return-*ft (arg)
  `(mv ,arg orac trace))

(defmacro evtailcall-*ft (call)
  `(b* (((evbind-*ft res) ,call))
     (evo-return-*ft res)))

(acl2::def-b*-binder evbind-*ft
  :body
  `(b* (((mv ,(car acl2::args) orac trace-tmp) . ,acl2::forms)
        (trace (append trace-tmp trace)))
     ,acl2::rest-expr))

(acl2::def-b*-binder evo-*ft
  :body
  `(b* ((evresult ,(car acl2::forms)))
     (eval_result-case evresult
       :ev_normal (b* ,(and (not (eq (car acl2::args) '&))
                           `((,(car acl2::args) evresult.res)))
                    ,acl2::rest-expr)
       :otherwise (mv evresult orac trace))))

(acl2::def-b*-binder evoo-*ft
  :body
  `(b* (((evbind-*ft (evo-*ft ,(car acl2::args))) . ,acl2::forms))
     ,acl2::rest-expr))

(acl2::def-b*-binder evs-*ft
  :body
    `(b* (((evoo-*ft cflow) ,(car acl2::forms)))
     (control_flow_state-case cflow
              :returning (evo_normal-*ft cflow)
              :continuing (b* ,(and (not (eq (car acl2::args) '&))
                                    `((,(car acl2::args) cflow.env)))
                            ,acl2::rest-expr))))

(acl2::def-b*-binder evob-*ft
  :body
  `(b* ((evresult ,(car acl2::forms)))
     (eval_result-case evresult
       :ev_normal (b* ,(and (not (eq (car acl2::args) '&))
                           `((,(car acl2::args) evresult.res)))
                    ,acl2::rest-expr)
       
       :otherwise (pass-error-*ft (init-backtrace evresult pos) orac))))

(defmacro evbody-*ft (body)
  `(let ((trace nil))
     ,body))



(local
 (defun pair-suffixed (syms suffix)
   (if (atom syms)
       nil
     (cons (cons (car syms)
                 (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name (car syms))
                               (symbol-name suffix))
                  (car syms)))
           (pair-suffixed (cdr syms) suffix)))))

(defconsts *eval-fulltrace-substitution*
  (pair-suffixed (append *asl-interp-fns*
                         '(evo_normal pass-error evo_error evo_throwing evo-return
                                      evbind evoo evo evob evs evtailcall
                                      asl-interpreter-mutual-recursion))
                 '-*ft))
  


(local
 (defconst *eval_subprogram-*ft-def*
   '(define eval_subprogram-*ft ((env env-p)
                                 (name identifier-p)
                                 (vparams vallist-p)
                                 (vargs vallist-p)
                                 &key
                                 ((clk natp) 'clk)
                                 (orac 'orac)
                                 ((pos posn-p) 'pos))
      :short "Full Tracing version of @(see eval_subprogram); see @(see
asl-interpreter-mutual-recursion-*ft) for overview."
      :measure (nats-measure clk 1 0 1)
      :returns (mv (eval func_eval_result-p) new-orac
                   (trace asl-tracelist-p))
      (b* (((mv res orac trace) (eval_subprogram-*ft1 env name vparams vargs))
           (trace (list (make-asl-trace
                         :fn name
                         :params vparams
                         :args vargs
                         :globals-in (global-env->storage (env->global env))
                         :calls (acl2::rev trace)
                         :result res
                         :pos pos))))
        (mv res orac trace)))))


(local
 (defun find-eval_subprogram-def-and-rename (suffix x)
   (if (atom x)
       x
     (case-match x
       (('define 'eval_subprogram . rest)
        `(define ,(intern-in-package-of-symbol
                   (concatenate 'string "EVAL_SUBPROGRAM-" (symbol-name suffix) "1")
                   'asl-pkg) . ,rest))
       (& (cons (find-eval_subprogram-def-and-rename suffix (car x))
                (find-eval_subprogram-def-and-rename suffix (cdr x))))))))

(local
 (defun add-define-to-defines (def x)
   (if (atom x)
       x
     (case-match x
       (('defines arg . rest)
        (if (and (symbolp arg)
                 (not (keywordp arg)))
            `(defines ,arg ,def . ,rest)
          `(defines ,def ,arg . ,rest)))
       (& (cons (add-define-to-defines def (car x))
                (add-define-to-defines def (cdr x))))))))

(local
 (defun add-trace-to-returns (x)
   (if (atom x)
       x
     (case-match x
       ((':returns x . rest)
        `(:returns (,@x (trace asl-tracelist-p)) . ,rest))
       (& (cons (add-trace-to-returns (car x))
                (add-trace-to-returns (cdr x))))))))

(local
 (defun wrap-define-bodies (macro x)
   (if (atom x)
       x
     (if (and (eq (car x) 'define)
              (true-listp x))
         (let ((len (len x)))
           (update-nth (1- len)
                       (list macro (nth (1- len) x))
                       x))
       (cons (wrap-define-bodies macro (car x))
             (wrap-define-bodies macro (cdr x)))))))



  






(local
 (defun eval-return-equiv-thms (names suffix wrld)
   (if (atom names)
       nil
     (cons
      (let* ((name (car names))
             (name-mod (intern-in-package-of-symbol
                        (concatenate 'string (symbol-name name) "-"
                                     (if (eq name 'eval_subprogram)
                                         (concatenate 'string (symbol-name suffix) "1")
                                       (symbol-name suffix)))
                        name))
             (macro-args (macro-args name wrld))
             (nonkey-formals (take (- (len macro-args)
                                      (len (member '&key macro-args)))
                                   macro-args)))
        `(defret ,(intern-in-package-of-symbol
                   (concatenate 'string "<FN>" "-" (symbol-name suffix) "-EQUALS-ORIGINAL")
                   'asl-pkg)
           (b* (((mv res-mod orac-mod &) (,name-mod . ,nonkey-formals))
                ((mv res orac) (,name . ,nonkey-formals)))
             (and (equal res-mod res)
                  (equal orac-mod orac)))
           :hints ((let ((expand (acl2::just-expand-cp-parse-hints
                                  '((:free (,@nonkey-formals clk orac) (,name-mod . ,nonkey-formals))
                                    (:free (,@nonkey-formals clk orac) (,name . ,nonkey-formals)))
                                  world)))
                     `(:computed-hint-replacement
                       ((acl2::expand-marked))
                       :clause-processor (acl2::mark-expands-cp
                                          clause
                                          '(t ;; last-only
                                            t ;; lambdas
                                            ,expand)))))
           :fn ,name-mod))
      (eval-return-equiv-thms (cdr names) suffix wrld)))))

(local
 (defun equals-original-thm (suffix wrld)
   (let ((eval_subprogram-mod (intern-in-package-of-symbol
                               (concatenate 'string "EVAL_SUBPROGRAM-" (symbol-name suffix))
                               'eval_subprogram)))
     `(std::defret-mutual
        ,(intern-in-package-of-symbol
          (concatenate 'string (symbol-name suffix) "-EQUALS-ORIGINAL")
          'asl-pkg)
        (defret ,(intern-in-package-of-symbol
                  (concatenate 'string "EVAL_SUBPROGRAM-" (symbol-name suffix)
                               "-EQUALS-ORIGINAL")
                  'asl-pkg)
          (b* (((mv res-mod orac-mod &) (,eval_subprogram-mod
                                         env name vparams vargs))
               ((mv res orac) (eval_subprogram env name vparams vargs)))
            (and (equal res-mod res)
                 (equal orac-mod orac)))
          :hints ((let ((expand (acl2::just-expand-cp-parse-hints
                                 '((:free (env name vparams vargs clk orac)
                                    (,eval_subprogram-mod env name vparams vargs)))
                                 world)))
                    `(:computed-hint-replacement
                      ((acl2::expand-marked))
                      :clause-processor (acl2::mark-expands-cp
                                         clause
                                         '(t ;; last-only
                                           t ;; lambdas
                                           ,expand)))))
          :fn ,eval_subprogram-mod)
        . ,(eval-return-equiv-thms *asl-interp-fns* suffix wrld)))))

(local
 (defun insert-after-/// (forms x)
   (if (atom x)
       x
     (if (eq (car x) '///)
         (cons '/// forms)
       (cons (insert-after-/// forms (car x))
             (insert-after-/// forms (cdr x)))))))

(local
 (defun add-mutrec-xdoc (xdoc x)
   (if (atom x)
       x
     (case-match x
       (('defines name . rest)
        `(defines ,name ,@xdoc . ,rest))
       (& (cons (add-mutrec-xdoc xdoc (car x))
                (add-mutrec-xdoc xdoc (cdr x))))))))

(local
 (defun add-define-xdoc (short x)
   (declare (xargs :mode :program))
   (if (atom x)
       x
     (case-match x
       (('define name formals . rest)
        `(define ,name ,formals
           :short ,(acl2::template-subst short
                                         :string-str-alist
                                         `(("<NAME>" . ,(symbol-name name))))
           . ,rest))
       (& (cons (add-define-xdoc short (car x))
                (add-define-xdoc short (cdr x))))))))


(local (defconst *asl-*ft-xdoc*
         '(:parents (asl-tracing)
           :short "Modified version of @(see asl-interpreter-mutual-recursion) that collects a
full trace of all subprogram calls."
           :long "
<p>This is an automatically generated derived version of the ASL interpreter,
@(see asl-interpreter-mutual-recursion).  Each function in this mutual
recursion returns the same two values as the analogous function in the original
interpreter, and a third value that is an @(see asl-tracelist).</p>

<p>The exception to this rule is that whereas @('eval_subprogram-*ft1') is
derived from @(see eval_subprogram) and returns the tracelist of subprograms
called within the subprogram call, a wrapper @('eval_subprogram-*ft') produces
the trace for the whole subroutine call; calls of @('eval_subprogram')
therefore get translated into calls of @('eval_subprogram-*ft') because they
want to collect the trace including the outer subprogram call, not all the
calls within that call.</p>

<p>These functions produce the full trace of all subroutine calls, hence the
@('*ft') suffix.</p>")))








(local (in-theory (disable (tau-system)
                           len assoc-equal append true-listp loghead hons-assoc-equal floor mod expt take
                           acl2::repeat)))


(local (xdoc::set-default-parents asl-interpreter-mutual-recursion-*ft))

;; Assumptions about the syntax of the interpeter definition form:
;;  - Only the one occurrence of ///
;;  - No auxiliary functions defined in :prepwork
;;  - Each define form has its body last (after all keyword args).

;; ---------------------------------------------------------------------------
;; Definition of the Full-Tracing ASL Interpreter (suffixed with *t)
(make-event
 (b* ((form *asl-interpreter-mutual-recursion-command*)
      ;; Strip out the events after the /// (theorem about resolved-p-of-resolve-ty)
      (form (strip-post-/// form))
      ;; Strip out xdoc
      (form (strip-xdoc form))
      ;; Add xdoc topic for mutual recursion
      (form (add-mutrec-xdoc *asl-*ft-xdoc* form))
      ;; Add xdoc topic for each function
      (form (add-define-xdoc
             "Full Tracing version of @(see <NAME>); see @(see asl-interpreter-mutual-recursion-*ft) for overview."
             form))
      ;; Replace '(define eval_subprogram ...' with '(define eval_subprogram-*ft1'
      ;; since it's going to be wrapped in a call that deals with collecting the trace data.
      (form (find-eval_subprogram-def-and-rename '*ft form))
      ;; Substitute function names with their -*ft suffixed forms.
      (form (sublis *eval-fulltrace-substitution* form))
      ;; Wrap each define body in a call of evbody-*ft.
      (form (wrap-define-bodies 'evbody-*ft form))
      ;; Add (trace asl-tracelist-p) to all the :returns forms.
      (form (add-trace-to-returns form))
      ;; Add the definition of eval_subprogram-*ft which wraps around eval_subprogram-*ft1.
      (form (add-define-to-defines *eval_subprogram-*ft-def* form))
      ;; Disable the functions, prove the non-trace return values equal to the originals, and verify guards.
      (form (insert-after-///
             (list
              '(make-event
                `(in-theory (disable . ,(fgetprop 'eval_expr-*ft-fn 'acl2::recursivep nil (w state)))))
              (equals-original-thm '*ft (w state))
              '(verify-guards eval_expr-*ft-fn))
             form)))
   
   `(progn (defconst *asl-interpreter-mutual-recursion-*ft-form* ',form)
           ,form)))
;; ---------------------------------------------------------------------------





(defprod tracespec-entry
  :parents (asl-tracing)
  :short "Entry describing what information should be collected in the trace for a given function."
  ((paramsp booleanp)
   (argsp booleanp)
   (globalsp booleanp)
   (resultp booleanp))
  :layout :list)


(local (in-theory (enable hons-assoc-equal)))
(fty::defmap tracespec :key-type identifier :val-type tracespec-entry
  :valp-of-nil nil :keyp-of-nil nil :true-listp t
  :parents (asl-tracing)
  :short "Specifies what information should be collected in the trace for a given subprogram.")








(defconsts *eval-trace-substitution*
  (append (pair-suffixed (append '(asl-interpreter-mutual-recursion) *asl-interp-fns*) '-*t)
          *eval-fulltrace-substitution*))



(local (defconst *asl-*t-xdoc*
         '(:parents (asl-tracing)
           :short "Modified version of @(see asl-interpreter-mutual-recursion) that collects a
trace of a specified set of subprogram calls."
           :long "
<p>This is an automatically generated derived version of the ASL interpreter,
@(see asl-interpreter-mutual-recursion).  Each function in this mutual
recursion returns the same two values as the analogous function in the original
interpreter, and a third value that is an @(see asl-tracelist).</p>

<p>The exception to this rule is that whereas @('eval_subprogram-*t1') is
derived from @(see eval_subprogram) and returns the tracelist of subprograms
called within the subprogram call, a wrapper @('eval_subprogram-*t') produces
the trace for the whole subroutine call; calls of @('eval_subprogram')
therefore get translated into calls of @('eval_subprogram-*ft') because they
want to collect the trace including the outer subprogram call, not all the
calls within that call.</p>

<p>These functions produce a trace as specified by an added @(see tracespec)
argument. For each subprogram call, if that subprogram has an entry in the
tracespec, then it produces a trace entry with information populated or elided
according to the @(see tracespec-entry) it is mapped to. Otherwise, it returns
the trace of any sub-calls within the body that are traced according to the
tracespec.</p>")))

(local
 (defconst *eval_subprogram-*t-def*
   '(define eval_subprogram-*t ((env env-p)
                                 (name identifier-p)
                                 (vparams vallist-p)
                                 (vargs vallist-p)
                                 &key
                                 ((clk natp) 'clk)
                                 (orac 'orac)
                                 ((pos posn-p) 'pos)
                                 ((tracespec tracespec-p) 'tracespec))
      :short "Tracing version of @(see eval_subprogram); see @(see
asl-interpreter-mutual-recursion-*t) for overview."
      :measure (nats-measure clk 1 0 1)
      :returns (mv (eval func_eval_result-p) new-orac
                   (trace asl-tracelist-p))
      (b* (((mv res orac trace) (eval_subprogram-*t1 env name vparams vargs))
           (tracespec-entry (cdr (hons-get (identifier-fix name) (tracespec-fix tracespec))))
           ((unless tracespec-entry)
            (mv res orac trace))
           ((tracespec-entry entry) tracespec-entry)
           (trace (list (make-asl-trace
                         :fn name
                         :params (and entry.paramsp vparams)
                         :args (and entry.argsp vargs)
                         :globals-in (and entry.globalsp (global-env->storage (env->global env)))
                         :calls (acl2::rev trace)
                         :result (if entry.resultp
                                     res
                                   (ev_error "Not tracing result" nil nil))
                         :pos pos))))
        (mv res orac trace)))))


(local
 (defun add-define-formals (new-formals x)
   (if (atom x)
       x
     (case-match x
       (('define name formals . rest)
        `(define ,name ,(append formals new-formals) . ,rest))
       (& (cons (add-define-formals new-formals (car x))
                (add-define-formals new-formals (cdr x))))))))
 


(local (xdoc::set-default-parents asl-interpreter-mutual-recursion-*t))

;; ---------------------------------------------------------------------------
;; Definition of the Tracing ASL Interpreter (suffixed with *t)
(make-event
 (b* ((form *asl-interpreter-mutual-recursion-command*)
      ;; Strip out the events after the /// (theorem about resolved-p-of-resolve-ty)
      (form (strip-post-/// form))
      ;; Strip out xdoc
      (form (strip-xdoc form))
      ;; Add xdoc topic for mutual recursion
      (form (add-mutrec-xdoc *asl-*t-xdoc* form))
      ;; Add xdoc topic for each function
      (form (add-define-xdoc
             "Tracing version of @(see <NAME>); see @(see asl-interpreter-mutual-recursion-*t) for overview."
             form))
      ;; Replace '(define eval_subprogram ...' with '(define eval_subprogram-*ft1'
      ;; since it's going to be wrapped in a call that deals with collecting the trace data.
      (form (find-eval_subprogram-def-and-rename '*t form))
      ;; Substitute function names with their -*t suffixed forms.
      (form (sublis *eval-trace-substitution* form))
      ;; Wrap each define body in a call of evbody-*ft.
      (form (wrap-define-bodies 'evbody-*ft form))
      ;; Add (trace asl-tracelist-p) to all the :returns forms.
      (form (add-trace-to-returns form))
      ;; Add the tracespec formal to each define form.
      (form (add-define-formals '(((tracespec tracespec-p) 'tracespec)) form))
      ;; Add the definition of eval_subprogram-*t which wraps around eval_subprogram-*t1.
      (form (add-define-to-defines *eval_subprogram-*t-def* form))
      ;; Disable the functions, prove the non-trace return values equal to the originals, and verify guards.
      (form (insert-after-///
             (list
              '(make-event
                `(in-theory (disable . ,(fgetprop 'eval_expr-*t-fn 'acl2::recursivep nil (w state)))))
              (equals-original-thm '*t (w state))
              '(verify-guards eval_expr-*t-fn))
             form)))
   `(progn (defconst *asl-interpreter-mutual-recursion-*t-form* ',form)
           ,form)))
;; ---------------------------------------------------------------------------


(define find-define (name x)
  (if (atom x)
      nil
    (case-match x
      (('define !name . &) x)
      (& (or (find-define name (car x))
             (find-define name (cdr x)))))))
