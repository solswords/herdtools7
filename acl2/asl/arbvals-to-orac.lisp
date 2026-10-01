;;****************************************************************************;;
;;                                ASLRef                                      ;;
;;****************************************************************************;;
;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause

(in-package "ASL")

(include-book "arbvals")
(local (std::add-default-post-define-hook :fix))

;; Translate an execution of the arbmap interpreter into the ordered sequence
;; of types and values read by ARBITRARY expressions.  Encoding that sequence
;; with typed-vallist-to-oracle supplies an oracle for the original interpreter.

(defmacro evo_normal-*ato (arg)
  `(mv (ev_normal ,arg) ato-types ato-vals))

(define pass-error-*ato ((val eval_result-p) ato-types ato-vals)
  :guard (eval_result-case val :ev_error)
  :inline t
  :enabled t
  (mv (ev_error-fix val) ato-types ato-vals))

(defmacro evo_error-*ato (&rest args)
  `(pass-error-*ato (ev_error . ,args) ato-types ato-vals))

(defmacro evo_throwing-*ato (&rest args)
  `(mv (ev_throwing . ,args) ato-types ato-vals))

(defmacro evo-return-*ato (arg)
  `(mv ,arg ato-types ato-vals))

(defmacro evtailcall-*ato (call)
  `(b* (((mv res ato-types1 ato-vals1) ,call)
        (ato-types (append ato-types ato-types1))
        (ato-vals (append ato-vals ato-vals1)))
     (mv res ato-types ato-vals)))

(defun ato-call-to-*a-fn (ato-call)
  (declare (xargs :mode :program))
  (b* (((cons ato-fn args) ato-call)
       (name (symbol-name ato-fn))
       (fnp (str::strsuffixp "-FN" name))
       (a-fn (intern-in-package-of-symbol
              (concatenate 'string
                           (subseq name 0 (- (length name) (if fnp 7 4)))
                           (if fnp "*A-FN" "*A"))
              ato-fn)))
    (cons a-fn args)))

(defmacro ato-call-to-*a (ato-call)
  (ato-call-to-*a-fn ato-call))

(defmacro add-arboffset-for-form-*ato (arboffset form)
  (let* ((form (ato-call-to-*a-fn form))
         (form-arboffset (add-arboffsets-for-form-args
                          (cdr form)
                          (cdr (assoc (car form) *arboffset-for-form-table*)))))
    (if form-arboffset
        `(arbaddr-offset-sum ,form-arboffset ,arboffset)
      arboffset)))

(acl2::def-b*-binder evbind-*ato
  :body
  `(b* (((mv ,(car acl2::args) ato-types1 ato-vals1) . ,acl2::forms)
        (?arboffset (add-arboffset-for-form-*ato arboffset . ,acl2::forms))
        (ato-types (append ato-types ato-types1))
        (ato-vals (append ato-vals ato-vals1)))
     ,acl2::rest-expr))

(acl2::def-b*-binder evbind-nonrec-*ato
  :body
  `(b* (((mv ,(car acl2::args) ato-types1 ato-vals1) . ,acl2::forms)
        (ato-types (append ato-types ato-types1))
        (ato-vals (append ato-vals ato-vals1)))
     ,acl2::rest-expr))

(acl2::def-b*-binder evo-*ato
  :body
  `(b* ((evresult ,(car acl2::forms)))
     (eval_result-case evresult
       :ev_normal (b* ,(and (not (eq (car acl2::args) '&))
                           `((,(car acl2::args) evresult.res)))
                    ,acl2::rest-expr)
       :otherwise (mv (eval_result-nonnormal-fix evresult) ato-types ato-vals))))

(acl2::def-b*-binder evoo-*ato
  :body
  `(b* (((evbind-*ato evoo-*ato-tmp) . ,acl2::forms)
        ((evo-*ato ,(car acl2::args)) evoo-*ato-tmp))
     (acl2::check-vars-not-free (evoo-*ato-tmp) ,acl2::rest-expr)))

(acl2::def-b*-binder evs-*ato
  :body
  `(b* (((evoo-*ato cflow) ,(car acl2::forms)))
     (control_flow_state-case cflow
       :returning (evo_normal-*ato
                   (mbe :logic (returning cflow.vals cflow.env)
                        :exec cflow))
       :continuing (b* ,(and (not (eq (car acl2::args) '&))
                             `((,(car acl2::args) cflow.env)))
                     ,acl2::rest-expr))))

(acl2::def-b*-binder evoo-*ato-special
  :body
  `(b* (((evbind-nonrec-*ato evoo-*ato-tmp) . ,acl2::forms)
        ((evo-*ato ,(car acl2::args)) evoo-*ato-tmp))
     (acl2::check-vars-not-free (evoo-*ato-tmp) ,acl2::rest-expr)))

(acl2::def-b*-binder evs-*ato-special
  :body
  `(b* (((evoo-*ato-special cflow) ,(car acl2::forms)))
     (control_flow_state-case cflow
       :returning (evo_normal-*ato
                   (mbe :logic (returning cflow.vals cflow.env)
                        :exec cflow))
       :continuing (b* ,(and (not (eq (car acl2::args) '&))
                             `((,(car acl2::args) cflow.env)))
                     ,acl2::rest-expr))))

(acl2::def-b*-binder evob-*ato
  :body
  `(b* ((evresult ,(car acl2::forms)))
     (eval_result-case evresult
       :ev_normal (b* ,(and (not (eq (car acl2::args) '&))
                            `((,(car acl2::args) evresult.res)))
                    ,acl2::rest-expr)
       :ev_throwing (evo-return-*ato
                     (init-backtrace (ev_throwing-fix evresult)
                                     (local-env->storage (env->local env)) pos))
       :otherwise (pass-error-*ato
                   (init-backtrace (ev_error-fix evresult)
                                   (local-env->storage (env->local env)) pos)
                   ato-types ato-vals))))

(defmacro evbody-*ato (body)
  `(let ((ato-types nil) (ato-vals nil)) ,body))

(defconst *e_arbitrary-*ato-def*
  '(b* (((evoo-*ato ty) (resolve-ty-*ato env desc.type))
        (val (arbmap-lookup
              (cons (arbaddr-component-arb
                     (arbaddr-offset->arboffset arboffset))
                    arbaddr)
              ty arbmap))
        ((unless val)
         (evo_error-*ato "DE_AET: " desc (list pos)))
        (ato-types (append ato-types (list ty)))
        (ato-vals (append ato-vals (list val))))
     (evo_normal-*ato (expr_result val env))))

(local (defconst *asl-*ato-case-replacements*
         `((:e_arbitrary . ,*e_arbitrary-*ato-def*))))

(local (defconst *asl-*ato-xdoc*
         '(:parents (asl-interpreter-functions)
           :short "Translate an arbmap execution into oracle input.")))

(defun pair-ato-names (fns)
  (declare (xargs :mode :program))
  (if (atom fns)
      nil
    (cons (cons (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name (car fns)) "-*A")
                 (car fns))
                (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name (car fns)) "-*ATO")
                 (car fns)))
          (pair-ato-names (cdr fns)))))

(defconst *eval-*ato-substitution*
  (list* (cons 'evs-*a-special 'evs-*ato-special)
         (cons 'add-arboffset-for-form 'add-arboffset-for-form-*ato)
         (pair-ato-names
          (append *asl-interp-fns*
                  '(evo_normal pass-error evo_error evo_throwing evo-return
                    evbind evbind-nonrec evoo evo evob evs evtailcall
                    asl-interpreter-mutual-recursion)))))

(local
 (defun add-ato-returns (x)
   (if (atom x)
       x
     (case-match x
       ((':returns res . rest)
        `(:returns (mv ,res (ato-types tylist-p) (ato-vals vallist-p)) . ,rest))
       (& (cons (add-ato-returns (car x))
                (add-ato-returns (cdr x))))))))

(defthm tylist-p-of-append-*ato
  (implies (and (tylist-p x) (tylist-p y))
           (tylist-p (append x y))))

(defthm vallist-p-of-append-*ato
  (implies (and (vallist-p x) (vallist-p y))
           (vallist-p (append x y))))

(encapsulate nil
  (local (in-theory (disable (:t eval_result-kind)
                             (:t append)
                             (:t pass-error)
                             (:t val-kind)
                             (:t acl2::true-listp-append)
                             (:t eval_expr)
                             (:t expr_result->env)
                             (:t expr_result->val)
                             (:t ev_error)
                             (:t pass-error-*a)
                             (:t ev_normal)
                             default-car default-cdr (tau-system))))
  (with-output
    :off (event)
    (make-event
     (b* ((form *asl-interpreter-mutual-recursion-*a-form*)
          (form (strip-xdoc form))
          (form (add-mutrec-xdoc *asl-*ato-xdoc* form))
          (form (add-define-xdoc
                 "Oracle-input translator for @(see <NAME>)." form))
          (form (sublis *eval-*ato-substitution* form))
          (form (add-ato-returns form))
          (form (replace-case-bodies form *asl-*ato-case-replacements*))
          (form (wrap-define-bodies 'evbody-*ato form)))
       `(progn (defconst *asl-interpreter-mutual-recursion-*ato-form* ',form)
               ,form)))))

(local (deflabel before-ato-equals-*a))

(encapsulate nil
  (local (in-theory (acl2::disable* equal-of-ev_normal
                                    equal-of-ev_throwing
                                    equal-of-ev_error
                                    equal-of-continuing
                                    equal-of-returning
                                    (tau-system))))
  (with-output
    :evisc (:gag-mode (evisc-tuple 3 4 nil nil))
    (std::defret-mutual-generate <fn>-equals-*a
      :rules ((t (:add-concl (equal res (ato-call-to-*a <call>))))
              ((not (:fnname eval_limit-*ato))
               (:add-keyword
                :hints ((and stable-under-simplificationp
                             '(:expand ((:free (pos otherwise is_while clk) <call>)
                                        (:free (pos otherwise is_while clk)
                                         (ato-call-to-*a <call>))))))))
              ((:fnname eval_limit-*ato)
               (:add-keyword
                :hints ((and stable-under-simplificationp
                             '(:expand ((:free (pos otherwise is_while x) <call>)
                                        (:free (pos otherwise is_while x)
                                         (ato-call-to-*a <call>)))))))))
      :mutual-recursion asl-interpreter-mutual-recursion-*ato)))

(acl2::def-ruleset! asl-*ato-equals-*a-rules
  (set-difference-equal (current-theory :here)
                        (current-theory 'before-ato-equals-*a)))

(local (in-theory (acl2::disable* asl-*ato-equals-*a-rules)))

(defun ato-append-induct (vals1 types1)
  (if (consp types1)
      (ato-append-induct (cdr vals1) (cdr types1))
    vals1))

(defthm tuple-type-satisfied-of-append-*ato
  (implies (and (vallist-p vals1)
                (tylist-p types1)
                (tuple-type-satisfied vals1 types1)
                (tuple-type-satisfied vals2 types2))
           (tuple-type-satisfied (append vals1 vals2)
                                 (append types1 types2)))
  :hints (("Goal" :induct (ato-append-induct vals1 types1)
           :in-theory (enable tuple-type-satisfied))))

(defthm tuple-type-satisfied-of-arbmap-lookup-*ato
  (implies (ty-satisfiable ty)
           (tuple-type-satisfied (list (arbmap-lookup addr ty arbmap))
                                 (list ty)))
  :hints (("Goal" :in-theory (enable tuple-type-satisfied))))

(with-output
  :evisc (:gag-mode (evisc-tuple 3 4 nil nil))
  (std::defret-mutual-generate <fn>-logs-satisfied
    :rules ((t (:add-concl (tuple-type-satisfied ato-vals ato-types)))
            ((not (:fnname eval_limit-*ato))
             (:add-keyword
              :hints ((and stable-under-simplificationp
                           '(:expand ((:free (pos otherwise is_while clk) <call>)))))))
            ((:fnname eval_limit-*ato)
             (:add-keyword
              :hints ((and stable-under-simplificationp
                           '(:expand ((:free (pos otherwise is_while x) <call>))))))))
    :mutual-recursion asl-interpreter-mutual-recursion-*ato))


(defun ato-call-to-orig-fn (ato-call)
  (declare (xargs :mode :program))
  (b* (((cons ato-fn args) ato-call)
       (name (symbol-name ato-fn))
       (fnp (str::strsuffixp "-FN" name))
       (a-fn (intern-in-package-of-symbol
              (concatenate 'string
                           (subseq name 0 (- (length name) (if fnp 8 5)))
                           (if fnp "-FN" ""))
              ato-fn))
       (new-args (append (set-difference-equal args '(arbaddr arbmap arboffset loop-iter loop-idx))
                         '(orac))))
    (cons a-fn new-args)))

(defmacro ato-call-to-orig (ato-call)
  (ato-call-to-orig-fn ato-call))


(local (include-book "std/lists/append" :dir :system))

(encapsulate nil
  (local (defun my-ind (x y)
           (if (atom y)
               x
             (my-ind (cdr x) (cdr y)))))
  
  (defthm typed-vallist-to-oracle-of-append
    (implies (tuple-type-satisfied vals1 tys1)
             (equal (typed-vallist-to-oracle (append tys1 tys2)
                                             (append vals1 vals2))
                    (append (typed-vallist-to-oracle tys1 vals1)
                            (typed-vallist-to-oracle tys2 vals2))))
    :hints(("Goal" :in-theory (enable typed-vallist-to-oracle append tuple-type-satisfied)
            :induct (my-ind vals1 tys1)))))
                          




;; (local (defthm check_int_constraints-*ato-of-ifix
;;          (equal (check_int_constraints-*ato env (ifix i) constrs)
;;                 (check_int_constraints-*ato env i constrs))
;;          :hints (("goal" :expand ((check_int_constraints-*ato env (ifix i) constrs)
;;                                   (check_int_constraints-*ato env i constrs))))))

(encapsulate nil
  ;; (local (include-book "std/lists/nth" :dir :system))
  ;; (local (include-book "std/lists/update-nth" :dir :system))

  (local (in-theory (disable 
                                 ;; performance optimizing
                                 acl2::prefixp-when-equal-lengths
                                 acl2::prefixp-when-prefixp
                                 ;; acl2::nth-when-too-large-cheap
                                 len not
                                 acl2::len-when-prefixp
                                 acl2::nth-when-prefixp
                                 acl2::prefixp-one-way-or-another
                                 acl2::prefixp-of-append-arg1
                                 acl2::prefixp-transitive
                                 acl2::prefixp-when-not-consp-right)))

  (local
   (defthm my-prefixp-of-append
     (equal (acl2::prefixp (append x y) z)
            (and (acl2::prefixp x z)
                 (acl2::prefixp y (nthcdr (len x) z))))
     :hints(("Goal" :in-theory (enable acl2::prefixp nthcdr len)))))
  
  (local (defthm nthcdr-of-nthcdr
           (equal (nthcdr n (nthcdr m x))
                  (nthcdr (+ (nfix n) (nfix m)) x))))


  (local (defthm oracle-st-of-nthcdr-orac
           (equal (nth 1 (nthcdr-orac n orac))
                  (nthcdr n (nth 1 orac)))
           :hints(("Goal" :in-theory (enable nthcdr-orac)))))

  (local (defthm oracle-mode-of-nthcdr-orac
           (equal (nth 0 (nthcdr-orac n orac))
                  (nth 0 orac))
           :hints(("Goal" :in-theory (enable nthcdr-orac)))))

  (local (defthm redundant-update-nth
           (equal (update-nth n v (update-nth n v1 x))
                  (update-nth n v x))
           :hints(("Goal" :in-theory (enable update-nth)))))
  
  (local (defthm nthcdr-orac-of-nthcdr-orac
           (equal (nthcdr-orac n (nthcdr-orac m orac))
                  (nthcdr-orac (+ (nfix n) (nfix m)) orac))
           :hints(("Goal" :in-theory (enable nthcdr-orac)))))

  (local (defthm nthcdr-orac-of-0
           (equal (nthcdr-orac 0 orac) orac)
           :hints(("Goal" :in-theory (enable nthcdr-orac)))))

  (local (defthm typed-vallist-to-oracle-of-singletons
           (equal (typed-vallist-to-oracle (list ty) (list val))
                  (typed-val-to-oracle ty val))
           :hints (("goal" :expand ((typed-vallist-to-oracle (list ty) (list val)))))))

  (local (defthm typed-val-to-oracle-correct-match
           (implies (and (equal orac-st (acl2::oracle-st orac))
                         (acl2::prefixp (typed-val-to-oracle ty val) orac-st)
                         (equal (acl2::oracle-mode orac) 3)
                         (ty-satisfied val ty))
                    (equal (ty-oracle-val ty orac)
                           (mv (val-fix val)
                               (nthcdr-orac (len (typed-val-to-oracle ty val)) orac))))
           :hints (("goal" :use ((:instance typed-val-to-oracle-correct
                                  (x ty)))
                    :in-theory (disable typed-val-to-oracle-correct)))))

  (local (in-theory (acl2::e/d* ()
                                ;; these congruences each mess up the matching of one of the defun-sks
                                (CHECK_INT_CONSTRAINTS-FN-OF-IFIX-I
                                 CHECK_INT_CONSTRAINTS-FN-INT-EQUIV-CONGRUENCE-ON-I
                                 EVAL_LOOP-FN-IFF-CONGRUENCE-ON-IS_WHILE
                                 eval_expr-fn-nat-equiv-congruence-on-clk
                                 eval_expr-fn-of-nfix-clk
                                 eval_expr_list-fn-nat-equiv-congruence-on-clk
                                 eval_expr_list-fn-of-nfix-clk
                                 EVAL_LOOP-FN-NAT-EQUIV-CONGRUENCE-ON-CLK
                                 eval_loop-fn-of-nfix-clk
                                 EVAL_BLOCK-FN-NAT-EQUIV-CONGRUENCE-ON-CLK
                                 eval_block-fn-of-nfix-clk
                                 EVAL_CALL-FN-NAT-EQUIV-CONGRUENCE-ON-CLK
                                 eval_call-fn-of-nfix-clk
                                 resolve-int_constraints-fn-posn-equiv-congruence-on-pos
                                 resolve-int_constraints-fn-of-posn-fix-pos

                                 ;; don't expand nth/update-nth
                                 nth update-nth
                                 ;; acl2::update-nth-of-cons
                                 ;; acl2::update-nth-when-zp
                                 ;; acl2::nth-when-zp
                                 nth-add1
                             
                                 ;; avoid case splitting, just need the rules below
                                 nthcdr-orac

                                 (tau-system)
                                 nthcdr append
                                 
                                 (:rules-of-class :type-prescription :here)
                                 (:rules-of-class :congruence :here)
                                 (:rules-of-class :rewrite-quoted-constant :here))
                                ((:t len)))))

  (with-output
    :evisc (:gag-mode (evisc-tuple 3 4 nil nil))
    :off (event warning prove)
    :summary-off :all :summary-on (acl2::form time)
    (std::defret-mutual-generate original-replicates-<fn>
      :rules ((t (:add-concl
                  (b* ((orac-prefix (typed-vallist-to-oracle ato-types ato-vals)))
                    (implies (and (equal (acl2::oracle-mode orac) 3)
                                  (acl2::prefixp orac-prefix
                                                 (acl2::oracle-st orac)))
                             (b* (((mv orig-res orig-orac)
                                   (ato-call-to-orig <call>)))
                               (and (equal orig-res res)
                                    (equal orig-orac (nthcdr-orac (len orac-prefix) orac))))))))
              ((not (:fnname eval_limit-*ato))
               (:add-keyword
                :hints ((and stable-under-simplificationp
                             `(:expand (,(car (last clause)))))
                        (and stable-under-simplificationp
                             '(:expand ((:free (pos otherwise is_while clk) <call>)
                                        (:free (pos otherwise is_while clk orac)
                                         (ato-call-to-orig <call>)))
                               :do-not-induct t)))))
              ((:fnname eval_limit-*ato)
               (:add-keyword
                :hints ((and stable-under-simplificationp
                             `(:expand (,(car (last clause)))))
                        (and stable-under-simplificationp
                             '(:expand ((:free (pos otherwise is_while x) <call>)
                                        (:free (pos otherwise is_while x orac)
                                         (ato-call-to-orig <call>)))
                               :do-not-induct t))))))
      :universally-quantify (orac)
      :mutual-recursion asl-interpreter-mutual-recursion-*ato)))
