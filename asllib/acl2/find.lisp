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
(include-book "centaur/fty/visitor" :dir :system)
(include-book "centaur/fty/multicase" :dir :system)




(acl2::def-b*-binder find-posn-return
  :decls ((declare (ignore acl2::args)))
  :body `(or ,@acl2::forms ,acl2::rest-expr))

(fty::defvisitor-template find-posn-of-call ((fn identifier-p) (x :object))
  :returns (call-pos (:ignore :return nil)
                     (iff (posn-p call-pos) call-pos))
  :binder find-posn-return
  :renames ((expr find-posn-of-call-expr-aux)
            (stmt find-posn-of-call-stmt-aux))
  :type-fns ((expr find-posn-of-call-expr)
             (stmt find-posn-of-call-stmt))
  :fnname-template find-posn-of-call-<type>)

(fty::defvisitor-multi find-posn-of-call-expr
  (define find-posn-of-call-expr ((fn identifier-p)
                                  (x expr-p))
    :returns (call-pos (iff (posn-p call-pos) call-pos))
    :measure (acl2::nat-list-measure (list (expr-count x) 1))
    (b* (((expr x))
         ((when (expr_desc-case x.desc
                  :e_call (equal (call->name x.desc.call) (identifier-fix fn))
                  :otherwise nil))
          x.pos_start))
      (find-posn-of-call-expr-aux fn x)))

  (fty::defvisitors :template find-posn-of-call
    :types (expr)
    :measure (acl2::nat-list-measure (list :count 0))))

(set-bogus-measure-ok t)
(fty::defvisitors find-posn-of-call-stmt-deps
  :template find-posn-of-call
  :dep-types (stmt)
  :measure (acl2::nat-list-measure (list :count 0)))


(local
 (set-default-hints
  '((and stable-under-simplificationp '(:in-theory (enable maybe-stmt-some->val))))))

(fty::defvisitor-multi find-posn-of-call-stmt
  (define find-posn-of-call-stmt ((fn identifier-p)
                                  (x stmt-p))
    :returns (call-pos (iff (posn-p call-pos) call-pos))
    :measure (acl2::nat-list-measure (list (stmt-count x) 1))
    (b* (((stmt x))
         ((when (stmt_desc-case x.desc
                  :s_call (equal (call->name x.desc.call) (identifier-fix fn))
                  :otherwise nil))
          x.pos_start))
      (find-posn-of-call-stmt-aux fn x)))

  (fty::defvisitors :template find-posn-of-call
    :types (stmt)
    :measure (acl2::nat-list-measure (list :count 0))))
  

(define find-posn-of-call-in-function ((called-function identifier-p)
                                       (context-function identifier-p)
                                       (static-env static_env_global-p))
  :returns (call-pos (iff (posn-p call-pos) call-pos))
  (B* (((static_env_global static-env))
       (fn-look (hons-assoc-equal (identifier-fix context-function)
                                  static-env.subprograms))
       ((unless fn-look)
        nil)
       ((func-ses func) (cdr fn-look))
       ((func func.fn))
       ((unless (subprogram_body-case func.fn.body :sb_asl))
        nil)
       ((sb_asl body) func.fn.body))
    (find-posn-of-call-stmt called-function body.stmt)))


(local (include-book "std/lists/append" :dir :system))
(fty::deflist posnlist :elt-type posn :true-listp t :elementp-of-nil nil)


(fty::defvisitor-template find-posns-of-calls ((fn identifier-p) (x :object))
  :returns (call-posns (:join (append call-posns1 call-posns)
                        :tmp-var call-posns1
                        :initial nil)
                       posnlist-p)
  :renames ((expr find-posns-of-calls-expr-aux)
            (stmt find-posns-of-calls-stmt-aux))
  :type-fns ((expr find-posns-of-calls-expr)
             (stmt find-posns-of-calls-stmt))
  :fnname-template find-posns-of-calls-<type>)

(fty::defvisitor-multi find-posns-of-calls-expr
  (define find-posns-of-calls-expr ((fn identifier-p)
                                  (x expr-p))
    :returns (call-posns posnlist-p)
    :measure (acl2::nat-list-measure (list (expr-count x) 1))
    (b* (((expr x))
         ((when (expr_desc-case x.desc
                  :e_call (equal (call->name x.desc.call) (identifier-fix fn))
                  :otherwise nil))
          (cons x.pos_start
                (find-posns-of-calls-expr-aux fn x))))
      (find-posns-of-calls-expr-aux fn x)))

  (fty::defvisitors :template find-posns-of-calls
    :types (expr)
    :measure (acl2::nat-list-measure (list :count 0))))

(set-bogus-measure-ok t)
(fty::defvisitors find-posns-of-calls-stmt-deps
  :template find-posns-of-calls
  :dep-types (stmt)
  :measure (acl2::nat-list-measure (list :count 0)))


(local
 (set-default-hints
  '((and stable-under-simplificationp '(:in-theory (enable maybe-stmt-some->val))))))

(fty::defvisitor-multi find-posns-of-calls-stmt
  (define find-posns-of-calls-stmt ((fn identifier-p)
                                  (x stmt-p))
    :returns (call-posns posnlist-p)
    :measure (acl2::nat-list-measure (list (stmt-count x) 1))
    (b* (((stmt x))
         ((when (stmt_desc-case x.desc
                  :s_call (equal (call->name x.desc.call) (identifier-fix fn))
                  :otherwise nil))
          (cons x.pos_start
                (find-posns-of-calls-stmt-aux fn x))))
      (find-posns-of-calls-stmt-aux fn x)))

  (fty::defvisitors :template find-posns-of-calls
    :types (stmt)
    :measure (acl2::nat-list-measure (list :count 0))))
  

(define find-posns-of-calls-in-function ((called-function identifier-p)
                                       (context-function identifier-p)
                                       (static-env static_env_global-p))
  :returns (call-posns posnlist-p)
  (B* (((static_env_global static-env))
       (fn-look (hons-assoc-equal (identifier-fix context-function)
                                  static-env.subprograms))
       ((unless fn-look)
        nil)
       ((func-ses func) (cdr fn-look))
       ((func func.fn))
       ((unless (subprogram_body-case func.fn.body :sb_asl))
        nil)
       ((sb_asl body) func.fn.body))
    (find-posns-of-calls-stmt called-function body.stmt)))




(local (table fty::deftagsum-defaults :short-names t))

(acl2::def-b*-binder writes-var-return
  :decls ((declare (ignore acl2::args)))
  :body `(or ,@acl2::forms ,acl2::rest-expr))

(fty::defvisitor-template writes-var ((var identifier-p) (x :object))
  :returns (writes (:ignore :return nil))
  :binder writes-var-return
  :renames ((lexpr lexpr-writes-var-aux))
  :type-fns ((lexpr lexpr-writes-var))
  :fnname-template <type>-writes-var)


(fty::defvisitor-multi lexpr-writes-var
  (define lexpr-writes-var ((var identifier-p)
                            (x lexpr-p))
    :returns (writes)
    :measure (acl2::nat-list-measure (list (lexpr-count x) 1))
    (b* (((lexpr x)))
      (or (lexpr_desc-case x.desc
            :le_var (equal x.desc.name (identifier-fix var))
            :le_setcollectionfields (equal x.desc.base (identifier-fix var))
            :otherwise nil)
          (lexpr-writes-var-aux var x))))

  (fty::defvisitors :template writes-var
    :types (lexpr)
    :measure (acl2::nat-list-measure (list :count 0))))



(fty::defoption maybe-literal literal)
(fty::defoption maybe-binop binop-p)
(fty::defoption maybe-unop unop-p)

(fty::deftypes expr-matcher
  (deftagsum expr-matcher
    (:em_contains     ((matcher expr-matcher)))
    (:em_literal      ((val maybe-literal-p)))
    (:em_var          ((name maybe-identifier-p)))
    (:em_atc          ((type maybe-expr-matcher)))
    (:em_binop        ((op maybe-binop-p)
                       (arg1 maybe-expr-matcher)
                       (arg2 maybe-expr-matcher)))
    (:em_unop         ((op maybe-unop-p)
                       (arg maybe-expr-matcher)))
    (:em_call         ((fn maybe-identifier-p)
                       (params maybe-expr-matcher-list)
                       (args maybe-expr-matcher-list)))
    (:em_slice        ((expr maybe-expr-matcher)))
    (:em_cond         ((test maybe-expr-matcher)
                       (then maybe-expr-matcher)
                       (else maybe-expr-matcher)))
    (:em_getarray     ((base maybe-expr-matcher)
                       (index maybe-expr-matcher)))
    (:em_getenumarray ((base maybe-expr-matcher)
                       (index maybe-expr-matcher)))
    (:em_getfield     ((base maybe-expr-matcher)
                       (field maybe-identifier-p)))
    (:em_getfields    ((base maybe-expr-matcher)
                       (field maybe-identifier-p)))
    (:em_getcollectionfields ((base maybe-identifier-p)
                              (field maybe-identifier-p)))
    (:em_getitem      ((base maybe-expr-matcher)
                       (index acl2::maybe-integerp)))
    (:em_record       ((type maybe-expr-matcher)
                       (fields maybe-expr-matcher)))
    (:em_tuple        ((exprs maybe-expr-matcher-list)))
    (:em_array        ((length maybe-expr-matcher)
                       (value maybe-expr-matcher)))
    (:em_enumarray    ((enum maybe-identifier-p)
                       (value maybe-expr-matcher)))
    (:em_arbitrary    ((type maybe-expr-matcher)))
    (:em_pattern      ((expr maybe-expr-matcher)
                       (pattern maybe-expr-matcher)))
    :measure (acl2::two-nats-measure (+ 1 (acl2-count x)) 1))
  (fty::defoption maybe-expr-matcher expr-matcher
    :measure (acl2::two-nats-measure (if x (+ 1 (acl2-count x)) 0) 3)
    :post-acc-events ((local (in-theory (enable maybe-expr-matcher-some->val)))))
  (fty::deflist maybe-expr-matcher-list :elt-type maybe-expr-matcher
    :true-listp t :elementp-of-nil t
    :measure (acl2::two-nats-measure (+ 1 (acl2-count x)) 0)))


(local (in-theory (disable acl2-count)))

(defthm expr-matcher-count-<-maybe-expr-matcher-count
  (implies matcher
           (< (expr-matcher-count matcher)
              (maybe-expr-matcher-count matcher)))
  :hints (("goal" :expand ((maybe-expr-matcher-count matcher))
           :in-theory (enable maybe-expr-matcher-some->val)))
  :rule-classes ((:linear :trigger-terms ((maybe-expr-matcher-count matcher)))))

(local (defthm maybe-expr-matcher-fix-when-matcher
         (implies matcher
                  (equal (maybe-expr-matcher-fix matcher)
                         (expr-matcher-fix matcher)))
         :hints(("Goal" :in-theory (enable maybe-expr-matcher-fix)))))



(fty::defvisitor-template find-matching-exprs ((matcher expr-matcher-p) (x :object))
  :returns (exprs (:join (append exprs exprs1)
                        :tmp-var exprs1
                        :initial nil)
                       exprlist-p)
  :renames ((expr find-matching-exprs-in-expr-aux))
  :type-fns ((expr find-matching-exprs-in-expr))
  :fnname-template find-matching-exprs-in-<type>)



(local (defthm exprlist-p-of-append
         (implies (and (exprlist-p x)
                       (exprlist-p y))
                  (exprlist-p (append x y)))))


(with-output
  :evisc (:gag-mode '(nil 7 10 nil))
  (fty::defvisitor-multi expr-match
    (define expr-match ((matcher expr-matcher-p)
                        (x expr-p))
      :measure (acl2::nat-list-measure (list (expr-count x) (expr-matcher-count matcher) 0))
      (b* (((expr x)))
        (fty::multicase
          ((expr-matcher-case matcher)
           (expr_desc-case x.desc))
          ((:em_contains            -)                      (consp (find-matching-exprs-in-expr matcher.matcher x)))
          ((:em_literal             :e_literal)             (or (not matcher.val)
                                                                (equal x.desc.val matcher.val)))
          ((:em_var                 :e_var)                 (or (not matcher.name)
                                                                (equal x.desc.name matcher.name)))
          ((:em_atc                 :e_atc)                 (or (not matcher.type)
                                                                (consp (find-matching-exprs-in-ty matcher.type x.desc.type))))
          ((:em_binop               :e_binop)               (and (or (not matcher.op)
                                                                     (eq matcher.op x.desc.op))
                                                                 (expr-maybe-match matcher.arg1 x.desc.arg1)
                                                                 (expr-maybe-match matcher.arg2 x.desc.arg2)))
          ((:em_unop                :e_unop)                (and (or (not matcher.op)
                                                                     (eq matcher.op x.desc.op))
                                                                 (expr-maybe-match matcher.arg x.desc.arg)))
          ((:em_call                :e_call)                (and (or (not matcher.fn)
                                                                     (equal matcher.fn (call->name x.desc.call)))
                                                                 (expr-match-list matcher.args (call->args x.desc.call))))
          ((:em_slice               :e_slice)               (expr-maybe-match matcher.expr x.desc.expr))
          ((:em_cond                :e_cond)                (and (expr-maybe-match matcher.test x.desc.test)
                                                                 (expr-maybe-match matcher.then x.desc.then)
                                                                 (expr-maybe-match matcher.else x.desc.else)))
          ((:em_getarray            :e_getarray)            (and (expr-maybe-match matcher.base x.desc.base)
                                                                 (expr-maybe-match matcher.index x.desc.index)))
          ((:em_getfield            :e_getfield)            (and (expr-maybe-match matcher.base x.desc.base)
                                                                 (or (not matcher.field)
                                                                     (equal matcher.field x.desc.field))))
          ((:em_getfields           :e_getfields)           (and (expr-maybe-match matcher.base x.desc.base)
                                                                 (or (not matcher.field)
                                                                     (member-equal matcher.field x.desc.fields))))
          ((:em_getcollectionfields :e_getcollectionfields) (and (or (not matcher.base)
                                                                     (equal matcher.base x.desc.base))
                                                                 (or (not matcher.field)
                                                                     (member-equal matcher.field x.desc.fields))))
          ((:em_getitem             :e_getitem)             (and (expr-maybe-match matcher.base x.desc.base)
                                                                 (or (not matcher.index)
                                                                     (eql matcher.index x.desc.index))))
          ((:em_record              :e_record)              (and (or (not matcher.type)
                                                                     (consp (find-matching-exprs-in-ty matcher.type x.desc.type)))
                                                                 (or (not matcher.fields)
                                                                     (consp (find-matching-exprs-in-named_exprlist matcher.fields x.desc.fields)))))
          ((:em_tuple               :e_tuple)               (expr-match-list matcher.exprs x.desc.exprs))
          ((:em_array               :e_array)               (and (expr-maybe-match matcher.length x.desc.length)
                                                                 (expr-maybe-match matcher.value x.desc.value)))
          ((:em_enumarray           :e_enumarray)           (and (or (not matcher.enum)
                                                                     (equal matcher.enum x.desc.enum))
                                                                 (expr-maybe-match matcher.value x.desc.value)))
          ((:em_arbitrary           :e_arbitrary)           (or (not matcher.type)
                                                                (consp (find-matching-exprs-in-ty matcher.type x.desc.type))))
          ((:em_pattern             :e_pattern)             (and (expr-maybe-match matcher.expr x.desc.expr)
                                                                 (or (not matcher.pattern)
                                                                     (consp (find-matching-exprs-in-pattern matcher.pattern x.desc.pattern)))))
          ((- -) nil))))

    (define expr-maybe-match ((matcher maybe-expr-matcher-p)
                              (x expr-p))
      :measure (acl2::nat-list-measure (list (expr-count x) (maybe-expr-matcher-count matcher) 0))
      (or (not matcher)
          (expr-match matcher x)))
  
    (define expr-match-list ((matcher maybe-expr-matcher-list-p)
                             (x exprlist-p))
      :measure (acl2::nat-list-measure (list (exprlist-count x) (maybe-expr-matcher-list-count matcher) 0))
      (if (atom matcher)
          t
        (and (consp x)
             (expr-maybe-match (car matcher) (car x))
             (expr-match-list (cdr matcher) (cdr x)))))

    (define find-matching-exprs-in-expr ((matcher expr-matcher-p)
                                         (x expr-p))
      :measure (acl2::nat-list-measure (list (expr-count x) (expr-matcher-count matcher) 1))
      :returns (exprs exprlist-p)
      (if (expr-match matcher x)
          (list (expr-fix x))
        (find-matching-exprs-in-expr-aux matcher x)))

    (fty::defvisitors :template find-matching-exprs
      :types (expr)
      :measure (acl2::nat-list-measure (list :count 0 0)))))

(fty::defvisitors find-matching-exprs-in-stmt
  :template find-matching-exprs
  :types (stmt)
  :measure (acl2::nat-list-measure (list :count 0 0)))

(fty::deftypes stmt-matcher
  (deftagsum stmt-matcher
    (:sm_contains ((matcher stmt-matcher-p)))
    (:sm_hasexpr  ((matcher expr-matcher-p)))
    (:sm_pass ())
    (:sm_decl ((name maybe-identifier-p)
               (ty maybe-expr-matcher)
               (expr maybe-expr-matcher)))
    (:sm_assign ((lexpr maybe-expr-matcher)
                 (expr maybe-expr-matcher)))
    (:sm_call ((fn maybe-identifier-p)
               (params maybe-expr-matcher-list)
               (args maybe-expr-matcher-list)))
    (:sm_return ((expr maybe-expr-matcher)))
    (:sm_cond ((test maybe-expr-matcher)
               (then maybe-stmt-matcher)
               (else maybe-stmt-matcher)))
    (:sm_assert ((expr maybe-expr-matcher)))
    (:sm_for ((index_name maybe-identifier)
              (start_e maybe-expr-matcher)
              (end_e maybe-expr-matcher)
              (body maybe-stmt-matcher)
              (limit maybe-expr-matcher)))
    (:sm_while ((test maybe-expr-matcher)
                (limit maybe-expr-matcher)
                (body maybe-stmt-matcher)))
    (:sm_repeat ((body maybe-stmt-matcher)
                 (test maybe-expr-matcher)
                 (limit maybe-expr-matcher)))
    (:sm_throw ((val maybe-expr-matcher)))
    (:sm_try ((body maybe-stmt-matcher)
              (catchers maybe-stmt-matcher)
              (otherwise maybe-stmt-matcher)))
    (:sm_print ((args maybe-expr-matcher-list)))
    (:sm_unreachable ())
    (:sm_pragma ((exprs maybe-expr-matcher-list)))
    :measure (acl2::two-nats-measure (+ 1 (acl2-count x)) 1))
  (fty::defoption maybe-stmt-matcher stmt-matcher
    :measure (acl2::two-nats-measure (if x (+ 1 (acl2-count x)) 0) 3)
    :post-acc-events ((local (in-theory (enable maybe-stmt-matcher-some->val)))))
  (fty::deflist maybe-stmt-matcher-list :elt-type maybe-stmt-matcher
    :true-listp t :elementp-of-nil t
    :measure (acl2::two-nats-measure (+ 1 (acl2-count x)) 0)))






(defthm stmt-matcher-count-<-maybe-stmt-matcher-count
  (implies matcher
           (< (stmt-matcher-count matcher)
              (maybe-stmt-matcher-count matcher)))
  :hints (("goal" :expand ((maybe-stmt-matcher-count matcher))
           :in-theory (enable maybe-stmt-matcher-some->val)))
  :rule-classes :linear)

(defthm stmt-count-<-maybe-stmt-count
  (implies stmt
           (< (stmt-count stmt)
              (maybe-stmt-count stmt)))
  :hints (("goal" :expand ((maybe-stmt-count stmt))
           :in-theory (enable maybe-stmt-some->val)))
  :rule-classes :linear)

(local (defthm maybe-stmt-matcher-fix-when-matcher
         (implies matcher
                  (equal (maybe-stmt-matcher-fix matcher)
                         (stmt-matcher-fix matcher)))
         :hints(("Goal" :in-theory (enable maybe-stmt-matcher-fix)))))



(fty::deflist stmtlist :elt-type stmt :true-listp t :elementp-of-nil nil)

(fty::defvisitor-template find-matching-stmts ((matcher stmt-matcher-p) (x :object))
  :returns (stmts (:join (append stmts stmts1)
                        :tmp-var stmts1
                        :initial nil)
                       stmtlist-p)
  :renames ((stmt find-matching-stmts-in-stmt-aux))
  :type-fns ((stmt find-matching-stmts-in-stmt))
  :fnname-template find-matching-stmts-in-<type>)



;; (local (defthm stmtlist-p-of-append
;;          (implies (and (stmtlist-p x)
;;                        (stmtlist-p y))
;;                   (stmtlist-p (append x y)))))


(with-output
  :evisc (:gag-mode '(nil 7 10 nil))
  (fty::defvisitor-multi stmt-match
    (define stmt-match ((matcher stmt-matcher-p)
                        (x stmt-p))
      :measure (acl2::nat-list-measure (list (stmt-count x) (stmt-matcher-count matcher) 0))
      (b* (((stmt x)))
        (fty::multicase
          ((stmt-matcher-case matcher)
           (stmt_desc-case x.desc))
          ((:sm_contains            -)              (consp (find-matching-stmts-in-stmt matcher.matcher x)))
          ((:sm_hasexpr             -)              (consp (find-matching-exprs-in-stmt matcher.matcher x)))
          ((:sm_pass                :s_pass)        t)
          ((:sm_decl                :s_decl)        (and (or (not matcher.name)
                                                             (local_decl_item-case x.desc.item
                                                               :ldi_var (equal matcher.name x.desc.item.name)
                                                               :ldi_tuple (member-equal matcher.name x.desc.item.names)))
                                                         (or (not matcher.ty)
                                                             (and x.desc.ty
                                                                  (consp (find-matching-exprs-in-ty matcher.ty x.desc.ty))))
                                                         (or (not matcher.expr)
                                                             (and x.desc.expr (expr-match matcher.expr x.desc.expr)))))
          ((:sm_assign              :s_assign)      (and (or (not matcher.lexpr)
                                                             (consp (find-matching-exprs-in-lexpr matcher.lexpr x.desc.lexpr)))
                                                         (expr-maybe-match matcher.expr x.desc.expr)))
          ((:sm_call                :s_call)        (and (or (not matcher.fn)
                                                             (equal matcher.fn (call->name x.desc.call)))
                                                         (expr-match-list matcher.params (call->params x.desc.call))
                                                         (expr-match-list matcher.args (call->args x.desc.call))))
          ((:sm_return              :s_return)      (or (not matcher.expr)
                                                        (and x.desc.expr (expr-match matcher.expr x.desc.expr))))
          ((:sm_cond                :s_cond)        (and (expr-maybe-match matcher.test x.desc.test)
                                                         (stmt-maybe-match matcher.then x.desc.then)
                                                         (stmt-maybe-match matcher.else x.desc.else)))
          ((:sm_assert              :s_assert)      (expr-maybe-match matcher.expr x.desc.expr))
          ((:sm_for                 :s_for)         (and (or (not matcher.index_name)
                                                             (equal matcher.index_name x.desc.index_name))
                                                         (expr-maybe-match matcher.start_e x.desc.start_e)
                                                         (expr-maybe-match matcher.end_e x.desc.end_e)
                                                         (stmt-maybe-match matcher.body x.desc.body)
                                                         (or (not matcher.limit)
                                                             (and x.desc.limit (expr-match matcher.limit x.desc.limit)))))
          ((:sm_while               :s_while)       (and (expr-maybe-match matcher.test x.desc.test)
                                                         (or (not matcher.limit)
                                                             (and x.desc.limit (expr-match matcher.limit x.desc.limit)))
                                                         (stmt-maybe-match matcher.body x.desc.body)))
          ((:sm_repeat              :s_repeat)      (and (stmt-maybe-match matcher.body x.desc.body)
                                                         (expr-maybe-match matcher.test x.desc.test)
                                                         (or (not matcher.limit)
                                                             (and x.desc.limit (expr-match matcher.limit x.desc.limit)))))
          ((:sm_throw               :s_throw)       (or (not matcher.val)
                                                        (consp (find-matching-exprs-in-maybe-[expr*maybe-ty] matcher.val x.desc.val))))
          ((:sm_try                 :s_try)         (and (stmt-maybe-match matcher.body x.desc.body)
                                                         (or (not matcher.catchers)
                                                             (stmt-matcher-case matcher.catchers
                                                               :sm_hasexpr (consp (find-matching-exprs-in-catcherlist matcher.catchers.matcher x.desc.catchers))
                                                               :otherwise (consp (find-matching-stmts-in-catcherlist matcher.catchers x.desc.catchers))))
                                                         (or (not matcher.otherwise)
                                                             (and x.desc.otherwise
                                                                  (stmt-match matcher.otherwise x.desc.otherwise)))))
          ((:sm_print               :s_print)       (expr-match-list matcher.args x.desc.args))
          ((:sm_unreachable         :s_unreachable) t)
          ((:sm_pragma              :s_pragma)      (expr-match-list matcher.exprs x.desc.exprs))
          ((- -) nil))))

    (define stmt-maybe-match ((matcher maybe-stmt-matcher-p)
                              (x stmt-p))
      :measure (acl2::nat-list-measure (list (stmt-count x) (maybe-stmt-matcher-count matcher) 0))
      (or (not matcher)
          (stmt-match matcher x)))

    (define find-matching-stmts-in-stmt ((matcher stmt-matcher-p)
                                         (x stmt-p))
      :measure (acl2::nat-list-measure (list (stmt-count x) (stmt-matcher-count matcher) 1))
      :returns (stmts stmtlist-p)
      (if (stmt-match matcher x)
          (list (stmt-fix x))
        (find-matching-stmts-in-stmt-aux matcher x)))

    (fty::defvisitors :template find-matching-stmts
      :types (stmt)
      :measure (acl2::nat-list-measure (list :count 0 0)))))
  
