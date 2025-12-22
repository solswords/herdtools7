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

(in-package "TAC")

(include-book "logic")
(include-book "centaur/meta/fixed-evaluator" :dir :system)
(include-book "clause-processors/ev-theoremp" :dir :system)
(local (include-book "std/lists/sets" :dir :System))
(local (std::add-default-post-define-hook :fix))

(cmr::defevaluator-fixed tac-ev tac-ev-lst
  ((emptyset)
   (universe)
   (singleton s)
   (setunion s1 s2)
   (setintersect s1 s2)
   (setimage s r)
   (setpreimage r s)
   (relidentity s)
   (relunion r1 r2)
   (relintersect r1 r2)
   (relcompose r1 r2)
   (relstar r)
   (relstar-bounded n r)
   (relplus r)
   (relinverse r)
   (relprod s1 s2)
   (pred-false)
   (pred-true)
   (pred-nonempty s)
   (pred-equal e1 e2)
   (pred-in-set e s)
   (pred-in-rel e1 e2 r)
   (base-set-p x)
   (base-rel-p x)
   (not-singleton-set-p x)
   (mentioned-event-p x)
   
   (event-p x)
   (event-set-p x)
   (relation-p x)

   (if a b c)
   (implies a b)
   (equal a b)
   (iff a b)
   (not x)
   (return-last x y z)

   (typespec-check ts x))
  :namedp t)

(defthm len-of-tac-ev-lst
  (equal (len (tac-ev-lst x a))
         (len x)))

(include-book "clause-processors/pseudo-term-fty" :Dir :system)

(acl2::def-ev-pseudo-term-fty-support tac-ev tac-ev-lst)

(include-book "std/util/defenum" :dir :system)

(defenum tac-type-p (:event :set :rel :count :pred nil))

(fty::deflist tac-typelist :elt-type tac-type-p :true-listp t)

(fty::defmap type-ctx :key-type pseudo-var :val-type tac-type-p :true-listp t
  ///
  (defthm tac-type-p-of-cdr-assoc-when-type-ctx-p
    (implies (type-ctx-p x)
             (tac-type-p (cdr (assoc-equal k x))))))

(define tac-typed-val-p (val (type tac-type-p))
  (case (tac-type-fix type)
    (:event (event-p val))
    (:set (event-set-p val))
    (:count (natp val))
    (:rel   (relation-p val))
    (:pred (booleanp val))
    (t t))
  ///
  (defthm tac-typed-val-p-of-nil-type
    (tac-typed-val-p x nil))

  ;; (defthm tac-typed-val-p-implies-event
  ;;   (implies (tac-typed-val-p val :event)
  ;;            (event-p val)))

  ;; (defthm tac-typed-val-p-implies-set
  ;;   (implies (tac-typed-val-p val :set)
  ;;            (and (setp val) (event-set-p val))))
  
  ;; (defthm tac-typed-val-p-implies-rel
  ;;   (implies (tac-typed-val-p val :rel)
  ;;            (and (relation-p val) (event-rel-p val))))
  )

(define tac-typed-vallist-p ((vals true-listp) (types tac-typelist-p))
  :measure (len types)
  (if (atom types)
      t
    (and (tac-typed-val-p (car vals) (car types))
         (tac-typed-vallist-p (cdr vals) (cdr types)))))

(define tac-1typed-vallist-p ((vals true-listp) (type tac-type-p))
  (if (atom vals)
      t
    (and (tac-typed-val-p (car vals) type)
         (tac-1typed-vallist-p (cdr vals) type))))

(include-book "centaur/meta/parse-rewrite" :Dir :system)

(define tac-typed-env-p-aux ((vars cmr::pseudo-var-list-p)
                             (env alistp)
                             (ctx type-ctx-p))
  (if (atom vars)
      t
    (and (tac-typed-val-p (cdr (assoc-eq (pseudo-var-fix (car vars)) env))
                          (cdr (assoc-eq (pseudo-var-fix (car vars)) (type-ctx-fix ctx))))
         (tac-typed-env-p-aux (cdr vars) env ctx)))
  ///
  (defthm tac-typed-env-p-aux-implies-lookup
    (implies (and (tac-typed-env-p-aux vars env ctx)
                  (member-equal v (cmr::pseudo-var-list-fix vars)))
             (tac-typed-val-p (cdr (assoc-eq v env))
                              (cdr (assoc-equal v (type-ctx-fix ctx)))))
    :hints(("Goal" :in-theory (enable type-ctx-fix)))))

(define tac-typed-env-p ((env alistp) (ctx type-ctx-p))
  :prepwork ((local (defthm pseudo-var-list-p-alist-keys-of-type-ctx
                      (implies (type-ctx-p x)
                               (cmr::pseudo-var-list-p (acl2::alist-keys x)))
                      :hints(("Goal" :in-theory (enable type-ctx-p acl2::alist-keys
                                                        cmr::pseudo-var-list-p))))))
  (tac-typed-env-p-aux (acl2::alist-keys (type-ctx-fix ctx)) env ctx)
  ///

  (local (Defthm member-alist-keys-of-type-ctx
           (implies (type-ctx-p x)
                    (iff (member-equal v (acl2::alist-keys x))
                         (assoc-equal v x)))
           :hints(("Goal" :in-theory (enable type-ctx-p acl2::alist-keys)))))
  
  (defthm tac-typed-env-p-implies-lookup
    (implies (and (tac-typed-env-p env ctx)
                  (assoc-equal v (type-ctx-fix ctx))
                  (pseudo-var-p v))
             (tac-typed-val-p (cdr (assoc-eq v env))
                              (cdr (assoc-equal v (type-ctx-fix ctx))))))

  (defthm tac-typed-env-p-implies-lookup-event-p
    (implies (and (tac-typed-env-p env ctx)
                  (equal (cdr (assoc-equal v (type-ctx-fix ctx))) :event)
                  (pseudo-var-p v))
             (event-p (cdr (assoc-eq v env))))
    :hints (("goal" :use tac-typed-env-p-implies-lookup
             :in-theory (e/d (tac-typed-val-p) (tac-typed-env-p-implies-lookup)))))

  (defthm tac-typed-env-p-implies-lookup-event-set-p
    (implies (and (tac-typed-env-p env ctx)
                  (equal (cdr (assoc-equal v (type-ctx-fix ctx))) :set)
                  (pseudo-var-p v))
             (and  (setp (cdr (assoc-eq v env)))
                   (event-set-p (cdr (assoc-eq v env)))))
    :hints (("goal" :use tac-typed-env-p-implies-lookup
             :in-theory (e/d (tac-typed-val-p) (tac-typed-env-p-implies-lookup)))))

  (defthm tac-typed-env-p-implies-lookup-relation-p
    (implies (and (tac-typed-env-p env ctx)
                  (equal (cdr (assoc-equal v (type-ctx-fix ctx))) :rel)
                  (pseudo-var-p v))
             (relation-p (cdr (assoc-eq v env))))
    :hints (("goal" :use tac-typed-env-p-implies-lookup
             :in-theory (e/d (tac-typed-val-p) (tac-typed-env-p-implies-lookup)))))

  (defthm tac-typed-env-p-implies-lookup-natp
    (implies (and (tac-typed-env-p env ctx)
                  (equal (cdr (assoc-equal v (type-ctx-fix ctx))) :count)
                  (pseudo-var-p v))
             (natp (cdr (assoc-eq v env))))
    :hints (("goal" :use tac-typed-env-p-implies-lookup
             :in-theory (e/d (tac-typed-val-p) (tac-typed-env-p-implies-lookup)))))

  (defthm tac-typed-env-p-implies-lookup-booleanp
    (implies (and (tac-typed-env-p env ctx)
                  (equal (cdr (assoc-equal v (type-ctx-fix ctx))) :pred)
                  (pseudo-var-p v))
             (booleanp (cdr (assoc-eq v env))))
    :hints (("goal" :use tac-typed-env-p-implies-lookup
             :in-theory (e/d (tac-typed-val-p) (tac-typed-env-p-implies-lookup))))))


(include-book "tools/easy-simplify" :dir :system)

(defconst *tac-function-argument-types*
  '((emptyset)
    (universe)
    (singleton :event)
    (setunion :set :set)
    (setintersect :set :set)
    (setimage :set :rel)
    (setpreimage :rel :set)
    (relidentity :set)
    (relunion :rel :rel)
    (relintersect :rel :rel)
    (relcompose :rel :rel)
    (relstar :rel)
    (relstar-bounded :count :rel)
    (relplus :rel)
    (relinverse :rel)
    (relprod :set :set)
    (pred-false)
    (pred-true)
    (pred-nonempty :set)
    (pred-equal :event :event)
    (pred-in-set :event :set)
    (pred-in-rel :event :event :rel)
    (not :pred)))

(defconst *tac-function-return-types*
  '((emptyset . :set)
    (universe . :set)
    (singleton . :set)
    (setunion . :set)
    (setintersect . :set)
    (setimage . :set)
    (setpreimage . :set)
    (relidentity . :rel)
    (relunion . :rel)
    (relintersect . :rel)
    (relcompose . :rel)
    (relstar . :rel)
    (relstar-bounded . :rel)
    (relplus . :rel)
    (relinverse . :rel)
    (relprod . :rel)
    (pred-false . :pred)
    (pred-true . :pred)
    (pred-nonempty . :pred)
    (pred-equal . :pred)
    (pred-in-set . :pred)
    (pred-in-rel . :pred)
    (not . :pred)))

(define tac-function-return-type ((x pseudo-fnsym-p))
  :returns (type tac-type-p)
  (cdr (assoc-eq (pseudo-fnsym-fix x) *tac-function-return-types*)))

(define tac-function-argument-types ((x pseudo-fnsym-p))
  :returns (types tac-typelist-p)
  (cdr (assoc-eq (pseudo-fnsym-fix x) *tac-function-argument-types*))
  ///
  (defret member-nil-of-<fn>
    (not (member nil types))))



(defines tac-term-type
  :flag-local nil
  (define tac-term-type ((x pseudo-termp) (ctx type-ctx-p))
    :measure (pseudo-term-count x)
    :returns (type tac-type-p)
    (pseudo-term-case x
      :var (cdr (assoc-eq x.name (type-ctx-fix ctx)))
      :const nil ;; ?
      :lambda nil
      :fncall (b* ((rettype (tac-function-return-type x.fn)))
                (and rettype
                     (acl2::prefixp (tac-function-argument-types x.fn)
                                    (tac-termlist-types x.args ctx))
                     rettype))))
  (define tac-termlist-types ((x pseudo-term-listp)
                              (ctx type-ctx-p))
    :measure (pseudo-term-list-count x)
    :returns (types tac-typelist-p)
    (if (atom x)
        nil
      (cons (tac-term-type (car x) ctx)
            (tac-termlist-types (cdr x) ctx))))
  ///
  (defthm consp-of-tac-termlist-types
    (iff (consp (tac-termlist-types x ctx))
         (consp x))
    :hints (("goal" :expand ((tac-termlist-types x ctx)
                             (tac-termlist-types nil ctx)))))
  (defthm cdr-of-tac-termlist-types
    (equal (cdr (tac-termlist-types x ctx))
           (tac-termlist-types (cdr x) ctx))
    :hints (("goal" :expand ((tac-termlist-types x ctx)
                             (tac-termlist-types nil ctx)))))

  (defthm car-of-tac-termlist-types
    (equal (car (tac-termlist-types x ctx))
           (tac-term-type (car x) ctx))
    :hints (("goal" :expand ((tac-termlist-types x ctx)
                             (tac-termlist-types nil ctx)))))

  (defthm tac-termlist-types-of-append
    (equal (Tac-termlist-types (append x y) ctx)
           (append (tac-termlist-types x ctx)
                   (tac-termlist-types y ctx)))
    :hints (("goal" :induct (append x y)
             :expand ((:free (a b) (tac-termlist-types (cons a b) ctx))))))

  

  (local (defthm open-prefixp
           (equal (acl2::prefixp (cons a b) x)
                  (and (consp x)
                       (equal (car x) a)
                       (acl2::prefixp b (cdr x))))
           :hints(("Goal" :in-theory (enable acl2::prefixp)))))

  (local (defthm prefixp-of-nil
           (acl2::prefixp nil x)
           :hints(("Goal" :in-theory (enable acl2::prefixp)))))
  
  (local (in-theory (disable tac-term-type tac-termlist-types)))
  
  (std::defret-mutual tac-typed-val-p-when-term-type
    (defret tac-typed-val-p-when-term-type
      (implies (tac-typed-env-p env ctx)
               (tac-typed-val-p (tac-ev x env) type))
      :hints ('(:expand (<call>
                         (:free (a b x) (tac-typed-vallist-p (cons a b) x)))
                :in-theory (enable tac-function-return-type
                                   tac-typed-val-p
                                   tac-function-argument-types)))
      :fn tac-term-type)
    (defret tac-typed-vallist-p-when-termlist-types
      (implies (tac-typed-env-p env ctx)
               (tac-typed-vallist-p (tac-ev-lst x env) types))
      :hints ('(:expand (<call>
                         (:free (a b x) (tac-typed-vallist-p x (cons a b))))))
      :fn tac-termlist-types))

  (defret type-of-tac-ev-by-term-type
    (implies (tac-typed-env-p env ctx)
             (and (implies (equal type :set)
                           (event-set-p (tac-ev x env)))
                  (implies (equal type :rel)
                           (relation-p (tac-ev x env)))
                  (implies (equal type :event)
                           (event-p (tac-ev x env)))))
    :hints (("Goal" :use tac-typed-val-p-when-term-type
             :in-theory (e/d (tac-typed-val-p)
                             (tac-typed-val-p-when-term-type))))
    :fn tac-term-type)

  (fty::deffixequiv-mutual tac-term-type)
  
  (defret tac-typed-val-p-when-equal-term-type
    (implies (and (tac-typed-env-p env ctx)
                  (equal (tac-type-fix ty) type))
             (tac-typed-val-p (tac-ev x env) ty))
    :hints (("goal" :use tac-typed-val-p-when-term-type
             :in-theory (disable tac-typed-val-p-when-term-type)))
    :fn tac-term-type)

  (defret tac-typed-vallist-p-when-equal-termlist-types
    (implies (and (tac-typed-env-p env ctx)
                  (equal (tac-typelist-fix tys) types))
             (tac-typed-vallist-p (tac-ev-lst x env) tys))
    :hints (("goal" :use tac-typed-vallist-p-when-termlist-types
             :in-theory (disable tac-typed-vallist-p-when-termlist-types)))
    :fn tac-termlist-types)

  (std::defret-mutual tac-term-type-of-add-unused
    (defret tac-term-type-of-add-unused-var
      (implies (not (member-equal var (cmr::term-vars x)))
               (equal (tac-term-type x (cons (cons var typ) ctx))
                      type))
      :hints ('(:expand ((:free (ctx) <call>)
                         (cmr::term-vars x))))
      :fn tac-term-type)
    (defret tac-termlist-types-of-add-unused-var
      (implies (not (member-equal var (cmr::termlist-vars x)))
               (equal (tac-termlist-types x (cons (cons var typ) ctx))
                      types))
      :hints ('(:expand ((:free (ctx) <call>)
                         (cmr::termlist-vars x))))
      :fn tac-termlist-types))



  (acl2::defopen tac-term-type-when-var
    (tac-term-type x ctx)
    :hyp (acl2::pseudo-term-case x :var)
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-const
    (tac-term-type x ctx)
    :hyp (acl2::pseudo-term-case x :const)
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-lambda
    (tac-term-type x ctx)
    :hyp (acl2::pseudo-term-case x :lambda)
    :hint (:expand ((tac-term-type x ctx))))


  (acl2::defopen tac-term-type-when-fncall-with-no-return-type
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (not (tac-function-return-type (acl2::pseudo-term-fncall->fn x))))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-fncall-with-return-type
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (tac-function-return-type (acl2::pseudo-term-fncall->fn x)))
    :hint (:expand ((tac-term-type x ctx))))

  )

(define tac-subst-ctx ((x cmr::pseudo-term-subst-p)
                       (ctx type-ctx-p))
  :returns (subst-ctx type-ctx-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (pseudo-var-p (caar x))))
        (cons (cons (caar x)
                    (tac-term-type (cdar x) ctx))
              (tac-subst-ctx (cdr x) ctx))
      (tac-subst-ctx (cdr x) ctx)))
  ///
  (defret assoc-equal-of-<fn>
    (equal (assoc-equal var subst-ctx)
           (and (pseudo-var-p var)
                (let ((look (assoc-equal var x)))
                  (and look
                       (cons var (tac-term-type (cdr look) ctx)))))))
  (local (in-theory (enable cmr::pseudo-term-subst-fix))))

(defthm-tac-term-type-flag
  (defthm tac-term-type-of-term-subst-strict
    (equal (tac-term-type (cmr::term-subst-strict x subst) ctx)
           (tac-term-type x (tac-subst-ctx subst ctx)))
    :hints ('(:expand ((cmr::term-subst-strict x subst))))
    :flag tac-term-type)
  (defthm tac-termlist-type-of-termlist-subst-strict
    (equal (tac-termlist-types (cmr::termlist-subst-strict x subst) ctx)
           (tac-termlist-types x (tac-subst-ctx subst ctx)))
    :hints ('(:expand ((cmr::termlist-subst-strict x subst)
                       (tac-termlist-types nil ctx)
                       (:free (ctx) (tac-termlist-types x ctx))
                       (:free (a b) (tac-termlist-types (cons a b) ctx)))))
    :flag tac-termlist-types))


(acl2::def-ev-theoremp tac-ev)

(define tac-ev-cube ((x pseudo-term-listp) (env alistp))
  :verify-guards nil
  (if (atom x)
      t
    (and (tac-ev (car x) env)
         (tac-ev-cube (cdr x) env)))
  ///
  (defthm tac-ev-of-conjoin
    (iff (tac-ev (acl2::conjoin lst) env)
         (tac-ev-cube lst env))
    :hints(("Goal" :in-theory (enable tac-ev-cube))))

  (defthm tac-ev-cube-of-append
    (iff (tac-ev-cube (append x y) env)
         (and (tac-ev-cube x env)
              (tac-ev-cube y env)))))

(define tac-ev-theoremp* ((x pseudo-termp))
  :verify-guards nil
  (and (tac-ev-theoremp x) t)
  ///
  (in-theory (disable (tac-ev-theoremp*)))
  (defthm tac-ev-theoremp*-implies
    (implies (tac-ev-theoremp* x)
             (tac-ev x a))
    :hints (("goal" :use tac-ev-falsify)))

  (defthmd tac-ev-theoremp*-expand
    (iff (tac-ev-theoremp* x)
         (tac-ev x (tac-ev-falsify x)))
    :rule-classes :definition)

  (fty::deffixequiv tac-ev-theoremp*
    :hints ((and stable-under-simplificationp
                 (b* ((lit (assoc 'tac-ev clause))
                      (xx (cadr (caddr lit)))
                      (other (if (eq xx 'x) '(acl2::pseudo-term-fix$inline x) 'x)))
                   `(:use ((:instance tac-ev-falsify
                            (x ,other) (a (tac-ev-falsify ,xx))))))))))

(define tac-ev-theoremlist-p ((x pseudo-term-listp))
  :verify-guards nil
  (if (atom x)
      t
    (and (tac-ev-theoremp* (car x))
         (tac-ev-theoremlist-p (cdr x)))))


(define tac-ev-alist ((x cmr::pseudo-term-subst-p) a)
  :verify-guards nil
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (pseudo-var-p (caar x))))
        (cons (cons (caar x) (tac-ev (cdar x) a))
              (tac-ev-alist (cdr x) a))
      (tac-ev-alist (cdr x) a)))
  ///

  (defthm lookup-in-tac-ev-alist-split
    (equal (assoc k (tac-ev-alist x a))
           (and (pseudo-var-p k)
                (let ((look (assoc k x)))
                  (and look
                       (cons k (tac-ev (cdr look) a)))))))

  (defthm hons-assoc-equal-lookup-in-tac-ev-alist-split
    (equal (hons-assoc-equal k (tac-ev-alist x a))
           (and (pseudo-var-p k)
                (let ((look (hons-assoc-equal k x)))
                  (and look
                       (cons k (tac-ev (cdr look) a)))))))

  (defthm tac-typed-env-p-of-tac-ev-alist
    (implies (tac-typed-env-p env ctx)
             (tac-typed-env-p
              (tac-ev-alist x env)
              (tac-subst-ctx x ctx)))
    :hints(("Goal" :in-theory (enable tac-ev-alist tac-subst-ctx
                                      tac-typed-env-p
                                      acl2::alist-keys
                                      tac-typed-env-p-aux))))

  (defthm alist-keys-of-tac-ev-alist
    (equal (acl2::alist-keys (tac-ev-alist x env))
           (acl2::alist-keys (cmr::pseudo-term-subst-fix x)))
    :hints(("Goal" :in-theory (enable cmr::pseudo-term-subst-fix
                                      acl2::alist-keys))))
  
  (local (in-theory (enable cmr::pseudo-term-subst-fix))))

(defthm tac-ev-of-term-subst-strict
  (equal (tac-ev (cmr::term-subst-strict x a) env)
         (tac-ev x (tac-ev-alist a env)))
  :hints (("goal" :use ((:instance
                         (:functional-instance cmr::base-ev-of-term-subst-strict
                          (cmr::base-ev tac-ev)
                          (cmr::base-ev-list tac-ev-lst)
                          (cmr::base-ev-alist tac-ev-alist))
                         (x x) (a a) (env env)))
           :in-theory (enable tac-ev-alist))))

(defthm tac-ev-lst-of-termlist-subst-strict
  (equal (tac-ev-lst (cmr::termlist-subst-strict x a) env)
         (tac-ev-lst x (tac-ev-alist a env)))
  :hints (("goal" :use ((:instance
                         (:functional-instance cmr::base-ev-list-of-termlist-subst-strict
                          (cmr::base-ev tac-ev)
                          (cmr::base-ev-list tac-ev-lst)
                          (cmr::base-ev-alist tac-ev-alist))
                         (x x) (a a) (env env)))
           :in-theory (enable tac-ev-alist))))

(defthm tac-ev-cube-of-termlist-subst-strict
  (equal (tac-ev-cube (cmr::termlist-subst-strict x a) env)
         (tac-ev-cube x (tac-ev-alist a env)))
  :hints(("Goal" :in-theory (enable tac-ev-cube cmr::termlist-subst-strict))))


