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

(include-book "interp-types")
(include-book "utils/oracle")
(include-book "centaur/fty/multicase" :dir :system)
(include-book "std/alists/alist-defuns" :dir :system)
(include-book "std/stobjs/clone" :dir :system)
(local (include-book "std/stobjs/absstobjs" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "centaur/misc/arith-equivs" :dir :System))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable ifix)))

(stobjs::defstobj-clone orac acl2::orac :pkg asl-pkg)


(define int-literal-expr-p ((x expr-p))
  (b* ((v (expr->desc x)))
    (expr_desc-case v
      :e_literal (literal-case v.val :l_int)
      :otherwise nil)))

(define int-literal-expr->val ((x expr-p))
  :guard (int-literal-expr-p x)
  :guard-hints (("goal" :in-theory (enable int-literal-expr-p)))
  :returns (val integerp :rule-classes :type-prescription)
  (l_int->val (e_literal->val (expr->desc x))))


(define int_constraint-resolved-p ((x int_constraint-p))
  (int_constraint-case x
    :constraint_exact (int-literal-expr-p x.val)
    :constraint_range (and (int-literal-expr-p x.from)
                           ;; also require from <= to?
                           (int-literal-expr-p x.to)))
  ///
  (defthm int_constraint-resolved-p-implies
    (implies (int_constraint-resolved-p x)
             (and (implies (int_constraint-case x :constraint_exact)
                           (int-literal-expr-p (constraint_exact->val x)))
                  (implies (int_constraint-case x :constraint_range)
                           (and (int-literal-expr-p (constraint_range->from x))
                                (int-literal-expr-p (constraint_range->to x))))))))

(define int_constraintlist-resolved-p ((x int_constraintlist-p))
  (if (atom x)
      t
    (and (int_constraint-resolved-p (car x))
         (int_constraintlist-resolved-p (cdr x))))
  ///
  (defthm int_constraintlist-resolved-p-implies
    (implies (int_constraintlist-resolved-p x)
             (and (int_constraintlist-resolved-p (cdr x))
                  (implies (consp x)
                           (int_constraint-resolved-p (car x)))))))
  
(define constraint_kind-resolved-p ((x constraint_kind-p))
  (constraint_kind-case x
    :unconstrained t
    :wellconstrained (int_constraintlist-resolved-p x.constraints)
    :otherwise nil)
  ///
  (defthm constraint_kind-resolved-p-implies
    (implies (constraint_kind-resolved-p x)
             (and (not (constraint_kind-case x :pendingconstrained))
                  (not (constraint_kind-case x :parametrized))
                  (implies (constraint_kind-case x :wellconstrained)
                           (int_constraintlist-resolved-p (wellconstrained->constraints x)))))))

(define array_index-resolved-p ((x array_index-p))
  (array_index-case x
    :arraylength_expr (int-literal-expr-p x.length)
    :otherwise t)
  ///
  (defthm array_index-resolved-p-implies
    (implies (and (array_index-resolved-p x)
                  (array_index-case x :arraylength_expr))
             (int-literal-expr-p (arraylength_expr->length x)))))


(defines ty-resolved-p
  (define ty-resolved-p ((x ty-p))
    :measure (ty-count x)
    (b* ((x (ty->val x)))
      (type_desc-case x
        :t_int (constraint_kind-resolved-p x.constraint)
        :t_bits (int-literal-expr-p x.expr)
        :t_tuple (tylist-resolved-p x.types)
        :t_array (and (array_index-resolved-p x.index)
                      (ty-resolved-p x.type))
        :t_record (typed_identifierlist-resolved-p x.fields)
        :t_exception (typed_identifierlist-resolved-p x.fields)
        :t_collection (typed_identifierlist-resolved-p x.fields)
        :t_named nil
        :otherwise t))
    ///
    (defthm ty_resolved-p-implies
      (implies (ty-resolved-p x)
               (b* ((x (ty->val x)))
                 (and (implies (type_desc-case x :t_int)
                               (constraint_kind-resolved-p (t_int->constraint x)))
                      (implies (type_desc-case x :t_bits)
                               (int-literal-expr-p (t_bits->expr x)))
                      (implies (type_desc-case x :t_tuple)
                               (tylist-resolved-p (t_tuple->types x)))
                      (implies (type_desc-case x :t_array)
                               (and (array_index-resolved-p (t_array->index x))
                                    (ty-resolved-p (t_array->type x))))
                      (implies (type_desc-case x :t_record)
                               (typed_identifierlist-resolved-p (t_record->fields x)))
                      (implies (type_desc-case x :t_exception)
                               (typed_identifierlist-resolved-p (t_exception->fields x)))
                      (implies (type_desc-case x :t_collection)
                               (typed_identifierlist-resolved-p (t_collection->fields x)))
                      (not (type_desc-case x :t_named)))))))

  (define tylist-resolved-p ((x tylist-p))
    :measure (tylist-count x)
    (if (atom x)
        t
      (and (ty-resolved-p (car x))
           (tylist-resolved-p (cdr x))))
    ///
    (defthm tylist-resolved-p-implies
      (implies (tylist-resolved-p x)
               (and (tylist-resolved-p (cdr x))
                    (implies (consp x)
                             (ty-resolved-p (car x)))))))

  (define typed_identifier-resolved-p ((x typed_identifier-p))
    :measure (typed_identifier-count x)
    (ty-resolved-p (typed_identifier->type x))
    ///
    (defthm typed_identifier-resolved-p-implies
      (implies (typed_identifier-resolved-p x)
               (ty-resolved-p (typed_identifier->type x)))))
  
  (define typed_identifierlist-resolved-p ((x typed_identifierlist-p))
    :measure (typed_identifierlist-count x)
    (if (atom x)
        t
      (and (typed_identifier-resolved-p (car x))
           (typed_identifierlist-resolved-p (cdr x))))
    ///
    (defthm typed_identifierlist-resolved-p-implies
      (implies (typed_identifierlist-resolved-p x)
               (and (typed_identifierlist-resolved-p (cdr x))
                    (implies (consp x)
                             (typed_identifier-resolved-p (car x)))))))
  ///
  (fty::deffixequiv-mutual ty-resolved-p))


(define int_constraint-satisfied ((x integerp)
                                  (c int_constraint-p))
  :guard (int_constraint-resolved-p c)
  (int_constraint-case c
    :constraint_exact (eql (lifix x) (int-literal-expr->val c.val))
    :constraint_range
    (and (<= (int-literal-expr->val c.from) (lifix x))
         (<= (lifix x) (int-literal-expr->val c.to)))))

(define int_constraintlist-satisfied ((x integerp)
                                      (c int_constraintlist-p))
  :guard (int_constraintlist-resolved-p c)
  (if (atom c)
      nil
    (or (int_constraint-satisfied x (car c))
        (int_constraintlist-satisfied x (cdr c)))))


(define constraint_kind-satisfied ((x integerp)
                                   (c constraint_kind-p))
  :guard (constraint_kind-resolved-p c)
  (constraint_kind-case c
    :unconstrained t
    :wellconstrained (int_constraintlist-satisfied x c.constraints)
    :otherwise nil))


(local (defthm vallist-p-vals-of-val-imap-p
         (implies (val-imap-p x)
                  (vallist-p (acl2::alist-vals x)))
         :hints(("Goal" :in-theory (enable acl2::alist-vals)))))

(defines ty-satisfied
  :flag-local nil
  (define ty-satisfied ((x val-p)
                          (ty ty-p))
    :guard (ty-resolved-p ty)
    :measure (acl2::two-nats-measure (ty-count ty) 0)
    (b* ((ty (ty->val ty)))
      (fty::multicase ((type_desc-case ty)
                       (val-case x))
        ((:t_int :v_int) (constraint_kind-satisfied x.val ty.constraint))
        ((:t_bits :v_bitvector) (eql x.len (int-literal-expr->val ty.expr)))
        ((:t_real :v_real) t)
        ((:t_string :v_string) t)
        ((:t_bool :v_bool) t)
        ((:t_enum :v_label) (member-equal x.val ty.elts))
        ((:t_tuple :v_array) (tuple-type-satisfied x.arr ty.types))
        ((:t_array :v_array)
         :when (array_index-case ty.index :arraylength_expr)
         (and (eql (len x.arr) (int-literal-expr->val (arraylength_expr->length ty.index)))
              (array-type-satisfied x.arr ty.type)))
        ((:t_array :v_record)
         :when (array_index-case ty.index :arraylength_enum)
         (and (equal (acl2::alist-keys x.rec) (arraylength_enum->elts ty.index))
              (array-type-satisfied (acl2::alist-vals x.rec) ty.type)))
        ((:t_record :v_record)
         (record-type-satisfied x.rec ty.fields))
        ((:t_exception :v_record)
         (record-type-satisfied x.rec ty.fields))
        ((:t_collection :v_record)
         (record-type-satisfied x.rec ty.fields))
        (- nil))))

  (define tuple-type-satisfied ((x vallist-p)
                                (types tylist-p))
    :guard (tylist-resolved-p types)
    :measure (acl2::two-nats-measure (tylist-count types) 0)
    (if (atom types)
        (atom x)
      (and (consp x)
           (ty-satisfied (car x) (car types))
           (tuple-type-satisfied (cdr x) (Cdr types)))))

  (define array-type-satisfied ((x vallist-p)
                                (ty ty-p))
    :guard (ty-resolved-p ty)
    :measure (acl2::two-nats-measure (ty-count ty) (len x))
    (if (atom x)
        t
      (and (ty-satisfied (car x) ty)
           (array-type-satisfied (cdr x) ty))))

  (define record-type-satisfied ((x val-imap-p)
                                 (fields typed_identifierlist-p))
    :guard (typed_identifierlist-resolved-p fields)
    :measure (acl2::two-nats-measure (typed_identifierlist-count fields) 0)
    (b* ((x (val-imap-fix x)))
      (if (atom fields)
          (atom x)
        (and (consp x)
             (consp (car x))
             (b* (((cons key val) (car x))
                  ((typed_identifier f1) (car fields)))
               (and (equal key f1.name)
                    (ty-satisfied val f1.type)))
             (record-type-satisfied (cdr x) (cdr fields))))))
  ///
  (fty::deffixequiv-mutual ty-satisfied))


(define int_constraint-satisfying-val ((x int_constraint-p))
  :guard (int_constraint-resolved-p x)
  :returns (val acl2::maybe-integerp :rule-classes :type-prescription)
  (int_constraint-case x
    :constraint_exact (int-literal-expr->val x.val)
    :constraint_range (b* ((from (int-literal-expr->val x.from))
                           (to (int-literal-expr->val x.to)))
                        (and (<= from to)
                             from)))
  ///
  (defret <fn>-correct
    (implies val
             (int_constraint-satisfied val x))
    :hints(("Goal" :in-theory (enable int_constraint-satisfied))))

  (defret <fn>-sufficient
    (implies (int_constraint-satisfied someval x)
             val)
    :hints(("Goal" :in-theory (enable int_constraint-satisfied)))))

(define int_constraintlist-satisfying-val ((x int_constraintlist-p))
  :guard (int_constraintlist-resolved-p x)
  :returns (val acl2::maybe-integerp :rule-classes :type-prescription)
  (if (atom x)
      nil
    (or (int_constraint-satisfying-val (car x))
        (int_constraintlist-satisfying-val (cdr x))))
  ///
  (defret <fn>-correct
    (implies val
             (int_constraintlist-satisfied val x))
    :hints(("Goal" :in-theory (enable int_constraintlist-satisfied))))

  (defret <fn>-sufficient
    (implies (int_constraintlist-satisfied someval x)
             val)
    :hints(("Goal" :in-theory (enable int_constraintlist-satisfied)))))

(define constraint_kind-satisfying-val ((x constraint_kind-p))
  :guard (constraint_kind-resolved-p x)
  :returns (val acl2::maybe-integerp :rule-classes :type-prescription)
  (constraint_kind-case x
    :unconstrained 0
    :wellconstrained (int_constraintlist-satisfying-val x.constraints)
    :otherwise nil)
  ///
  (defret <fn>-correct
    (implies val
             (constraint_kind-satisfied val x))
    :hints(("Goal" :in-theory (enable constraint_kind-satisfied))))

  (defret <fn>-sufficient
    (implies (constraint_kind-satisfied someval x)
             val)
    :hints(("Goal" :in-theory (enable constraint_kind-satisfied)))))



(defines ty-satisfying-val
  (define ty-satisfying-val ((x ty-p))
    :guard (ty-resolved-p x)
    :verify-guards nil
    :measure (ty-count x)
    :returns (val maybe-val-p)
    (b* ((x (ty->val x)))
      (type_desc-case x
        :t_int (b* ((val (constraint_kind-satisfying-val x.constraint)))
                 (and val (v_int val)))
        :t_bits (b* ((val (int-literal-expr->val x.expr)))
                  (and (<= 0 val)
                       (v_bitvector val 0)))
        :t_real (v_real 0)
        :t_string (v_string "")
        :t_bool (v_bool nil)
        :t_enum (and (consp x.elts) (v_label (car x.elts)))
        :t_tuple (b* (((mv ok vals) (tylist-satisfying-val x.types)))
                   (and ok
                        (v_array vals)))
        :t_array (b* ((val (ty-satisfying-val x.type)))
                   (array_index-case x.index
                     :arraylength_expr
                     (b* ((len (int-literal-expr->val x.index.length)))
                       (if (eql 0 len)
                           (v_array nil)
                         (and (<= 0 len)
                              val
                              (v_array (make-list len :initial-element val)))))
                     :arraylength_enum
                     (if (atom x.index.elts)
                         (v_record nil)
                       (and val
                            (v_record (pairlis$ x.index.elts
                                                (make-list (len x.index.elts) :initial-element val)))))))
        :t_record (b* (((mv ok val) (typed_identifierlist-satisfying-val x.fields)))
                    (and ok
                         (v_record val)))
        :t_exception (b* (((mv ok val) (typed_identifierlist-satisfying-val x.fields)))
                       (and ok
                            (v_record val)))
        :t_collection (b* (((mv ok val) (typed_identifierlist-satisfying-val x.fields)))
                        (and ok
                             (v_record val)))
        :t_named nil)))

  (define tylist-satisfying-val ((x tylist-p))
    :guard (tylist-resolved-p x)
    :measure (tylist-count x)
    :returns (mv ok (val vallist-p))
    (b* (((when (atom x)) (mv t nil))
         (val1 (ty-satisfying-val (car x)))
         ((unless val1)
          (mv nil nil))
         ((mv ok rest) (tylist-satisfying-val (cdr x))))
      (mv ok (and ok (cons val1 rest)))))

  (define typed_identifierlist-satisfying-val ((x typed_identifierlist-p))
    :guard (typed_identifierlist-resolved-p x)
    :measure (typed_identifierlist-count x)
    :returns (mv ok (val val-imap-p))
    (b* (((When (atom x)) (mv t nil))
         ((typed_identifier f1) (car x))
         (val1 (ty-satisfying-val f1.type))
         ((unless val1)
          (mv nil nil))
         ((mv ok rest) (typed_identifierlist-satisfying-val (cdr x))))
      (mv ok (and ok (cons (cons f1.name val1) rest)))))
  ///
  (verify-guards ty-satisfying-val)


  (defthm array-type-satisfied-of-repeat
    (iff (array-type-satisfied (acl2::repeat n val) ty)
         (or (zp n)
             (ty-satisfied val ty)))
    :hints(("Goal" :in-theory (enable acl2::repeat)
            :induct t
            :expand ((:free (x y) (array-type-satisfied (cons x y) ty))
                     (array-type-satisfied nil ty)))))

  (local (defthm alist-vals-of-pairlis$
           (implies (and (equal (len x) (len y))
                         (true-listp y))
                    (equal (acl2::alist-vals (pairlis$ x y)) y))
           :hints(("Goal" :in-theory (enable acl2::alist-vals)))))

  (local (defthm alist-keys-of-pairlis$
           (implies (and (equal (len x) (len y))
                         (true-listp x))
                    (equal (acl2::alist-keys (pairlis$ x y)) x))
           :hints(("Goal" :in-theory (enable acl2::alist-keys)))))

  (local (defthm consp-of-alist-vals
           (iff (consp (acl2::alist-vals x))
                (consp (acl2::Alist-keys x)))
           :hints(("Goal" :in-theory (enable acl2::alist-keys
                                             acl2::alist-vals)))))
  
  (std::defret-mutual <fn>-correct
    (defret <fn>-correct
      (implies val
               (ty-satisfied val x))
      :hints ('(:expand (<call>
                         (:free (v) (ty-satisfied v x))
                         (:free (ty) (array-type-satisfied nil ty)))))
      :fn ty-satisfying-val)
    (defret <fn>-correct
      (implies ok
               (tuple-type-satisfied val x))
      :hints ('(:expand (<call>)
                :in-theory (enable tuple-type-satisfied)))
      :fn tylist-satisfying-val)
    (defret <fn>-correct
      (implies ok
               (record-type-satisfied val x))
      :hints ('(:expand (<call>)
                :in-theory (enable record-type-satisfied)))
      :fn typed_identifierlist-satisfying-val))

  (defthm-ty-satisfied-flag ty-satisfying-val-sufficient
    (defthm ty-satisfying-val-sufficient
      (implies (ty-satisfied x ty)
               (ty-satisfying-val ty))
      :hints ('(:expand ((ty-satisfying-val ty)
                         (ty-satisfied x ty)
                         (:free (ty) (array-type-satisfied nil ty)))))
      :flag ty-satisfied)
    (defthm tylist-satisfying-val-sufficient
      (implies (tuple-type-satisfied x types)
               (mv-nth 0 (tylist-satisfying-val types)))
      :hints ('(:expand ((tuple-type-satisfied x types)
                         (tylist-satisfying-val types))))
      :flag tuple-type-satisfied)
    (defthm typed_identifierlist-satisfying-val-sufficient
      (implies (record-type-satisfied x fields)
               (mv-nth 0 (typed_identifierlist-satisfying-val fields)))
      :hints ('(:expand ((record-type-satisfied x fields)
                         (typed_identifierlist-satisfying-val fields))))
      :flag record-type-satisfied)
    (defthm tmp
      (implies (and (array-type-satisfied x ty)
                    (consp x))
               (ty-satisfying-val ty))
      :hints ('(:expand ((array-type-satisfied x ty))))
      :flag array-type-satisfied
      :skip t)
    :skip-others t)

  (fty::deffixequiv-mutual ty-satisfying-val))






(define int_constraint-width ((x int_constraint-p))
  :guard (int_constraint-resolved-p x)
  :returns (val natp :rule-classes :type-prescription)
  (int_constraint-case x
    :constraint_exact 1
    :constraint_range (b* ((from (int-literal-expr->val x.from))
                           (to (int-literal-expr->val x.to)))
                        (if (<= from to)
                            (+ 1 (- to from))
                          0)))
  ///
  (defret <fn>-zero
    (iff (equal val 0)
         (not (int_constraint-satisfying-val x)))
    :hints(("Goal" :in-theory (enable int_constraint-satisfying-val)))))

(define int_constraintlist-width ((x int_constraintlist-p))
  :guard (int_constraintlist-resolved-p x)
  :returns (val natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (+ (int_constraint-width (car x))
       (int_constraintlist-width (cdr x))))
  ///
  (defret <fn>-zero
    (iff (equal val 0)
         (not (int_constraintlist-satisfying-val x)))
    :hints(("Goal" :in-theory (enable int_constraintlist-satisfying-val))))

  (defret <fn>-posp
    (implies (int_constraintlist-satisfying-val x)
             (posp val))
    :rule-classes :type-prescription))

(define int_constraint-oracle-val ((rel-val natp)
                                 (x int_constraint-p))
  :guard (and (int_constraint-resolved-p x)
              (< rel-val (int_constraint-width x)))
  :returns (val integerp :rule-classes :type-prescription)
  (int_constraint-case x
    :constraint_exact (int-literal-expr->val x.val)
    :constraint_range (b* ((from (int-literal-expr->val x.from)))
                        (+ from (lnfix rel-val))))
  ///
  (defret <fn>-correct
    (implies (and (< (nfix rel-val) (int_constraint-width x)))
             (int_constraint-satisfied val x))
    :hints(("Goal" :in-theory (enable int_constraint-width
                                      int_constraint-satisfied)))))

(define int_constraintlist-oracle-val-aux ((rel-val natp)
                                           (x int_constraintlist-p))
  :guard (and (int_constraintlist-resolved-p x)
              (< rel-val (int_constraintlist-width x)))
  :guard-hints (("goal" :in-theory (enable int_constraintlist-width)))
  :returns (val integerp :rule-classes :type-prescription)
  :measure (len x)
  (if (mbt (consp x))
      (b* ((w1 (int_constraint-width (car x)))
           (rel-val (lnfix rel-val)))
        (if (< rel-val w1)
            (int_constraint-oracle-val rel-val (car x))
          (int_constraintlist-oracle-val-aux (- rel-val w1) (cdr x))))
    0)
  ///
  (defret <fn>-correct
    (implies (and (< (nfix rel-val) (int_constraintlist-width x)))
             (int_constraintlist-satisfied val x))
    :hints(("Goal" :in-theory (enable int_constraintlist-width
                                      int_constraintlist-satisfied)))))
      


(define int_constraintlist-oracle-val ((x int_constraintlist-p)
                                       orac)
  :guard (int_constraintlist-resolved-p x)
  :returns (mv (val acl2::maybe-integerp :rule-classes :type-prescription)
               new-orac)
  (b* ((width (int_constraintlist-width x))
       ((when (eql width 0)) (mv nil orac))
       ((mv rel-val orac) (acl2::orac-read width orac)))
    (mv (int_constraintlist-oracle-val-aux rel-val x) orac))
  ///
  (defret <fn>-correct
    (implies (int_constraintlist-satisfying-val x)
             (and val
                  (int_constraintlist-satisfied val x)))))


(define constraint_kind-oracle-val ((x constraint_kind-p)
                                    orac)
  :guard (constraint_kind-resolved-p x)
  :returns (mv (val acl2::maybe-integerp :rule-classes :type-prescription)
               new-orac)
  (constraint_kind-case x
    :unconstrained (acl2::orac-read-int orac)
    :wellconstrained (int_constraintlist-oracle-val x.constraints orac)
    :otherwise (mv nil orac))
  ///
  (defret <fn>-correct
    (implies (constraint_kind-satisfying-val x)
             (and val
                  (constraint_kind-satisfied val x)))
    :hints(("Goal" :in-theory (enable constraint_kind-satisfied
                                      constraint_kind-satisfying-val)))))


(defines ty-oracle-val
  :flag-local nil
  (define ty-oracle-val ((x ty-p) orac)
    :guard (ty-resolved-p x)
    :verify-guards nil
    :measure (acl2::two-nats-measure (ty-count x) 0)
    :returns (mv (val maybe-val-p) new-orac)
    (b* ((x (ty->val x)))
      (type_desc-case x
        :t_int (b* (((mv val orac) (constraint_kind-oracle-val x.constraint orac)))
                 (mv (and val (v_int val)) orac))
        :t_bits (b* ((width (int-literal-expr->val x.expr))
                     ((unless (<= 0 width)) (mv nil orac))
                     ((mv val orac) (acl2::orac-read-bits width orac)))
                  (mv (v_bitvector width val) orac))
        :t_real (b* (((mv val orac) (acl2::orac-read-rational orac)))
                  (mv (v_real val) orac))
        :t_string (b* (((mv val orac) (acl2::orac-read-string orac)))
                    (mv (v_string val) orac))
        :t_bool (b* (((mv bit orac) (acl2::orac-read-bits 1 orac)))
                  (mv (v_bool (eql bit 1)) orac))
        :t_enum (b* (((unless (consp x.elts))
                      (mv nil orac))
                     ((mv idx orac) (acl2::orac-read (len x.elts) orac)))
                  (mv (v_label (nth idx x.elts)) orac))
        :t_tuple (b* (((mv ok vals orac) (tylist-oracle-val x.types orac)))
                   (mv (and ok
                            (v_array vals))
                       orac))
        :t_array (array_index-case x.index
                   :arraylength_expr
                   (b* ((len (int-literal-expr->val x.index.length))
                        ((when (<= len 0))
                         (mv (v_array nil) orac))
                        ((mv ok vals orac) (ty-oracle-vals len x.type orac)))
                     (mv (and ok (v_array vals)) orac))
                   :arraylength_enum
                   (if (atom x.index.elts)
                       (mv (v_record nil) orac)
                     (b* (((mv ok vals orac) (ty-oracle-vals (len x.index.elts) x.type orac)))
                       (mv (and ok (v_record (pairlis$ x.index.elts vals)))
                           orac))))
        :t_record (b* (((mv ok vals orac) (typed_identifierlist-oracle-val x.fields orac)))
                    (mv (and ok
                             (v_record vals))
                        orac))
        :t_exception (b* (((mv ok vals orac) (typed_identifierlist-oracle-val x.fields orac)))
                       (mv (and ok
                                (v_record vals))
                           orac))
        :t_collection (b* (((mv ok vals orac) (typed_identifierlist-oracle-val x.fields orac)))
                        (mv (and ok
                                 (v_record vals))
                            orac))
        :t_named (mv nil orac))))
  
  (define tylist-oracle-val ((x tylist-p) orac)
    :guard (tylist-resolved-p x)
    :measure (acl2::two-nats-measure (tylist-count x) 0)
    :returns (mv ok (val vallist-p) new-orac)
    (b* (((when (atom x)) (mv t nil orac))
         ((mv val1 orac) (ty-oracle-val (car x) orac))
         ((unless val1)
          (mv nil nil orac))
         ((mv ok rest orac) (tylist-oracle-val (cdr x) orac)))
      (mv ok (and ok (cons val1 rest)) orac)))

  (define ty-oracle-vals ((n natp) (x ty-p) orac)
    :guard (ty-resolved-p x)
    :measure (acl2::two-nats-measure (ty-count x) n)
    :returns (mv ok (vals vallist-p) new-orac)
    (b* (((when (zp n)) (mv t nil orac))
         ((mv val1 orac) (ty-oracle-val x orac))
         ((unless val1)
          (mv nil nil orac))
         ((mv ok rest orac) (ty-oracle-vals (1- n) x orac)))
      (mv ok (and ok (cons val1 rest)) orac)))

  (define typed_identifierlist-oracle-val ((x typed_identifierlist-p) orac)
    :guard (typed_identifierlist-resolved-p x)
    :measure (acl2::two-nats-measure (typed_identifierlist-count x) 0)
    :returns (mv ok (val val-imap-p) new-orac)
    (b* (((When (atom x)) (mv t nil orac))
         ((typed_identifier f1) (car x))
         ((mv val1 orac) (ty-oracle-val f1.type orac))
         ((unless val1)
          (mv nil nil orac))
         ((mv ok rest orac) (typed_identifierlist-oracle-val (cdr x) orac)))
      (mv ok (and ok (cons (cons f1.name val1) rest)) orac)))
  ///
  (local (defthm len-equal-0
           (equal (equal (len x) 0)
                  (not (consp x)))))

  (local (defthm len-gt-0
           (equal (> (len x) 0)
                  (consp x))))

  (local (defthm nth-of-identifierlist
           (implies (and (identifierlist-p x)
                         (< (nfix n) (len x)))
                    (identifier-p (nth n x)))
           :hints(("Goal" :in-theory (enable nth)))))

  (std::defret-mutual len-of-ty-oracle-vals
    (defret len-of-ty-oracle-vals
      (implies ok
               (equal (len vals) (nfix n)))
      :hints ('(:expand (<call>)))
      :fn ty-oracle-vals)
    :skip-others t)
  
  (verify-guards ty-oracle-val)


  (local (defthm alist-vals-of-pairlis$
           (implies (and (equal (len x) (len y))
                         (true-listp y))
                    (equal (acl2::alist-vals (pairlis$ x y)) y))
           :hints(("Goal" :in-theory (enable acl2::alist-vals)))))

  (local (defthm alist-keys-of-pairlis$
           (implies (and (equal (len x) (len y))
                         (true-listp x))
                    (equal (acl2::alist-keys (pairlis$ x y)) x))
           :hints(("Goal" :in-theory (enable acl2::alist-keys)))))

  (local (defthm consp-of-alist-vals
           (iff (consp (acl2::alist-vals x))
                (consp (acl2::Alist-keys x)))
           :hints(("Goal" :in-theory (enable acl2::alist-keys
                                             acl2::alist-vals)))))

  (local (defthm member-of-nth
           (implies (< (nfix n) (len x))
                    (member-equal (nth n x) x))
           :hints(("Goal" :in-theory (enable nth)))))

  (local (defthm true-listp-when-vallist-p-rw
           (implies (vallist-p x)
                    (true-listp x))))
  
  (std::defret-mutual <fn>-correct
    (defret <fn>-correct
      (implies (ty-satisfying-val x)
               (and val
                    (ty-satisfied val x)))
      :hints ('(:expand (<call>
                         (ty-satisfying-val x)
                         (:free (v) (ty-satisfied v x))
                         (:free (ty) (array-type-satisfied nil ty)))))
      :fn ty-oracle-val)
    (defret <fn>-correct
      (implies (mv-nth 0 (tylist-satisfying-val x))
               (and ok
                    (tuple-type-satisfied val x)))
      :hints ('(:expand (<call>
                         (tylist-satisfying-val x))
                :in-theory (enable tuple-type-satisfied)))
      :fn tylist-oracle-val)
    (defret <fn>-correct
      (implies (ty-satisfying-val x)
               (and ok
                    (array-type-satisfied vals x)))
      :hints ('(:expand (<call>
                         (ty-satisfying-val x))
                :in-theory (enable array-type-satisfied)))
      :fn ty-oracle-vals)
    (defret <fn>-correct
      (implies (mv-nth 0 (typed_identifierlist-satisfying-val x))
               (and ok
                    (record-type-satisfied val x)))
      :hints ('(:expand (<call>
                         (typed_identifierlist-satisfying-val x))
                :in-theory (enable record-type-satisfied)))
      :fn typed_identifierlist-oracle-val))

  (fty::deffixequiv-mutual ty-oracle-val))
