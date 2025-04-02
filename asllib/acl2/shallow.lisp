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

(include-book "proof-utils")
(include-book "openers")
(include-book "centaur/meta/let-abs" :dir :System)
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))
(local (include-book "centaur/vl/util/default-hints" :dir :system))
(local (in-theory (disable loghead unsigned-byte-p)))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (acl2::disable* openers)))

(define keyword-fix ((x keywordp))
  :returns (new-x keywordp
                  :hints(("Goal" :in-theory (enable member-symbol-name))))
  (mbe :logic (intern-in-package-of-symbol
               (symbol-name (acl2::symbol-fix x))
               :keyword-pkg)
       :exec x)
  ///
  (defthm keyword-fix-when-keywordp
    (implies (keywordp x)
             (equal (keyword-fix x) x)))

  (fty::deffixtype keyword :pred keywordp :fix keyword-fix :equiv keyword-equiv :define t))

(define id-to-native ((x identifier-p))
  :returns (sym keywordp
                :hints(("Goal" :in-theory (enable member-symbol-name))))
  (intern-in-package-of-symbol
   (identifier->val x) :keyword-pkg)
  ///
  (defret symbol-name-of-id-to-native
    (equal (symbol-name sym)
           (identifier-fix x))
    :hints(("Goal" :in-theory (enable identifier-fix
                                      identifier->val)))))

(local (in-theory (disable keywordp)))

(fty::deflist keywordlist :elt-type keyword :true-listp t)

(fty::defalist keyword-alist :key-type keyword :true-listp t)

(define idlist-to-native ((x identifierlist-p))
  :returns (new-x keywordlist-p)
  (if (atom x)
      nil
    (cons (id-to-native (car x))
          (idlist-to-native (cdr x))))
  ///
  (defret len-of-<fn>
    (equal (len new-x) (len x))))




(defines val-to-native
  (define val-to-native ((x val-p))
    :measure (val-count x)
    (val-case x
      (:v_int x.val)
      (:v_real x.val)
      (:v_bool x.val)
      (:v_string x.val)
      (:v_bitvector x.val)
      (:v_label (id-to-native x.val))
      (:v_record (val-imap-to-native x.rec))
      (:v_array (vallist-to-native x.arr))))
  (define val-imap-to-native ((x val-imap-p))
    :measure (val-imap-count x)
    :returns (new-x keyword-alist-p)
    (b* ((x (val-imap-fix x))
         ((when (atom x)) nil)
         ((cons key val) (car x)))
      (cons (cons (id-to-native key) (val-to-native val))
            (val-imap-to-native (cdr x)))))
  (define vallist-to-native ((x vallist-p))
    :measure (vallist-count x)
    :Returns (new-x true-listp :rule-classes :type-prescription)
    (if (atom x)
        nil
      (cons (val-to-native (car x))
            (vallist-to-native (cdr x)))))
  ///

  (defret len-of-vallist-to-native
    (equal (len new-x) (len x))
    :hints(("Goal" :induct (len x)
            :expand ((vallist-to-native x))))
    :fn vallist-to-native)

  (std::defret-mutual keys-of-val-imap-to-native
    (defret keys-of-val-imap-to-native
      (equal (acl2::alist-keys new-x)
             (idlist-to-native (acl2::alist-keys (val-imap-fix x))))
      :hints ('(:in-theory (enable acl2::alist-keys
                                   val-imap-fix)
                :expand ((val-imap-to-native x)
                         (val-imap-fix x)
                         (:free (a b) (idlist-to-native (cons a b))))))
      :fn val-imap-to-native)
    :skip-others t)

  (std::defret-mutual vals-of-val-imap-to-native
    (defret vals-of-val-imap-to-native
      (equal (acl2::alist-vals new-x)
             (vallist-to-native (acl2::alist-vals (val-imap-fix x))))
      :hints ('(:in-theory (enable acl2::alist-vals
                                   val-imap-fix)
                :expand ((val-imap-to-native x)
                         (val-imap-fix x)
                         (:free (a b) (vallist-to-native (cons a b))))))
      :fn val-imap-to-native)
    :skip-others t)

  (fty::deffixequiv-mutual val-to-native)
  
  (local (in-theory (enable val-to-native)))

  (acl2::defopen val-to-native-when-v_int (val-to-native x) :hyp (val-case x :v_int) :hint (:expand ((val-to-native x))))
  (acl2::defopen val-to-native-when-v_real (val-to-native x) :hyp (val-case x :v_real) :hint (:expand ((val-to-native x))))
  (acl2::defopen val-to-native-when-v_bool (val-to-native x) :hyp (val-case x :v_bool) :hint (:expand ((val-to-native x))))
  (acl2::defopen val-to-native-when-v_string (val-to-native x) :hyp (val-case x :v_string) :hint (:expand ((val-to-native x))))
  (acl2::defopen val-to-native-when-v_bitvector (val-to-native x) :hyp (val-case x :v_bitvector) :hint (:expand ((val-to-native x))))
  (acl2::defopen val-to-native-when-v_label (val-to-native x) :hyp (val-case x :v_label) :hint (:expand ((val-to-native x))))
  (acl2::defopen val-to-native-when-v_record (val-to-native x) :hyp (val-case x :v_record) :hint (:expand ((val-to-native x))))
  (acl2::defopen val-to-native-when-v_array (val-to-native x) :hyp (val-case x :v_array) :hint (:expand ((val-to-native x))))
  
  (defthm val-to-native-of-v_int
    (equal (val-to-native (v_int x)) (ifix x)))

  (defthm val-to-native-of-v_real
    (equal (val-to-native (v_real x)) (rfix x)))

  (defthm val-to-native-of-v_bool
    (equal (val-to-native (v_bool x)) (acl2::bool-fix x)))

  (defthm val-to-native-of-v_string
    (equal (val-to-native (v_string x)) (acl2::str-fix x)))

  (defthm val-to-native-of-v_bitvector
    (equal (val-to-native (v_bitvector n x)) (loghead n x)))

  (defthm val-to-native-of-v_label
    (equal (val-to-native (v_label x)) (id-to-native x)))

  (defthm val-to-native-of-v_record
    (equal (val-to-native (v_record x)) (val-imap-to-native x))
    :hints (("goal" :expand ((val-to-native (v_record x))))))

  (defthm val-to-native-of-v_array
    (equal (val-to-native (v_array x)) (vallist-to-native x))
    :hints (("goal" :expand ((val-to-native (v_array x))))))

  (defthm vallist-to-native-of-cons
    (equal (vallist-to-native (cons a b))
           (cons (val-to-native a)
                 (vallist-to-native b)))
    :hints (("goal" :expand ((vallist-to-native (cons a b)))))))

(local
 (defthm vallist-p-alist-vals-of-val-imap
   (implies (val-imap-p x)
            (vallist-p (acl2::alist-vals X)))
   :hints(("Goal" :in-theory (enable acl2::alist-vals)))))


(defines typed-val-to-native
  (define typed-val-to-native ((x val-p) (ty ty-p))
    :guard (and (ty-resolved-p ty)
                (ty-satisfied x ty))
    :guard-hints (("goal" :expand ((tylist-resolved-p types)
                                   (tuple-type-satisfied x types)
                                   (array-type-satisfied x ty)
                                   (typed_identifierlist-resolved-p fields)
                                   (record-type-satisfied x fields)
                                   (ty-satisfied x ty)))
                  (and stable-under-simplificationp
                       '(:expand ((ty-resolved-p ty)))))
    :measure (acl2::two-nats-measure (ty-count ty) 0)
    :returns (val)
    (b* ((ty (ty->val ty)))
      (type_desc-case ty
        :t_int (v_int->val x)
        :t_bits (v_bitvector->val x)
        :t_real (v_real->val x)
        :t_bool (v_bool->val x)
        :t_string (v_string->val x)
        :t_enum (id-to-native (v_label->val x))
        :t_tuple (tuple-val-to-native (v_array->arr x) ty.types)
        :t_array (array_index-case ty.index
                   :arraylength_expr (typed-vallist-to-native (v_array->arr x) ty.type)
                   :arraylength_enum (pairlis$ (idlist-to-native ty.index.elts)
                                               (typed-vallist-to-native (acl2::alist-vals (v_record->rec x)) ty.type)))
        :t_record (typed-val-imap-to-native (v_record->rec x) ty.fields)
        :t_exception (typed-val-imap-to-native (v_record->rec x) ty.fields)
        :t_collection (typed-val-imap-to-native (v_record->rec x) ty.fields)
        :t_named nil)))
  (define tuple-val-to-native ((x vallist-p)
                               (types tylist-p))
    :guard (and (tylist-resolved-p types)
                (tuple-type-satisfied x types))
    :measure (acl2::two-nats-measure (tylist-count types) 0)
    :returns (val)
    (if (atom types)
        nil
      (cons (typed-val-to-native (car x) (car types))
            (tuple-val-to-native (cdr x) (cdr types)))))
  (define typed-vallist-to-native ((x vallist-p)
                                   (ty ty-p))
    :measure (acl2::two-nats-measure (ty-count ty) (len x))
    :guard (and (ty-resolved-p ty)
                (array-type-satisfied x ty))
    :returns (val)
    (if (atom x)
        nil
      (cons (typed-val-to-native (car x) ty)
            (typed-vallist-to-native (cdr x) ty))))
  (define typed-val-imap-to-native ((x val-imap-p) (fields typed_identifierlist-p))
    :measure (acl2::two-nats-measure (typed_identifierlist-count fields) 0)
    :guard (and (typed_identifierlist-resolved-p fields)
                (record-type-satisfied x fields))
    :returns (val)
    (b* (((when (atom fields)) nil)
         ((typed_identifier f1) (car fields))
         (val (cdar x)))
      (cons (cons (id-to-native f1.name) (typed-val-to-native val f1.type))
            (typed-val-imap-to-native (cdr x) (cdr fields)))))
      
  ///

  (local (defthm pairlis$-equals-val-imap-to-native
           (implies (val-imap-p x)
                    (equal (pairlis$ (idlist-to-native (acl2::alist-keys x))
                                     (vallist-to-native (acl2::alist-vals x)))
                           (val-imap-to-native x)))
           :hints(("Goal" :in-theory (enable acl2::alist-vals
                                             acl2::alist-keys
                                             val-imap-to-native
                                             idlist-to-native
                                             vallist-to-native)))))
  
  (std::defret-mutual <fn>-is-val-to-native
    (defretd <fn>-is-val-to-native
      (implies (ty-satisfied x ty)
               (equal val (val-to-native x)))
      :hints ('(:expand ((ty-satisfied x ty)
                         (val-to-native x)
                         <call>)))
      :fn typed-val-to-native)
    (defretd <fn>-is-val-to-native
      (implies (tuple-type-satisfied x types)
               (equal val (vallist-to-native x)))
      :hints ('(:expand ((tuple-type-satisfied x types)
                         (vallist-to-native x)
                         <call>)))
      :fn tuple-val-to-native)
    (defretd <fn>-is-val-to-native
      (implies (array-type-satisfied x ty)
               (equal val (vallist-to-native x)))
      :hints ('(:expand ((array-type-satisfied x ty)
                         (vallist-to-native x)
                         <call>)))
      :fn typed-vallist-to-native)
    (defretd <fn>-is-val-to-native
      (implies (and (record-type-satisfied x fields)
                    (val-imap-p x))
               (equal val (val-imap-to-native x)))
      :hints ('(:expand ((record-type-satisfied x fields)
                         (val-imap-to-native x)
                         <call>)))
      :fn typed-val-imap-to-native))

  (defopener open-typed-val-to-native typed-val-to-native
    :hyp (syntaxp (or (quotep ty)
                      (case-match ty
                        (('ty (ctor . &))
                         (member-eq ctor
                                    '(t_int t_bits t_real t_string t_bool t_enum
                                            t_tuple t_array t_record t_exception
                                            t_collection t_named)))
                        (& nil))))))

;; (define integerp* (x)
;;   (integerp x)
;;   ///
;;   (defthm integerp-when-integerp*
;;     (implies (integerp* x)
;;              (integerp x))))

(define loghead* ((n integerp) (x integerp))
  :returns (new-x integerp :rule-classes :type-prescription)
  (loghead (nfix n) x)
  ///
  (defret unsigned-byte-p-of-loghead*
    (implies (and (<= (ifix n) m)
                  (natp m))
             (unsigned-byte-p m new-x)))
  (defret loghead*-when-unsigned-byte-p
    (implies (unsigned-byte-p n x)
             (equal new-x x))))
;; (define unsigned-byte-p* (n x)
;;   (unsigned-byte-p (nfix n) x)
;;   ///
;;   (local (defthm ifix-nfix
;;            (<= (ifix x) (nfix x))
;;            :hints(("Goal" :in-theory (enable ifix nfix)))))
;;   (defthm unsigned-byte-p*-of-loghead*
;;     (unsigned-byte-p* n (loghead* n x)))

;;   (defthm loghead*-when-unsigned-byte-p*
;;     (implies (unsigned-byte-p* n x)
;;              (equal (loghead* n x) x))
;;     :hints(("Goal" :in-theory (e/d (loghead*)
;;                                    (acl2::loghead-identity))
;;             :use ((:instance acl2::loghead-identity
;;                    (size (nfix n)) (i x)))))))

(defines ty-satisfied-native
  :flag-local nil
  (define ty-satisfied-native (x (ty ty-p))
    :guard (ty-resolved-p ty)
    :measure (acl2::two-nats-measure (ty-count ty) 0)
    ;; :prepwork ((local (in-theory (enable integerp*))))
    (b* ((ty (ty->val ty)))
      (type_desc-case ty
        (:t_int (and (integerp x)
                     (constraint_kind-satisfied x ty.constraint)))
        (:t_bits ;;(and (integerp* x)
         (unsigned-byte-p (int-literal-expr->val ty.expr) x))
        (:t_real (rationalp x))
        (:t_string (stringp x))
        (:t_bool (booleanp x))
        (:t_enum (and (keywordp x)
                      (member-equal (symbol-name x) ty.elts)))
        (:t_tuple (tuple-type-satisfied-native x ty.types))
        (:t_array (array_index-case ty.index
                    :arraylength_expr
                    (and (true-listp x)
                         (eql (len x) (int-literal-expr->val ty.index.length))
                         (array-type-satisfied-native x ty.type))
                    :arraylength_enum
                    (and (keyword-alist-p x)
                         (equal (acl2::alist-keys x) (idlist-to-native (arraylength_enum->elts ty.index)))
                         (array-type-satisfied-native (acl2::alist-vals x) ty.type))))
        (:t_record (and (keyword-alist-p x)
                        (record-type-satisfied-native x ty.fields)))
        (:t_exception (and (keyword-alist-p x)
                           (record-type-satisfied-native x ty.fields)))
        (:t_collection (and (keyword-alist-p x)
                            (record-type-satisfied-native x ty.fields)))
        (otherwise nil))))

  (define tuple-type-satisfied-native (x (types tylist-p))
    :guard (tylist-resolved-p types)
    :measure (acl2::two-nats-measure (tylist-count types) 0)
    (if (atom types)
        (eq x nil)
      (and (consp x)
           (ty-satisfied-native (car x) (car types))
           (tuple-type-satisfied-native (cdr x) (Cdr types)))))

  (define array-type-satisfied-native ((x true-listp)
                                       (ty ty-p))
    :guard (ty-resolved-p ty)
    :measure (acl2::two-nats-measure (ty-count ty) (len x))
    (if (atom x)
        t
      (and (ty-satisfied-native (car x) ty)
           (array-type-satisfied-native (cdr x) ty))))

  (define record-type-satisfied-native ((x keyword-alist-p)
                                        (fields typed_identifierlist-p))
    :guard (typed_identifierlist-resolved-p fields)
    :measure (acl2::two-nats-measure (typed_identifierlist-count fields) 0)
    (b* ((x (keyword-alist-fix x)))
      (if (atom fields)
          (atom x)
        (and (consp x)
             (consp (car x))
             (b* (((cons key val) (car x))
                  ((typed_identifier f1) (car fields)))
               (and (equal key (id-to-native f1.name))
                    (ty-satisfied-native val f1.type)))
             (record-type-satisfied-native (cdr x) (cdr fields))))))
  ///
  (fty::deffixequiv-mutual ty-satisfied-native)


  (defthm-ty-satisfied-flag
    (defthm ty-satisfied-native-of-val-to-native
      (implies (and (ty-satisfied x ty)
                    (ty-resolved-p ty))
               (ty-satisfied-native (val-to-native x) ty))
      :hints ('(:expand ((val-to-native x)
                         (:free (x) (ty-satisfied x ty))
                         (:free (x) (ty-satisfied-native x ty)))))
      :flag ty-satisfied)
    (defthm tuple-type-satisfied-native-of-val-to-native
      (implies (and (tuple-type-satisfied x types)
                    (tylist-resolved-p types))
               (tuple-type-satisfied-native (vallist-to-native x) types))
      :hints ('(:expand ((vallist-to-native x)
                         (:free (x) (tuple-type-satisfied x types))
                         (:free (x) (tuple-type-satisfied-native x types)))))
      :flag tuple-type-satisfied)

    (defthm array-type-satisfied-native-of-val-to-native
      (implies (and (array-type-satisfied x ty)
                    (ty-resolved-p ty))
               (array-type-satisfied-native (vallist-to-native x) ty))
      :hints ('(:expand ((vallist-to-native x)
                         (array-type-satisfied x ty)
                         (array-type-satisfied-native nil ty)
                         (:free (a b) (array-type-satisfied-native (cons a b) ty)))))
      :flag array-type-satisfied)

    (defthm record-type-satisfied-native-of-val-to-native
      (implies (and (record-type-satisfied x fields)
                    (typed_identifierlist-resolved-p fields))
               (record-type-satisfied-native (val-imap-to-native x) fields))
      :hints ('(:expand ((val-imap-to-native x)
                         (:free (x) (record-type-satisfied x fields))
                         (:free (x) (record-type-satisfied-native x fields)))))
      :flag record-type-satisfied))


  (defthm-ty-satisfied-native-flag
    (defthm tuple-type-satisfied-native-implies-true-listp
      (implies (tuple-type-satisfied-native x types)
               (and (true-listp x)
                    (equal (len x) (len types))))
      :hints ('(:expand ((tuple-type-satisfied-native x types))))
      :rule-classes :forward-chaining
      :flag tuple-type-satisfied-native)
    :skip-others t))



(define int_constraint-value-fix ((x integerp)
                                  (c int_constraint-p))
  :guard (int_constraint-resolved-p c)
  :returns (new-x integerp :rule-classes :type-prescription)
  (int_constraint-case c
    :constraint_exact (int-literal-expr->val c.val)
    :constraint_range
    (if (<= (int-literal-expr->val c.from) (lifix x))
        (if (<= (lifix x) (int-literal-expr->val c.to))
            (lifix x)
          (int-literal-expr->val c.to))
      (int-literal-expr->val c.from)))
  ///
  (defthm int_constraint-value-fix-satisfying
    (implies (int_constraint-satisfying-val c)
             (int_constraint-satisfied (int_constraint-value-fix x c) c))
    :hints(("Goal" :in-theory (enable int_constraint-satisfied
                                      int_constraint-satisfying-val))))
  
  (defthm int_constraint-value-fix-when-satisfied
    (implies (int_constraint-satisfied x c)
             (equal (int_constraint-value-fix x c)
                    (ifix x)))
    :hints(("Goal" :in-theory (enable int_constraint-satisfied)))))

(define int_constraintlist-value-fix ((x integerp)
                                      (c int_constraintlist-p))
  :guard (int_constraintlist-resolved-p c)
  :verify-guards nil
  :guard-hints (("goal" :in-theory (enable int_constraintlist-resolved-p)))
  :returns (new-x integerp :rule-classes :type-prescription)
  ;; a little complicated and inefficient
  (if (atom c)
      0
    (if (int_constraint-satisfied x (car c))
        (lifix x)
      (let ((new-x (int_constraintlist-value-fix x (cdr c))))
        (if (int_constraintlist-satisfied new-x (cdr c))
            new-x
          (int_constraint-value-fix x (car c))))))
  ///
  (verify-guards int_constraintlist-value-fix)
  
  (defthm int_constraintlist-value-fix-satisfying
    (implies (int_constraintlist-satisfying-val c)
             (int_constraintlist-satisfied (int_constraintlist-value-fix x c) c))
    :hints(("Goal" :in-theory (enable int_constraintlist-satisfied
                                      int_constraintlist-satisfying-val))))
  
  (defthm int_constraintlist-value-fix-when-satisfied
    (implies (int_constraintlist-satisfied x c)
             (equal (int_constraintlist-value-fix x c)
                    (ifix x)))
    :hints(("Goal" :in-theory (enable int_constraintlist-satisfied)))))


(define constraint_kind-value-fix ((x integerp)
                                   (c constraint_kind-p))
  :guard (constraint_kind-resolved-p c)
  :returns (new-x integerp :rule-classes :type-prescription)
  (constraint_kind-case c
    :wellconstrained (int_constraintlist-value-fix x c.constraints)
    :otherwise (lifix x))
  ///
  
  (defthm constraint_kind-value-fix-satisfying
    (implies (constraint_kind-satisfying-val c)
             (constraint_kind-satisfied (constraint_kind-value-fix x c) c))
    :hints(("Goal" :in-theory (enable constraint_kind-satisfied
                                      constraint_kind-satisfying-val))))
  
  (defthm constraint_kind-value-fix-when-satisfied
    (implies (constraint_kind-satisfied x c)
             (equal (constraint_kind-value-fix x c)
                    (ifix x)))
    :hints(("Goal" :in-theory (enable constraint_kind-satisfied)))))



(local (defthm keyword-alist-p-of-pairlis$
         (implies (keywordlist-p x)
                  (keyword-alist-p (pairlis$ x y)))))

(local (defthm keyword-list-p-alist-keys-when-keyword-alist-p
         (implies (keyword-alist-p x)
                  (keywordlist-p (acl2::alist-keys x)))
         :hints(("Goal" :in-theory (enable acl2::alist-keys)))))

(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (atom x))))

(local (defthm alist-keys-of-pairlis$
         (equal (acl2::alist-keys (pairlis$ x y))
                (true-list-fix x))
         :hints(("Goal" :in-theory (enable acl2::alist-keys pairlis$)))))

(local (defthm alist-vals-of-pairlis$
         (implies (equal (len x) (len y))
                  (equal (acl2::alist-vals (pairlis$ x y))
                         (true-list-fix y)))
         :hints(("Goal" :in-theory (enable acl2::alist-vals pairlis$)))))                       

(local (defthm pairlis$-keys-vals-when-alistp
         (implies (alistp x)
                  (equal (pairlis$ (acl2::alist-keys x)
                                   (acl2::alist-vals x))
                         x))
         :hints(("Goal" :in-theory (enable acl2::alist-vals
                                           acl2::alist-keys)))))

(local (defthm alistp-when-keyword-alist-p-rw
         (implies (keyword-alist-p x)
                  (alistp x))))



(local (defthm len-of-alist-vals
         (equal (len (acl2::alist-vals x))
                (len (acl2::alist-keys x)))
         :hints(("Goal" :in-theory (enable acl2::alist-keys
                                           acl2::alist-vals)))))




(defines ty-fix-native
  :flag-local nil
  (define ty-fix-native (x (ty ty-p))
    :guard (ty-resolved-p ty)
    :verify-guards nil
    :measure (acl2::two-nats-measure (ty-count ty) 0)
    :returns (new-x (implies (ty-satisfying-val ty)
                             (ty-satisfied-native new-x ty))
                    :hints ('(:expand ((ty-satisfying-val ty)
                                       (:free (x) (ty-satisfied-native x ty))
                                       (:free (ty) (array-type-satisfied-native nil ty))))))
    (b* ((ty (ty->val ty)))
      (type_desc-case ty
        (:t_int (constraint_kind-value-fix (ifix x) ty.constraint))
        (:t_bits (loghead (nfix (int-literal-expr->val ty.expr)) (ifix x)))
        (:t_real (rfix x))
        (:t_string (acl2::str-fix x))
        (:t_bool (acl2::bool-fix x))
        (:t_enum (if (and (keywordp x)
                          (member-equal (symbol-name x) ty.elts))
                     x
                   (if (consp ty.elts)
                       (id-to-native (car ty.elts))
                     (id-to-native "EMPTY_ENUM"))))
        (:t_tuple (tuple-type-fix-native x ty.types))
        (:t_array (array_index-case ty.index
                    :arraylength_expr
                    (array-type-fix-native (nfix (int-literal-expr->val ty.index.length)) x ty.type)
                    :arraylength_enum
                    (pairlis$ (idlist-to-native ty.index.elts)
                              (array-type-fix-native
                               (len ty.index.elts)
                               (acl2::alist-vals x)
                               ty.type))))
        (:t_record (record-type-fix-native x ty.fields))
        (:t_exception (record-type-fix-native x ty.fields))
        (:t_collection (record-type-fix-native x ty.fields))
        (otherwise nil))))

  (define tuple-type-fix-native (x (types tylist-p))
    :guard (tylist-resolved-p types)
    :measure (acl2::two-nats-measure (tylist-count types) 0)
    :returns (new-x (implies (mv-nth 0 (tylist-satisfying-val types))
                             (tuple-type-satisfied-native new-x types))
                    :hints ('(:expand ((tylist-satisfying-val types)
                                       (:free (x) (tuple-type-satisfied-native x types))))))
    (if (atom types)
        nil
      (cons (ty-fix-native (and (consp x) (car x)) (car types))
            (tuple-type-fix-native (and (consp x) (cdr x)) (Cdr types)))))

  (define array-type-fix-native ((len natp) x (ty ty-p))
    :guard (ty-resolved-p ty)
    :measure (acl2::two-nats-measure (ty-count ty) len)
    :returns (new-x (and (true-listp new-x)
                         (equal (len new-x) (nfix len))
                         (implies (ty-satisfying-val ty)
                                  (array-type-satisfied-native new-x ty)))
                    :hints ((and stable-under-simplificationp
                                 '(:expand ((array-type-satisfied-native nil ty)
                                            (:free (a b) (array-type-satisfied-native (cons a b) ty)))))))
    (if (zp len)
        nil
      (cons (ty-fix-native (and (consp x) (car x)) ty)
            (array-type-fix-native (1- len) (and (consp x) (cdr x)) ty))))

  (define record-type-fix-native (x (fields typed_identifierlist-p))
    :guard (typed_identifierlist-resolved-p fields)
    :measure (acl2::two-nats-measure (typed_identifierlist-count fields) 0)
    :returns (new-x (and (keyword-alist-p new-x)
                         (implies (mv-nth 0 (typed_identifierlist-satisfying-val fields))
                                  (record-type-satisfied-native new-x fields)))
                    :hints ('(:expand ((typed_identifierlist-satisfying-val fields)
                                       (:free (x) (record-type-satisfied-native x fields))))))
    (b* (((when (atom fields)) nil)
         ((typed_identifier f1) (car fields))
         (val (ty-fix-native (and (consp x) (consp (car x)) (cdar x)) f1.type)))
      (cons (cons (id-to-native f1.name) val)
            (record-type-fix-native (and (consp x) (cdr x)) (cdr fields)))))
  ///
  (fty::deffixequiv-mutual ty-fix-native)

  (verify-guards ty-fix-native)

  (std::defret-mutual ty-fix-native-when-satisfied
    (defret <fn>-when-satisfied
      (implies (ty-satisfied-native x ty)
               (equal new-x x))
      :hints ('(:expand ((ty-satisfied-native x ty)
                         <call>)))
      :fn ty-fix-native)
    (defret <fn>-when-satisfied
      (implies (tuple-type-satisfied-native x types)
               (equal new-x x))
      :hints ('(:expand ((tuple-type-satisfied-native x types)
                         <call>)))
      :fn tuple-type-fix-native)
    (defret <fn>-when-satisfied
      (implies (and (array-type-satisfied-native x ty)
                    (equal (len x) (nfix len))
                    (true-listp x))
               (equal new-x x))
      :hints ('(:expand ((array-type-satisfied-native x ty)
                         <call>
                         (:free (x ty) (array-type-fix-native 0 x ty)))))
      :fn array-type-fix-native)
    (defret <fn>-when-satisfied
      (implies (and (record-type-satisfied-native x fields)
                    (keyword-alist-p x))
               (equal new-x x))
      :hints ('(:expand ((record-type-satisfied-native x fields)
                         <call>)))
      :fn record-type-fix-native))

  (defopener open-ty-fix-native ty-fix-native
    :hyp (syntaxp (or (quotep ty)
                      (case-match ty
                        (('ty (ctor . &))
                         (member-eq ctor
                                    '(t_int t_bits t_real t_string t_bool t_enum
                                            t_tuple t_array t_record t_exception
                                            t_collection t_named)))
                        (& nil))))))


(define symbol-name-list ((x symbol-listp))
  :returns (new-x string-listp)
  (if (atom x)
      nil
    (cons (symbol-name (car x))
          (symbol-name-list (cdr x)))))

(local (defthm symbol-listp-when-keyword-list-p
         (implies (keywordlist-p x)
                  (symbol-listp x))))


(local (defthm unsigned-byte-p-implies-natp-width
         (implies (unsigned-byte-p n x)
                  (natp n))
         :hints(("Goal" :in-theory (enable unsigned-byte-p)))
         :rule-classes :forward-chaining))


(defines native-to-typed-val
  (define native-to-typed-val (x (ty ty-p))
    :guard (and (ty-resolved-p ty)
                (ty-satisfied-native x ty))
    :verify-guards nil
    :returns (val val-p)
    :measure (acl2::two-nats-measure (ty-count ty) 0)
    (b* ((ty (ty->val ty)))
      (type_desc-case ty
        (:t_int (v_int x))
        (:t_bits (v_bitvector (int-literal-expr->val ty.expr) x))
        (:t_real (v_real x))
        (:t_string (v_string x))
        (:t_bool (v_bool x))
        (:t_enum (v_label (identifier (symbol-name x))))
        (:t_tuple (v_array (native-tuple-to-typed-val x ty.types)))
        (:t_array (array_index-case ty.index
                    :arraylength_expr
                    (v_array (native-array-to-typed-val x ty.type))
                    :arraylength_enum
                    (v_record (pairlis$ (arraylength_enum->elts ty.index)
                                        (native-array-to-typed-val (acl2::alist-vals x) ty.type)))))
        (:t_record     (v_record (native-record-to-typed-val x ty.fields)))
        (:t_exception  (v_record (native-record-to-typed-val x ty.fields)))
        (:t_collection (v_record (native-record-to-typed-val x ty.fields)))
        (otherwise (v_int 0)))))

  (define native-tuple-to-typed-val ((x true-listp)
                                     (types tylist-p))
    :guard (and (tylist-resolved-p types)
                (tuple-type-satisfied-native x types))
    :measure (acl2::two-nats-measure (tylist-count types) 0)
    :returns (vals vallist-p)
    (if (atom types)
        nil
      (cons (native-to-typed-val (car x) (car types))
            (native-tuple-to-typed-val (cdr x) (cdr types)))))

  (define native-array-to-typed-val ((x true-listp)
                                     (ty ty-p))
    :guard (and (ty-resolved-p ty)
                (array-type-satisfied-native x ty))
    :measure (acl2::two-nats-measure (ty-count ty) (len x))
    :returns (vals vallist-p)
    (if (atom x)
        nil
      (cons (native-to-typed-val (car x) ty)
            (native-array-to-typed-val (cdr x) ty))))

  (define native-record-to-typed-val ((x keyword-alist-p)
                                      (fields typed_identifierlist-p))
    :guard (and (typed_identifierlist-resolved-p fields)
                (record-type-satisfied-native x fields))
    :measure (acl2::two-nats-measure (typed_identifierlist-count fields) 0)
    :returns (vals val-imap-p)
    (b* ((x (keyword-alist-fix x))
         ((when (atom fields)) nil)
         ((cons & val) (car x))
         ((typed_identifier f1) (car fields)))
      (cons (cons f1.name
                  (native-to-typed-val val f1.type))
            (native-record-to-typed-val (cdr x) (cdr fields)))))
  ///

  (std::defret-mutual len-of-native-array-to-typed-val
    (defret len-of-native-array-to-typed-val
      (equal (len vals) (len x))
      :hints ('(:expand (<call>)))
      :fn native-array-to-typed-val)
    :skip-others t)
  
  (local (defthm equal-lens-when-when-equal-idlist-to-native
           (implies (equal x (idlist-to-native y))
                    (equal (equal (len y) (len x)) t))))

  
  
  (verify-guards native-to-typed-val
    :hints (("goal" :expand ((ty-satisfied-native x ty)
                             (tuple-type-satisfied-native x types)
                             (array-type-satisfied-native x ty)
                             (record-type-satisfied-native x fields)))))

  (std::defret-mutual ty-satisfied-of-native-to-typed-val
    (defret ty-satisfied-of-native-to-typed-val
      (implies (and (ty-satisfied-native x ty)
                    (ty-resolved-p ty))
               (ty-satisfied val ty))
      :hints ('(:expand (<call>
                         (:free (x) (ty-satisfied x ty))
                         (:free (x) (ty-satisfied-native x ty)))
                :in-theory (enable identifier identifier-fix)))
      :fn native-to-typed-val)
    (defret tuple-type-satisfied-of-<fn>
      (implies (and (tuple-type-satisfied-native x types)
                    (tylist-resolved-p types))
               (tuple-type-satisfied vals types))
      :hints ('(:expand (<call>
                         (:free (x) (tuple-type-satisfied x types))
                         (:free (x) (tuple-type-satisfied-native x types)))))
      :fn native-tuple-to-typed-val)

    (defret array-type-satisfied-of-<fn>
      (implies (and (array-type-satisfied-native x ty)
                    (ty-resolved-p ty))
               (array-type-satisfied vals ty))
      :hints ('(:expand (<call>
                         (array-type-satisfied-native x ty)
                         (array-type-satisfied nil ty)
                         (:free (a b) (array-type-satisfied (cons a b) ty)))))
      :fn native-array-to-typed-val)

    (defret record-type-satisfied-of-<fn>
      (implies (and (record-type-satisfied-native x fields)
                    (typed_identifierlist-resolved-p fields))
               (record-type-satisfied vals fields))
      :hints ('(:expand (<call>
                         (:free (x) (record-type-satisfied x fields))
                         (:free (x) (record-type-satisfied-native x fields)))))
      :fn native-record-to-typed-val)))

(defopener open-native-to-typed-val native-to-typed-val
  :hyp (syntaxp (or (quotep ty)
                    (case-match ty
                      (('ty (ctor . &))
                       (member-eq ctor
                                  '(t_int t_bits t_real t_string t_bool t_enum
                                          t_tuple t_array t_record t_exception
                                          t_collection t_named)))
                      (& nil)))))

(defopener open-ty-satisfied-native ty-satisfied-native
  :hyp (syntaxp (or (quotep ty)
                    (case-match ty
                      (('ty (ctor . &))
                       (member-eq ctor
                                  '(t_int t_bits t_real t_string t_bool t_enum
                                          t_tuple t_array t_record t_exception
                                          t_collection t_named)))
                      (& nil)))))



(deftagsum shallow_result
  (:sh_normal (res))
  (:sh_throwing ((throwdata maybe-throwdata)))
  (:sh_error ((desc stringp)
              (data)))
  :short-names t)

(program)

(define simplify-for-shallow (term hyp equiv state &key expand)
  ;; NOTE: always simplifies under EQUAL
  (acl2::easy-simplify-term-fn term hyp
                               `(:expand (:lambdas . ,expand)
                                 :in-theory (acl2::e/d* (asl-code-proof-enables)
                                                        (asl-code-proof-disables))) ;; hints
                               equiv   ;; equiv
                               t      ;; normalize
                               t      ;; rewrite
                               1000   ;; repeat
                               1000   ;; backchain-limit
                               t      ;; untrans-result
                               state))

;; =================================================================================
;; RESOLVING PARAMETER/ARGUMENT/RETURN TYPES.
;; =================================================================================
;; A function signature can have argument and return types that depend on
;; integer parameter values.
;; We need to derive various bits of info about these types:
;;  - guards for the shallow function
;;  - return type of the shallow function
;;  - input fixers for the shallow function
;;  - how to form interpreter parameters/args from the shallow function's parameters/args
;;    (we rewrite this form in order to produce the shallow function's body)
;;  - how to extract the shallow function's return value from the interpreter's return values
;;    (same reason)
;;  - how to extract the shallow function's parameters/args from the interpreter parameters/args
;;    (we want to prove a rule that expresses an interpreter call of the function in terms of the
;;    shallow function)
;;  - how to express the interpreter's return value in terms of the shallow function's return value
;;    (same reason)
;; An example:
;;   func foo {M, N} (x : bits(N)) => (bits(M-1), integer{M..2^N-1})

;; A subtlety of ASL typechecking is that the typechecker ensures (I think)
;; that if the function is called, it is called with correctly typed inputs,
;; but it does not ensure that the output types are necessarily well formed.
;; In fact, if we've defined a function with the signature above then we can
;; call it with foo{0,2}(Zeros{2}) or foo{5,2}(Zeros{2}) and this will
;; typecheck -- but since the return types are empty, somewhere along the way
;; we'll get an error.

;; I think we don't want to assume that such an error can't happen -- e.g., we
;; don't want to require guards m >= 1 or m <= 2^n-1 on the shallowing of the
;; above function. But we do need the guard n >= 0 because otherwise the input
;; can't exist.  We also do need those assumptions on the return types -- we
;; can't say our first return value is an unsigned-byte M-1 if M-1 is less than
;; 0.
;; =================================================================================


;; ---------------------------------------------------------------------------------
;; Resolving types:
;; A type may have variables in it, e.g., bits(N), represented as (t_bits (e_var "N"))
;; We want to resolve this to an ACL2 term representing an ASL type in which
;; all expressions are integer literals, such as (t_bits (e_literal (l_int n))),
;; where n is the variable that we're going to use for the parameter n.
;; Resolve-ty should have sufficient openers installed & enabled; the type here is a quoted value,
;; so only quotep openers are needd.

;; The local-storage argument should be a term nesting PUT-ASSOC-EQUAL
;; applications binding all of the ASL variables (such as "N" above) appearing
;; in the types. For the types inside a function signature that has passed
;; typechecking, bindings for the function's parameters should be sufficient,
;; and it should be possible to add these in order as the parameter types are
;; resolved.

;; (Obsolete:)
;; We compute two terms: the conditions under which the type successfully resolves (ty-resolves-term),
;; and the resolved term when we assume that it did resolve (resolved-ty-term).
;; The former should generally be true unless some variable referenced in the
;; type is missing from local-storage or is not known to be a v_int.
(define shallow-resolve-type ((type ty-p)
                              hyp
                              env-term
                              state)
  (b* (((er ty-resolves-term)
        (simplify-for-shallow `(mv-let (res orac) (resolve-ty ,env-term ',type :clk 1000)
                                 (declare (ignore orac))
                                 (eval_result-case res :ev_normal))
                              hyp 'iff state))
       (hyp (list 'and ty-resolves-term hyp))
       ((er resolved-ty-term)
        (simplify-for-shallow `(mv-let (res orac) (resolve-ty ,env-term ',type :clk 1000)
                                 (declare (ignore orac))
                                 (ev_normal->res res))
                              hyp 'equal state))
       ((when (or (equal resolved-ty-term ''nil)
                  (and (consp resolved-ty-term)
                       (eq (car resolved-ty-term) 'EV_NORMAL->RES$INLINE))
                  (not (or (quotep resolved-ty-term)
                           (case-match resolved-ty-term
                             (('ty (ctor . &))
                              (member-eq ctor
                                         '(t_int t_bits t_real t_string t_bool t_enum
                                                 t_tuple t_array t_record t_exception
                                                 t_collection t_named))))))))
        (er soft 'shallow-arg-req "Seems like type didn't resolve: ~x0 -- result ~x1" type resolved-ty-term)))
    (value resolved-ty-term)))

(define shallow-resolve-type-list ((types tylist-p)
                                   hyp
                                   env-term
                                   state)
  (b* (((when (atom types)) (value nil))
       ((er type1) (shallow-resolve-type (car types) hyp env-term state))
       ((er rest) (shallow-resolve-type-list (cdr types) hyp env-term state)))
    (value (cons type1 rest))))


(define shallow-type->native-satisfies-expr (type-expr ;; expr for resolved type
                                             x-expr    ;; value expression
                                             hyp state)
  ;; E.g., if type-expr is (t_bits n) and x-expr is v, result will be (unsigned-byte-p n v).
  (simplify-for-shallow `(ty-satisfied-native ,x-expr ,type-expr) hyp 'iff state))

(defines shallow-returntype-rewrites
  ;; returns list of expressions, implicitly conjoined
  (define shallow-returntype-rewrites (expr)
    (case-match expr
      (('and . exprs) (shallow-returntype-rewrites-lst exprs))
      (('unsigned-byte-p idx val)
       `((integerp ,val)
         ,(if (symbolp idx)
              `(unsigned-byte-p ,idx ,val)
            `(implies (equal __width ,idx)
                      (unsigned-byte-p __width ,val)))))
      (& (list expr))))
  (define shallow-returntype-rewrites-lst (exprs)
    (if (atom exprs)
        nil
      (append (shallow-returntype-rewrites (car exprs))
              (shallow-returntype-rewrites-lst (cdr exprs))))))

(defines shallow-returntype-forwards
  ;; returns list of expressions, implicitly conjoined
  ;; NOTE: Below, where this is used, we assume that the return value isn't mentioned, only the formals --
  ;; so we don't bind returnval to the result.
  (define shallow-returntype-forwards (expr)
    (case-match expr
      (('and . exprs) (shallow-returntype-forwards-lst exprs))
      (('unsigned-byte-p ('ifix idx) &)
       `((not (negp ,idx))))
      (& nil)))
  (define shallow-returntype-forwards-lst (exprs)
    (if (atom exprs)
        nil
      (append (shallow-returntype-forwards (car exprs))
              (shallow-returntype-forwards-lst (cdr exprs))))))

(defines shallow-returntype-type-prescriptions
  ;; returns list of expressions, implicitly conjoined
  (define shallow-returntype-type-prescriptions (expr)
    (case-match expr
      (('and . exprs) (shallow-returntype-type-prescriptions-lst exprs))
      (('unsigned-byte-p & val)
       `((natp ,val)))
      (('rationalp &) (list expr))
      (('integerp &) (list expr))
      (('stringp &) (list expr))
      (('keywordp val) `((symbolp ,val)))
      (('consp &) (list expr))
      (& nil)))
  (define shallow-returntype-type-prescriptions-lst (exprs)
    (if (atom exprs)
        nil
      (append (shallow-returntype-type-prescriptions (car exprs))
              (shallow-returntype-type-prescriptions-lst (cdr exprs))))))

            
  

(define shallow-type->asl-satisfies-expr (type-expr ;; expr for resolved type
                                          x-expr    ;; value expression
                                          hyp state)
  ;; E.g., if type-expr is (t_bits n) and x-expr is v, result will be (unsigned-byte-p n v).
  (simplify-for-shallow `(ty-satisfied ,x-expr ,type-expr) hyp 'iff state))

(define shallow-type->native-fix-expr (type-expr ;; expr for resolved type
                                       x-expr    ;; value expression
                                       hyp state)
  ;; E.g., if type-expr is (t_bits n) and x-expr is v, result will be (loghead n v).
  (simplify-for-shallow `(ty-fix-native ,x-expr ,type-expr) hyp 'equal state))

(define shallow-type->native-wrap-expr (type-expr ;; expr for resolved type
                                       x-expr    ;; value expression
                                       hyp state)
  ;; E.g., if type-expr is (t_bits n) and x-expr is v, result will be (v_bitvector n v).
  (simplify-for-shallow `(native-to-typed-val ,x-expr ,type-expr) hyp 'equal state))

(define shallow-type->native-wrap-exprlist (type-exprs ;; expr for resolved types
                                            x-exprs    ;; value expressions
                                            hyp state)
  (b* (((when (atom type-exprs)) (value nil))
       ((er first) (shallow-type->native-wrap-expr (car type-exprs) (car x-exprs) hyp state))
       ((er rest) (shallow-type->native-wrap-exprlist (cdr type-exprs) (cdr x-exprs) hyp state)))
    (Value (cons first rest))))

(define shallow-type->native-extract-expr (type-expr ;; expr for resolved type
                                           x-expr    ;; value expression
                                           hyp state)
  ;; E.g., if type-expr is (t_bits n) and x-expr is v, result will be (v_bitvector->val v).
  (simplify-for-shallow `(typed-val-to-native ,x-expr ,type-expr)
                        hyp 'equal state))



;; ---------------------------------------------------------------------------------
;; Fills in a local-storage-term with parameter bindings, for use with shallow-resolve-type.
(define shallow-local-storage-param-bindings ((params symbol-listp)
                                              (fn-params maybe-typed_identifierlist-p)
                                              local-storage-term)
  ;; Forms a term representing a val-imap in which each ASL parameter name is bound to (v_int v)
  ;; where v is the corresponding ACL2 variable.
  (b* (((when (atom params)) local-storage-term)
       ((maybe-typed_identifier p1) (car fn-params))
       (new-term `(put-assoc-equal ,p1.name (v_int ,(car params)) ,local-storage-term)))
    (shallow-local-storage-param-bindings (cdr params) (cdr fn-params) new-term)))


(define shallow-param-env ((params symbol-listp) (fn-params maybe-typed_identifierlist-p))
  (let ((storage-term (shallow-local-storage-param-bindings params fn-params 'env.local.storage)))
    `(change-env env :local (change-local-env (empty-local-env) :storage ,storage-term))))

(define shallow-param-integerp-hyps ((params symbol-listp))
  ;; Assumes each parameter variable to be integerp.
  (if (atom params)
      nil
    (cons `(integerp ,(car params))
          (shallow-param-integerp-hyps (cdr params)))))


;; ---------------------------------------------------------------------------------
;; Fills in a local-storage-term with parameter bindings, but leaves out the v_int constructors --
;; i.e. we're assuming the param variables are all bound to ASL values (v_int-p).
(define shallow-local-storage-asl-param-bindings ((params symbol-listp)
                                                  (fn-params maybe-typed_identifierlist-p)
                                                  local-storage-term)
  ;; Forms a term representing a val-imap in which each ASL parameter name is bound to (v_int v)
  ;; where v is the corresponding ACL2 variable.
  (b* (((when (atom params)) local-storage-term)
       ((maybe-typed_identifier p1) (car fn-params))
       (new-term `(put-assoc-equal ,p1.name ,(car params) ,local-storage-term)))
    (shallow-local-storage-asl-param-bindings (cdr params) (cdr fn-params) new-term)))


(define shallow-asl-param-env ((params symbol-listp) (fn-params maybe-typed_identifierlist-p))
  (let ((storage-term (shallow-local-storage-asl-param-bindings params fn-params 'env.local.storage)))
    `(change-env env :local (change-local-env (empty-local-env) :storage ,storage-term))))

(define shallow-asl-param-v_int-hyps ((params symbol-listp))
  ;; Assumes each parameter variable to be integerp.
  (if (atom params)
      nil
    (cons `(val-p ,(car params))
          (cons `(val-case ,(car params) :v_int)
                (shallow-asl-param-v_int-hyps (cdr params))))))
       


;; ---------------------------------------------------------------------------------
;; Computes the resolved types of the function's parameters.
;; Hyp here just needs to assume all parameters are integerp.
;; Just returns the ordered list of resolved types.
(define shallow-resolve-param-types ((fn-params maybe-typed_identifierlist-p)
                                     param-env-term
                                     hyp
                                     state)
  (b* (((when (atom fn-params)) (value nil))
       ((maybe-typed_identifier p1) (car fn-params))
       (type (or p1.type (ty (t_int (unconstrained)))))
       ((er type-term) (shallow-resolve-type type hyp param-env-term state))
       ((er rest) (shallow-resolve-param-types (cdr fn-params) param-env-term hyp state)))
    (value (cons type-term rest))))

;; ---------------------------------------------------------------------------------
;; Computes the resolved types of the function's arguments.
;; Hyp here just needs to assume all parameters are integerp.
;; Just returns the ordered list of resolved types.
(define shallow-resolve-arg-types ((fn-args typed_identifierlist-p)
                                   param-env-term
                                   hyp
                                   state)
  (b* (((when (atom fn-args)) (value nil))
       ((typed_identifier p1) (car fn-args))
       ((er type-term) (shallow-resolve-type p1.type hyp param-env-term state))
       ((er rest) (shallow-resolve-arg-types (cdr fn-args) param-env-term hyp state)))
    (value (cons type-term rest))))
   
    
;; ---------------------------------------------------------------------------------
;; Shallow function's DEFINE formals:
;; Given resolved types for the parameters and args, pair (varname type-satisfied-term).
;; The full set of guard assumptions can be derived from this using strip-cadrs.
(define shallow-define-formals ((args symbol-listp)
                                resolved-types ;; term list, one per arg
                                hyp ;; params integer-listp
                                state)
  (b* (((when (atom args)) (value nil))
       ((er satisfies-term)
        (shallow-type->native-satisfies-expr (car resolved-types) (car args)
                                             hyp state))
       ((er rest) (shallow-define-formals (cdr args) (cdr resolved-types) hyp state)))
    (value (cons `(,(car args) ,satisfies-term) rest))))


;; ---------------------------------------------------------------------------------
;; LET* bindings for use at the start of the shallow function to fix the
;; arguments to the required types.
(define shallow-formal-fixer-alist ((args symbol-listp)
                                    resolved-types ;; term list, one per arg
                                    hyp            ;; params integer-listp
                                    state)
  (b* (((when (atom args)) (value nil))
       ((er fix-expr)
        (shallow-type->native-fix-expr (car resolved-types) (car args) hyp state))
       ((er rest) (shallow-formal-fixer-alist (cdr args) (cdr resolved-types) hyp state)))
    (value (cons (cons (car args) fix-expr) rest))))

(define shallow-formal-fixer-bindings (alist)
  (if (atom alist)
      nil
    (b* (((cons var fix-expr) (car alist)))
      (cons `(,var (mbe :logic ,fix-expr :exec ,var))
            (shallow-formal-fixer-bindings (cdr alist))))))

;; ---------------------------------------------------------------------------------
;; For determining the function body, we rewrite a call of eval_subprogram
;; where we've constructed the arg and parameter lists from the shallow function's formals.
;; This constructs either the parameters or the args.
(define shallow-native-to-asl-args ((args symbol-listp)
                                    resolved-types ;; term list, one per arg
                                    hyp ;; params integer-listp ?
                                    state)
  (b* (((when (atom args)) (value nil))
       ((er arg-term) (shallow-type->native-wrap-expr (car resolved-types) (car args) hyp state))
       ((er rest) (shallow-native-to-asl-args (cdr args) (cdr resolved-types) hyp state)))
    (value (cons arg-term rest))))


;; ---------------------------------------------------------------------------------
;; The correctness proof of the shallow embedding shows that an arbitrary call
;; of eval_subprogram of the function with correct arity can be expressed in terms of the shallow function.
;; The shallow function needs to be called with args derived from the ASL value args given to eval_subprogram.
;; E.g., for foo {n} (v : bits(N)), we need (v_int->val n) (v_bits->val v).
;; 
(define shallow-asl-to-native-args ((args symbol-listp)
                                    asl-resolved-types
                                    hyp ;; params v_int
                                    state)
  (b* (((when (atom args)) (value nil))
       ((er first) (shallow-type->native-extract-expr (car asl-resolved-types) (car args) hyp state))
       ((er rest) (shallow-asl-to-native-args (cdr args) (cdr asl-resolved-types) hyp state)))
    (value (cons first rest))))

;; ---------------------------------------------------------------------------------
;; We install fixers at the beginning of the body so that the hypotheses for the return type theorems will be minimal.
;; But these fixers can't help when the input type isn't satisfiable, i.e., (t_bits n) when n < 0.
;; So we need to more broadly assume that the input types are all satisfiable even when we don't want to assume that the
;; inputs satisfy their types. Returns a list of assumptions.
(define shallow-types-satisfiable (resolved-types
                                   hyp ;; params integer-listp
                                   state)
  (b* (((when (atom resolved-types)) (value nil))
       ((er first) (simplify-for-shallow `(ty-satisfying-val ,(car resolved-types)) hyp 'iff state))
       ((when (eq first nil))
        (er soft 'shallow-types-satisfiable "Type cannot be satisfied: ~x0" (car resolved-types)))
       ((er rest) (shallow-types-satisfiable (cdr resolved-types) hyp state)))
    (value (if (eq first t)
               rest
             (cons first rest)))))
      


       

;; (define shallow-return-exprs-aux (returnvars returntypes hyps state)
;;   (b* (((When (atom returnvars)) (value nil))
;;        ((er (cons type type-resolves)) (shallow-resolve-type (car returntypes) hyps local-storage state))
;;        (term `(native-to-typed-val ,(car returnvars) ,type))
;;        (hyps (cons type-resolves hyps))
;;        ((er rw-term) (simplify-for-shallow term `(and . ,hyps) 'equal state))
;;        ((er rest) (shallow-return-exprs-aux (cdr returnvars) (cdr returntypes) hyps local-storage state)))
;;     (value (cons rw-term rest))))
    

;; (define shallow-return-exprs (returnvars returntype hyps local-storage state)
;;   (b* (((unless returntype)
;;         (value nil))
;;        (ty (ty->val returntype)))
;;     (type_desc-case ty
;;       :t_tuple (b* (((unless (eql (len returnvars) (len ty.types)))
;;                      (er soft 'shallow-return-exprs "Returns length mismatch")))
;;                  (shallow-return-exprs-aux returnvars ty.types hyps local-storage state))
;;       :otherwise (b* (((unless (symbolp returnvars))
;;                        (er soft 'shallow-return-exprs "Returns length mismatch")))
;;                    (shallow-return-exprs-aux
;;                     (list returnvars) (list returntype) hyps local-storage state)))))

    



;; (define shallow-return-type (returntype hyps local-storage state)
;;   (b* (((unless returntype)
;;         (value nil))
;;        ((er type) (shallow-resolve-type returntype hyps local-storage state))
;;        (term `(ty-satisfied-native returnval ,type))
;;        ((er rw-term) (simplify-for-shallow term `(and . ,hyps) 'iff state)))
;;     (value rw-term)))





;; (define remove-duplicated-keys-aux (x keys)
;;   (if (atom x)
;;       nil
;;     (if (and (consp (car x))
;;              (not (member-equal (caar x) keys)))
;;         (cons (car x)
;;               (remove-duplicated-keys-aux (cdr x) (cons (caar x) keys)))
;;       (remove-duplicated-keys-aux (cdr x) keys))))

;; (define remove-duplicated-keys (x)
;;   (remove-duplicated-keys-aux x nil))
                                     
             
(define remove-corresponding-elements (keys vals rem)
  (if (atom keys)
      nil
    (if (member-equal (car keys) rem)
        (remove-corresponding-elements (cdr keys) (cdr vals) rem)
      (cons (car vals)
            (remove-corresponding-elements (cdr keys) (cdr vals) rem)))))
                    



(define shallow-let-abstract (x state)
  (b* (((er x-trans) (acl2::translate x t nil t 'shallow-let-abstract (w state) state))
       (letabs (cmr::let-abstract-term-preserving-ifs x-trans 'tmp-)))
    (value (untranslate letabs nil (w state)))))


(define shallow-translate-alist (x state)
  (b* (((when (atom x)) (value nil))
       ((cons var term) (car x))
       ((er trans-term) (acl2::translate term t nil t 'shallow-translate-alist (w state) state))
       ((er rest) (shallow-translate-alist (cdr x) state)))
    (value (cons (cons var trans-term) rest))))

(define shallow-substitute (x al state)
  (b* (((er x-trans) (acl2::translate x t nil t 'shallow-let-abstract (w state) state))
       ((er al-trans) (shallow-translate-alist al state))
       (subst (cmr::term-subst x-trans al-trans)))
    (value (untranslate subst nil (w state)))))

(define shallow-translate-list (x state)
  (b* (((when (atom x)) (value nil))
       ((er first) (acl2::translate (car x) t nil t 'shallow-let-abstract (w state) state))
       ((er rest) (shallow-translate-list (cdr x) state)))
    (value (cons first rest))))


(define shallow-substitute-list (x al state)
  (b* (((er x-trans) (shallow-translate-list x state))
       ((er al-trans) (shallow-translate-alist al state))
       (subst (cmr::termlist-subst x-trans al-trans)))
    (value (acl2::untranslate-lst subst nil (w state)))))


(define def-asl-shallow-fn (name args state)
  (b* (((std::extract-keyword-args
         :other-args bad-args
         :allowed-keys '(:prepwork)
         ;; :kwd-alist kwd-alist
         function
         params
         args
         returns ;; name or list of names, not specs like in def-asl-subprogram
         ;; measure
         safe-clock
         
         ;; enable
         ;; disable
         ;; hints
         ;; prepwork

         (static-env '(stdlib-static-env)))
        args)
       
       ((when bad-args)
        (er soft 'def-asl-subprogram "Bad arguments: ~x0" bad-args))
       ((unless (stringp function))
        (er soft 'def-asl-subprogram "Function should be a string: ~x0" function))
       ((acl2::er (cons & static-env-val))
        (acl2::simple-translate-and-eval static-env nil nil
                                         (msg "static env ~x0" static-env)
                                         'def-asl-subprogram (w state) state t))
       ((unless (static_env_global-p static-env-val))
        (er soft 'def-asl-subprogram "Bad static env (evaluation of ~x0): doesn't satisfy static_env_global-p" static-env))
       (fn-struct (cdr (hons-assoc-equal function
                                         (static_env_global->subprograms static-env-val))))
       ((unless fn-struct)
        (er soft 'def-asl-subprogram "Bad function ~x0: not found in static env" function))
       ((func-ses fn-struct))
       ((func f) fn-struct.fn)

       ((unless (symbol-listp params))
        (er soft 'def-asl-subprogram "Params should be a symbol-list"))
       ((unless (eql (len params) (len f.parameters)))
        (er soft 'def-asl-subprogram "~x0 params were given but ~s1 has ~x2 parameters" (len params) function (len f.parameters)))
       ((unless (symbol-listp args))
        (er soft 'def-asl-subprogram "Args should be a symbol-list"))
       ((unless (eql (len args) (len f.args)))
        (er soft 'def-asl-subprogram "~x0 args were given but ~s1 has ~x2 args" (len args) function (len f.args)))

       (returntype-is-tuple
        (type_desc-case (ty->val f.return_type) :t_tuple))

       ;; Returntype can be a tuple, in which case returns is a list of the
       ;; same length.  If not, we accept either a symbol or list containing
       ;; one symbol, but normalize to just a symbol.
       ((unless
            (b* ((returntype (ty->val f.return_type)))
              (type_desc-case returntype
                :t_tuple (and (symbol-listp returns)
                              (equal (len returns) (len returntype.types)))
                :otherwise (or (symbolp returns)
                               (symbol-listp returns)
                               (eql (len returns) 1)))))
        (er soft 'def-asl-subprogram "Bad number of return values"))
       (returns (if (and (not returntype-is-tuple)
                         (not (symbolp returns)))
                    (car returns)
                  returns))

       
       (direct-subprograms (collect-direct-subprograms f.body nil))
       (table  (table-alist 'asl-subprogram-table (w state)))
       (subprograms (cons function (collect-transitive-subprograms direct-subprograms table nil)))
       (clk-val
        (or safe-clock
            (+ 1 (maximize-const-clocks direct-subprograms table -1))))


       ;; (orig-args args)

       (param-env-term (shallow-param-env params f.parameters))
       (params-integerp-hyps (shallow-param-integerp-hyps params))
       (params-integerp-hyp `(and . ,params-integerp-hyps))
       ((er param-types)
        (shallow-resolve-param-types f.parameters param-env-term params-integerp-hyp state))
       ((er arg-types)
        (shallow-resolve-arg-types f.args param-env-term params-integerp-hyp state))

       ((er types-sat) (shallow-types-satisfiable (append param-types arg-types)
                                                  params-integerp-hyp state))
       
       (nondup-args (set-difference-eq args params))
       (nondup-arg-types (remove-corresponding-elements args arg-types params))

       
       ((er param-formals)
        (shallow-define-formals params param-types t state))
       ((er arg-formals)
        (shallow-define-formals nondup-args nondup-arg-types params-integerp-hyp state))
       (formals (append param-formals arg-formals))
       (guard-hyps (acl2::strip-cadrs formals))
       

       ((er param-fixer-al)
        (shallow-formal-fixer-alist params param-types t state))
       ((er arg-fixer-al)
        (shallow-formal-fixer-alist nondup-args nondup-arg-types params-integerp-hyp state))
       (fixer-al (append param-fixer-al arg-fixer-al))
       (fixers (shallow-formal-fixer-bindings fixer-al))

       ((er asl-params)
        (shallow-native-to-asl-args params param-types params-integerp-hyp state))
       ((er asl-args)
        (shallow-native-to-asl-args args arg-types params-integerp-hyp state))
       
       (match-hyp `(subprograms-match ',subprograms
                                      (global-env->static (env->global env))
                                      ,static-env))
       (measure-reqs (if (eql clk-val 0)
                         t
                       `(<= ,clk-val (ifix clk))))

       
       (body-hyp (list* 'and match-hyp measure-reqs (append params-integerp-hyps guard-hyps)))
       (body-term `(mv-nth 0 (eval_subprogram env ,function (list . ,asl-params) (list . ,asl-args))))
       ((er body-simp) (simplify-for-shallow body-term body-hyp 'equal state
                                             :expand `((:free (params args)
                                                        (eval_subprogram env ,function params args)))))
       (normalp-term `(equal (eval_result-kind ,body-simp) :ev_normal))
       ((er normalp-simp) (simplify-for-shallow normalp-term body-hyp 'iff state))
       (always-normal (eq normalp-simp t))

       ((er return-type)
        (shallow-resolve-type f.return_type t param-env-term state))
       ((er return-type/s)
        (b* ((returntype (ty->val f.return_type)))
          (type_desc-case returntype
            :t_tuple (shallow-resolve-type-list returntype.types t param-env-term state)
            :otherwise (value return-type))))

       ;; ((er errorp-simp) (if always-normal
       ;;                       (value nil)
       ;;                     (simplify-for-shallow `(equal (eval_result-kind ,body-simp) :ev_error)
       ;;                                           `(and . ,hyps) 'iff state)))
       ;; ((er throwingp-simp) (if always-normal
       ;;                          (value nil)
       ;;                        (simplify-for-shallow `(equal (eval_result-kind ,body-simp) :ev_throwing)
       ;;                                              `(and . ,hyps) 'iff state)))
       
       (return-expr
        (if returntype-is-tuple
            `(tuple-vallist-to-native (func_result->vals res.res) ,return-type/s)
          `(typed-val-to-native (car (func_result->vals res.res)) ,return-type/s)))
       
       ((er body) (simplify-for-shallow
                   (if always-normal
                       `(let ((res.res (ev_normal->res ,body-simp)))
                          ,return-expr)
                     `(let ((res ,body-simp))
                        (eval_result-case res
                          :ev_normal (sh_normal ,return-expr)
                          :ev_error (sh_error res.desc res.data)
                          :ev_throwing (sh_throwing res.throwdata))))
                   body-hyp 'equal state))
       ((er body) (shallow-let-abstract body state))

       ((er return-type-term) (shallow-type->native-satisfies-expr
                               return-type 'returnval t state))
       ;; (return-concl (if always-normal
       ;;                   return-type-term
       ;;                 (and (shallow_result-p returnval)
       ;;                      (implies (shallow_result-case returnval :sh_normal)
       ;;                               (let ((returnval (sh_normal->res returnval)))
       ;;                                 ,return-type-term)))))
       ((er return-hyp) (shallow-substitute `(and . ,types-sat) fixer-al state))
       (return-sig-thmname (intern-in-package-of-symbol
                            (concatenate 'string (symbol-name name) "-RETURN-SIGNATURE")
                            'asl-pkg))
       (return-rewrites
        (if always-normal
            `(and . ,(shallow-returntype-rewrites return-type-term))
          `(and (shallow_result-p returnval)
                (implies (shallow_result-case returnval :sh_normal)
                         (let ((returnval (sh_normal->res returnval)))
                           (and . ,(shallow-returntype-rewrites return-type-term)))))))
       (return-rewrite-thmname (intern-in-package-of-symbol
                            (concatenate 'string (symbol-name name) "-RETURN-REWRITE")
                            'asl-pkg))
       (return-type-prescrips (shallow-returntype-type-prescriptions return-type-term))
       (return-type-prescrip
        (and return-type-prescrips
             (if always-normal
                 `(and . ,return-type-prescrips)
               `(implies (shallow_result-case returnval :sh_normal)
                         (let ((returnval (sh_normal->res returnval)))
                           (and . ,return-type-prescrips))))))
       (return-type-prescrip-thmname (intern-in-package-of-symbol
                            (concatenate 'string (symbol-name name) "-RETURN-TYPE-PRESCRIP")
                            'asl-pkg))

       (return-forwards (shallow-returntype-forwards return-type-term))
       (return-forward
        (and return-forwards
             (not always-normal)
             `(implies (shallow_result-case returnval :sh_normal)
                       (and . ,return-forwards))))
       (return-forward-thmname (intern-in-package-of-symbol
                                (concatenate 'string (symbol-name name) "-RETURN-FORWARD")
                                'asl-pkg))

       (return-concl `(and ,@(and return-type-prescrips `(,return-type-prescrip))
                           ,@(and return-forward `(,return-forward))
                           (implies ,return-hyp
                                    ,return-rewrites)))
                               

       (asl-param-env-term (shallow-asl-param-env params f.parameters))
       (asl-params-v_int-hyps (shallow-asl-param-v_int-hyps params))
       (asl-params-v_int-hyp `(and . ,asl-params-v_int-hyps))
       ((er asl-param-types)
        (shallow-resolve-param-types f.parameters asl-param-env-term asl-params-v_int-hyp state))
       ((er asl-arg-types)
        (shallow-resolve-arg-types f.args asl-param-env-term asl-params-v_int-hyp state))

       (nondup-asl-arg-types (remove-corresponding-elements args asl-arg-types params))

       ((er asl-to-native-args) (shallow-asl-to-native-args
                                 (append params nondup-args)
                                 (append asl-param-types nondup-asl-arg-types)
                                 asl-params-v_int-hyp state))

       
       
       (return-binder (if (symbolp returns) returns `(list . ,returns)))

       ((er asl-return-type)
        (shallow-resolve-type f.return_type asl-params-v_int-hyp asl-param-env-term state))
       ((er asl-return-type/s)
        (b* ((returntype (ty->val f.return_type)))
          (type_desc-case returntype
            :t_tuple (shallow-resolve-type-list returntype.types asl-params-v_int-hyp asl-param-env-term state)
            :otherwise (value asl-return-type))))

       ((er asl-return-exprs)
        (if returntype-is-tuple
            (shallow-type->native-wrap-exprlist asl-return-type/s returns asl-params-v_int-hyp state)
          (shallow-type->native-wrap-exprlist (list asl-return-type) (list returns) asl-params-v_int-hyp state))))
       
    (value `(define ,name ,formals
              :returns (returnval ,return-concl
                                  :rule-classes nil :name ,return-sig-thmname)
              (let* ,fixers
                ,body)
              ///

              (defret ,return-rewrite-thmname
                (implies ,return-hyp
                         ,return-rewrites)
                :hints (("goal" :use ,return-sig-thmname
                         :in-theory (disable ,name)))
                :rule-classes :rewrite)
              
              ,@(and return-type-prescrip
                     `((defret ,return-type-prescrip-thmname
                         ,return-type-prescrip
                         :hints (("goal" :use ,return-sig-thmname
                                  :in-theory (disable ,name
                                                      ,return-rewrite-thmname)))
                         :rule-classes :type-prescription)))

              ,@(and return-forward
                     `((defret ,return-forward-thmname
                         ,return-forward
                         :hints (("goal" :use ,return-sig-thmname
                                  :in-theory (disable ,name
                                                      ,return-rewrite-thmname)))
                         :rule-classes ((:forward-chaining :trigger-terms ((equal (shallow_result-kind <call>)
                                                                                  :sh_normal)))))))
              
              (def-asl-subprogram ,(intern-in-package-of-symbol
                                    (concatenate 'string (symbol-name name) "-SHALLOW-CORRECT")
                                    'asl-pkg)
                :function ,function
                :params ,params
                :args ,args
                :safe-clock ,safe-clock
                ;; need list of formals wrapped in val type constructors
                :bindings ((impl (,name  . ,asl-to-native-args))
                           ,@(if always-normal
                                 `((,return-binder impl))
                               `(((sh_normal impl))
                                 (,return-binder impl.res))))
                ,@(and (not always-normal)
                       `(:normal-cond (shallow_result-case impl :sh_normal)
                         :nonnormal-res (shallow_result-case impl
                                          :sh_error (ev_error impl.desc impl.data)
                                          :otherwise (b* (((sh_throwing impl)))
                                                       (ev_throwing impl.throwdata
                                                                    (change-env env :local (empty-local-env)))))))
                :return-values ,asl-return-exprs)))))
            



(defmacro def-asl-shallow (name &rest args)
  (let* ((prepwork (cadr (assoc-keyword :prepwork args))))
    `(defsection ,name
       ,@prepwork
       (make-event (def-asl-shallow-fn ',name ',args state)))))



