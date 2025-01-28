;;****************************************************************************;;
;;                                ASLRef                                      ;;
;;****************************************************************************;;
;;
;; SPDX-FileCopyrightText: Copyright 2022-2023 Arm Limited and/or its affiliates <open-source-office@arm.com>
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

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "std/util/defenum" :dir :System)
(include-book "std/basic/two-nats-measure" :dir :system)

;; how should we deal with type aliases?  E.g., an identifier is a string, an uid is an int.


(defmacro def-type-alias (new-type existing-type)
  `(defprod ,new-type
     ((val ,existing-type))
     :layout :tree))

  ;; `(table fty::fixtypes ',new-type
  ;;         (cdr (assoc ',existing-type (table-alist 'fty::fixtypes world)))))

(def-type-alias identifier string)
(deflist identifierlist :elt-type identifier :true-listp t)

(def-type-alias uid acl2::int)

(defmacro def-annotated (new-type existing-type)
  `(def-type-alias ,new-type ,existing-type))

(defenum unop-p (:bnot :neg :not))

(defenum binop-p
  (:and
   :band
   :beq 
   :bor 
   :div 
   :divrm
   :eor 
   :eq_op
   :gt  
   :geq 
   :impl
   :lt  
   :leq 
   :mod 
   :minus
   :mul 
   :neq 
   :or  
   :plus
   :pow 
   :rdiv
   :shl 
   :shr 
   :bv_concat))

(deftagsum literal
  (:l_int ((val integerp :rule-classes :type-prescription)))
  (:l_bool ((val booleanp :rule-classes :type-prescription)))
  (:l_real ((val rationalp :rule-classes :type-prescription)))
  (:l_bitvector ((len natp :rule-classes :type-prescription)
                 (val natp :rule-classes :type-prescription)))
  (:l_string ((val stringp :rule-classes :type-prescription)))
  (:l_label ((val stringp :rule-classes :type-prescription))))


(defenum subprogram_type-p
  (:st_procedure :st_function :st_getter :st_emptygetter :st_emptysetter))

(defprod bitvector_mask
  ((length natp)
   (set natp)
   (unset natp))
  :layout :alist)

(deftypes expr
  (deftagsum expr_desc
    (:e_literal ((val literal)))
    (:e_var ((name identifier)))
    (:e_atc ((expr expr)
             (type ty)))
    (:e_binop ((op binop-p)
               (arg1 expr)
               (arg2 expr)))
    (:e_unop ((op unop-p)
              (arg expr)))
    (:e_call ((call call)))
    (:e_slice ((expr expr)
               (slices slicelist)))
    (:e_cond ((test expr)
              (then expr)
              (else expr)))
    (:e_getarray ((base expr)
                  (index expr)))
    (:e_getenumarray ((base expr)
                      (index expr)))
    (:e_getfield ((base expr)
                  (field identifier)))
    (:e_getfields ((base expr)
                   (fields identifierlist)))
    (:e_getitem ((base expr)
                 (index acl2::int)))
    (:e_record ((type ty)
                (fields fieldlist)))
    (:e_tuple ((exprs exprlist)))
    (:e_array ((length expr)
               (value expr)))
    (:e_enumarray ((enum identifier)
                   (labels identifierlist)
                   (value expr)))
    (:e_arbitrary ((type ty)))
    (:e_pattern ((expr expr)
                 (pattern pattern)))
    :base-case-override :e_literal
    :measure (acl2::two-nats-measure (acl2-count x) 10))

  (defprod expr ((val expr_desc)) :layout :tree
    :measure (acl2::two-nats-measure (acl2-count x) 20))

  (deflist exprlist :elt-type expr :true-listp t
    :measure (acl2::two-nats-measure (acl2-count x) 10))
  
  (deftagsum pattern_desc
    (:pattern_all ())
    (:pattern_any ((patterns patternlist)))
    (:pattern_geq ((expr expr)))
    (:pattern_leq ((expr expr)))
    (:patern_mask ((mask bitvector_mask)))
    (:pattern_not ((pattern pattern)))
    (:pattern_range ((lower expr)
                     (upper expr)))
    (:pattern_single ((expr expr)))
    (:pattern_tuple ((patterns patternlist)))
    :measure (acl2::two-nats-measure (acl2-count x) 10))

  (defprod pattern ((val pattern_desc)) :layout :tree
    :measure (acl2::two-nats-measure (acl2-count x) 20))

  (deflist patternlist :elt-type pattern :true-listp t
    :measure (acl2::two-nats-measure (acl2-count x) 10))
  
  (deftagsum slice
    (:slice_single ((index expr)))
    (:slice_range ((end expr)
                   (start expr)))
    (:slice_length ((start expr)
                    (length expr)))
    (:slice_star ((factor expr)
                  (length expr)))
    :base-case-override :slice_single
    :measure (acl2::two-nats-measure (acl2-count x) 30))

  (deflist slicelist :elt-type slice :true-listp t
    :measure (acl2::two-nats-measure (acl2-count x) 10))
  
  (defprod call
    ((name identifier)
     (params exprlist)
     (args exprlist)
     (call_type subprogram_type-p))
    :measure (acl2::two-nats-measure (acl2-count x) 20)
    :layout :alist)

  (deftagsum type_desc
    (:t_int ((constraint constraint_kind)))
    (:t_bits ((expr expr)
              (fields bitfieldlist)))
    (:t_real ())
    (:t_string ())
    (:t_bool ())
    (:t_enum ((elts identifierlist)))
    (:t_tuple ((types tylist)))
    (:t_array ((index array_index)
               (type ty)))
    (:t_record ((fields fieldlist)))
    (:t_exception ((fields fieldlist)))
    (:t_named ((name identifier)))
    :measure (acl2::two-nats-measure (acl2-count x) 10))

  (defprod ty ((val type_desc)) :layout :tree
    :measure (acl2::two-nats-measure (acl2-count x) 20))

  (deflist tylist :elt-type ty :true-listp t
    :measure (acl2::two-nats-measure (acl2-count x) 10))

  (deftagsum int_constraint
    (:constraint_exact ((val expr)))
    (:constraint_range ((from expr)
                        (to expr)))
    :base-case-override :constraint_exact
    :measure (acl2::two-nats-measure (acl2-count x) 30))

  (deflist int_constraintlist :elt-type int_constraint :true-listp t
    :measure (acl2::two-nats-measure (acl2-count x) 10))
  
  (deftagsum constraint_kind
    (:unconstrained ())
    (:wellconstrained ((constraints int_constraintlist)))
    (:pendingconstrained ())
    (:parameterized ((id uid)
                     (name identifier)))
    :measure (acl2::two-nats-measure (acl2-count x) 10))

  (deftagsum bitfield
    (:bitfield_simple ((name identifier)
                       (slices slicelist)))
    (:bitfield_nested ((name identifier)
                       (slices slicelist)
                       (nested bitfieldlist)))
    (:bitfield_type ((name identifier)
                     (slices slicelist)
                     (type ty)))
    :base-case-override :bitfield_simple
    :measure (acl2::two-nats-measure (acl2-count x) 20))

  (deflist bitfieldlist :elt-type bitfield :true-listp t
    :measure (acl2::two-nats-measure (acl2-count x) 10))

  (deftagsum array_index
    (:arraylength ((length expr)))
    (:arraylength_enum ((name identifier)
                        (elts identifierlist)))
    :measure (acl2::two-nats-measure (acl2-count x) 10))

  (defprod field
    ((name identifier)
     (type ty))
    :measure (acl2::two-nats-measure (acl2-count x) 30)
    :layout :tree)

  (deflist fieldlist :elt-type field :true-listp t
    :measure (acl2::two-nats-measure (acl2-count x) 10)

    :measure-debug t))



