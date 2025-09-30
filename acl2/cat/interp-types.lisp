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

(in-package "CAT")

(include-book "ast")
(local (table fty::deftagsum-defaults :short-names t))
(local (std::add-default-post-define-hook :fix))

(deftagsum evttype
  (:evt-r ((addr natp :rule-classes :type-prescription)
           (val natp :rule-classes :type-prescription)
           ;; UID of corresponding write event
           (from natp :rule-classes :type-prescription)))
  (:evt-w ((addr natp :rule-classes :type-prescription)
           (val natp :rule-classes :type-prescription)
           (initp booleanp)))
  (:evt-b ())
  (:evt-f ()))

(defenum evtkind-p (:evt-r :evt-w :evt-b :evt-f))

(defthm evtkind-p-of-evttype-kind
  (evtkind-p (evttype-kind x))
  :hints(("Goal" :in-theory (enable evttype-kind))))

;; TODO flesh this out
(defprod evt
  ((uid natp :rule-classes :type-prescription)
   (procid natp :rule-classes :type-prescription)
   (po-index natp :rule-classes :type-prescription)
   (data evttype)))

(deflist evtlist :elt-type evt :true-listp t :elementp-of-nil nil
  ///
  (defthm evtlist-p-of-append
    (implies (and (evtlist-p x)
                  (evtlist-p y))
             (evtlist-p (append x y)))))


(defprod execgraph
  ((evts evtlist)))


(defprod evtpair
  ((from evt) (to evt))
  :layout :list)


(fty::defset relation :elt-type evtpair :elementp-of-nil nil)

(defprod fndef
  ((name var)
   (formals pat)
   (body exp)))
  
(deflist fndeflist :elt-type fndef :true-listp t :elementp-of-nil nil)


(deftypes val
  (deftagsum val
    ;; Empty; may be a set, valset, or relation, we don't need to distinguish.
    ;; This is useful for computing least fixpoints of relations, so that we
    ;; don't need to know what kind the starting variables should be.
    (:v_empty  ())
    (:v_tag    ((tag tag)))
    (:v_rel    ((rel relation)))
    (:v_set    ((evts evtlist))) ;; events are not values so this is a separate category than valset
    (:v_valset ((elts vallist))) ;; needs to satisfy well-formedness condition
    (:v_tuple  ((elts vallist))) ;; needs to have 0 or 2 or more elements
    (:v_enum   ((tags taglist)))
    (:v_fun    ((formals pat)
                (body exp)
                ;; Extension to represent the non-well-founded recursive function
                ;; binding form: if fndeflist is nonempty then this function
                ;; represents the infinite closure where env includes the bindings
                ;; of each name in recdefs to the corresponding closure that
                ;; includes that env itself.
                (recdefs fndeflist)
                (env env)))
    (:v_proc   ((formals pat)
                (body inslist)
                (env env))))

  (deflist vallist :elt-type val :true-listp t :elementp-of-nil nil)

  (fty::defmap env :key-type var :val-type val :true-listp t :keyp-of-nil nil :valp-of-nil nil))

(defthm env-p-of-append
  (implies (and (env-p x)
                (env-p y))
           (env-p (append x y))))

(defenum val-kind-p (:v_empty :v_tag :v_rel :v_set :v_valset :v_tuple :v_enum :v_fun :v_proc))
(defthm val-kind-p-of-val-kind
  (val-kind-p (val-kind x))
  :hints(("Goal" :in-theory (enable val-kind))))

(defenum judgement-p (:allowed :forbidden))

(defprod result
  ((judgement judgement-p)
   (flags varlist-p)
   (env env)
   (comrels varlist-p)))

(deflist resultlist :elt-type result :true-listp t :elementp-of-nil nil
  ///
  (defthm resultlist-p-of-append
    (implies (and (resultlist-p x)
                  (resultlist-p y))
             (resultlist-p (append x y)))))

(define vallist-same-kind-aux ((kind val-kind-p) (x vallist-p))
  (if (atom x)
      t
    (and (eq (val-kind (car x)) (val-kind-fix kind))
         (vallist-same-kind-aux kind (cdr x)))))

(define vallist-same-kind ((x vallist-p))
  (or (atom x)
      (vallist-same-kind-aux (val-kind (car x)) (cdr x))))
                               

(defines well-formed
  (define val-well-formed ((x val-p))
    :measure (val-count x)
    :hints ((and stable-under-simplificationp
                 '(:expand ((val-count x)))))
    (val-case x
      :v_valset (and (vallist-same-kind x.elts)
                     (vallist-well-formed x.elts))
      :v_tuple (and (or (atom x.elts)
                        (consp (cdr x.elts)))
                    (vallist-well-formed x.elts))
      :v_fun (env-well-formed x.env)
      :v_proc (env-well-formed x.env)
      :otherwise t))

  (define vallist-well-formed ((x vallist-p))
    :measure (vallist-count x)
    (if (atom x)
        t
      (and (val-well-formed (car x))
           (vallist-well-formed (cdr x)))))

  (define env-well-formed ((x env-p))
    :measure (env-count x)
    (b* ((x (env-fix x)))
      (if (atom x)
          t
        (and (val-well-formed (cdar x))
             (env-well-formed (cdr x))))))

  ///
  (fty::deffixequiv-mutual well-formed))
      
   

