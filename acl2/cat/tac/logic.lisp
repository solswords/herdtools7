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

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "tools/templates" :dir :system)
(local (include-book "std/lists/sets" :dir :System))
(local (std::add-default-post-define-hook :fix))


(encapsulate
  (((universe) => * :guard t :formals ())
   ((some-event) => * :guard t :formals ()))

  (local (defun universe () (list nil)))
  (local (defun some-event () nil))
  (defthm setp-of-universe
    (setp (universe)))

  (defthm some-event-in-universe
    (in (some-event) (universe))))

(define event-p (x)
  (in x (universe))
  ///
  (defthm event-p-of-some-event
    (event-p (some-event)))

  (in-theory (disable (event-p))))

(define event-fix ((x event-p))
  :returns (new-x event-p)
  (mbe :logic (if (event-p x) x (some-event))
       :exec x)
  ///
  (defret <fn>-when-event-p
    (implies (event-p x)
             (equal new-x x)))

  (fty::deffixtype event
    :pred event-p
    :fix event-fix
    :equiv event-equiv
    :define t :forward t)

  (in-theory (Disable (event-fix))))



;; (define event-set-p1-badguy ((x setp))
;;   :returns (badguy)
;;   (if (emptyp x)
;;       (some-event)
;;     (if (or (not (event-p (head x)))
;;             (emptyp (tail x)))
;;         (head x)
;;       (event-set-p1-badguy (tail x))))
;;   ///
;;   (defretd event-set-p1-when-badguy
;;     (implies (event-p badguy)
;;              (event-set-p1 x))
;;     :hints(("Goal" :in-theory (enable event-set-p1))))

;;   (defret in-of-badguy
;;     (implies (not (emptyp x))
;;              (in badguy x))))

(local (defthmd emptyp-when-setp
         (implies (setp x)
                  (iff (emptyp x) (not x)))
         :hints(("Goal" :in-theory (enable emptyp)))))

;; --------------------------------------------------------------------------
;; Define event-set type, where the fixing function filters events in the given set
(define event-set-p1 ((x setp))
  (if (emptyp x)
      t
    (and (event-p (head x))
         (event-set-p1 (tail x))))
  ///
  (defthmd event-set-p1-implies-not-in-when-not-event
    (implies (and (event-set-p1 x)
                  (not (event-p e)))
             (not (in e x)))))

(define event-set-p (x)
  (and (setp x)
       (event-set-p1 x))
  ///
  (defthmd event-set-p-implies-not-in-when-not-event
    (implies (and (event-set-p x)
                  (not (event-p e)))
             (not (in e x)))
    :hints(("Goal" :in-theory (enable event-set-p1-implies-not-in-when-not-event))))

  (defthm event-p-head-when-event-set-p
    (implies (and (event-set-p x)
                  (not (emptyp x)))
             (event-p (head x)))
    :hints(("Goal" :in-theory (enable event-set-p1))))

  (defthm event-set-p-tail-when-event-set-p
    (implies (event-set-p x)
             (event-set-p (tail x)))
    :hints(("Goal" :in-theory (enable event-set-p1))))

  (defthm setp-when-event-set-p
    (implies (event-set-p x) (setp x))))

(define event-set-p-badguy ((x setp))
  :returns (badguy)
  (if (emptyp x)
      (some-event)
    (if (and (event-p (head x))
             (not (emptyp (tail x))))
        (event-set-p-badguy (tail x))
      (head x)))
  ///
  (defretd event-set-p-by-badguy
    (implies (and (not (and (in badguy x)
                            (not (event-p badguy))))
                  (setp x))
             (event-set-p x))
    :hints(("Goal" :in-theory (enable event-set-p event-set-p1))))

  (defretd event-set-p-iff-badguy
    (implies (acl2::rewriting-positive-literal `(event-set-p ,x))
             (iff (event-set-p x)
                  (and (not (and (in badguy x)
                            (not (event-p badguy))))
                       (setp x))))
    :hints(("Goal" :in-theory (enable event-set-p-by-badguy
                                      event-set-p-implies-not-in-when-not-event))
           (and stable-under-simplificationp
                '(:in-theory (enable event-set-p)))))

  (local (in-theory (enable event-set-p-iff-badguy
                            event-set-p-implies-not-in-when-not-event)))
  
  (defthm event-set-p-of-insert
    (implies (and (event-set-p x)
                  (event-p e))
             (event-set-p (insert e x))))

  (defthm event-set-p-of-union
    (implies (and (event-set-p x)
                  (event-set-p y))
             (event-set-p (union x y))))

  (defthm event-set-p-of-intersect
    (implies (or (event-set-p x)
                 (event-set-p y))
             (event-set-p (intersect x y))))

  (defthm event-set-p-of-difference
    (implies (event-set-p x)
             (event-set-p (difference x y))))

  (defthm event-set-p-of-delete
    (implies (event-set-p x)
             (event-set-p (delete e x))))

  (defthm event-set-p-of-universe
    (event-set-p (universe))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable event-p))))))
    
(define event-set-fix ((x event-set-p))
  :returns (new-x event-set-p
                  :hints(("Goal" :in-theory (enable event-set-p event-set-p1))))
  :verify-guards nil
  (mbe :logic (if (emptyp x)
                  nil
                (if (event-p (head x))
                    (insert (head x)
                            (event-set-fix (tail x)))
                  (event-set-fix (tail x))))
       :exec x)
  ///
  (defret <fn>-when-event-set-p
    (implies (event-set-p x)
             (equal new-x x))
    :hints(("Goal" :in-theory (enable event-set-p event-set-p1
                                      emptyp-when-setp))))

  (verify-guards event-set-fix
    :hints(("Goal" :in-theory (enable event-set-p event-set-p1
                                      emptyp-when-setp))))

  (defretd in-of-<fn>
    (iff (in e new-x)
         (and (event-p e) (in e x))))

  (fty::deffixtype event-set
    :pred event-set-p
    :fix event-set-fix
    :equiv event-set-equiv
    :define t :forward t))



(defprod edge
  ((src event) (dst event))
  :layout :list)

;; --------------------------------------------------------------------------
;; Define relation type
;; This is copy+paste of event-set type with events replaced by edges
(define relation-p1 ((x setp))
  (if (emptyp x)
      t
    (and (edge-p (head x))
         (relation-p1 (tail x))))
  ///
  (defthmd relation-p1-implies-not-in-when-not-edge
    (implies (and (relation-p1 x)
                  (not (edge-p e)))
             (not (in e x)))))

(define relation-p (x)
  (and (setp x)
       (relation-p1 x))
  ///
  (defthmd relation-p-implies-not-in-when-not-edge
    (implies (and (relation-p x)
                  (not (edge-p e)))
             (not (in e x)))
    :hints(("Goal" :in-theory (enable relation-p1-implies-not-in-when-not-edge))))

  (defthm edge-p-head-when-relation-p
    (implies (and (relation-p x)
                  (not (emptyp x)))
             (edge-p (head x)))
    :hints(("Goal" :in-theory (enable relation-p1))))

  (defthm relation-p-tail-when-relation-p
    (implies (relation-p x)
             (relation-p (tail x)))
    :hints(("Goal" :in-theory (enable relation-p1))))

  (defthm setp-when-relation-p
    (implies (relation-p x) (setp x))))

(define relation-p-badguy ((x setp))
  :returns (badguy)
  (if (emptyp x)
      (edge (some-event) (some-event))
    (if (and (edge-p (head x))
             (not (emptyp (tail x))))
        (relation-p-badguy (tail x))
      (head x)))
  ///
  (defretd relation-p-by-badguy
    (implies (and (not (and (in badguy x)
                            (not (edge-p badguy))))
                  (setp x))
             (relation-p x))
    :hints(("Goal" :in-theory (enable relation-p relation-p1))))

  (defretd relation-p-iff-badguy
    (implies (acl2::rewriting-positive-literal `(relation-p ,x))
             (iff (relation-p x)
                  (and (not (and (in badguy x)
                            (not (edge-p badguy))))
                       (setp x))))
    :hints(("Goal" :in-theory (enable relation-p-by-badguy
                                      relation-p-implies-not-in-when-not-edge))
           (and stable-under-simplificationp
                '(:in-theory (enable relation-p)))))

  (local (in-theory (enable relation-p-iff-badguy
                            relation-p-implies-not-in-when-not-edge)))
  
  (defthm relation-p-of-insert
    (implies (and (relation-p x)
                  (edge-p e))
             (relation-p (insert e x))))

  (defthm relation-p-of-union
    (implies (and (relation-p x)
                  (relation-p y))
             (relation-p (union x y))))

  (defthm relation-p-of-intersect
    (implies (or (relation-p x)
                 (relation-p y))
             (relation-p (intersect x y))))

  (defthm relation-p-of-difference
    (implies (relation-p x)
             (relation-p (difference x y))))

  (defthm relation-p-of-delete
    (implies (relation-p x)
             (relation-p (delete e x)))))
    
(define relation-fix ((x relation-p))
  :returns (new-x relation-p
                  :hints(("Goal" :in-theory (enable relation-p relation-p1))))
  :verify-guards nil
  (mbe :logic (if (emptyp x)
                  nil
                (if (edge-p (head x))
                    (insert (head x)
                            (relation-fix (tail x)))
                  (relation-fix (tail x))))
       :exec x)
  ///
  (defret <fn>-when-relation-p
    (implies (relation-p x)
             (equal new-x x))
    :hints(("Goal" :in-theory (enable relation-p relation-p1
                                      emptyp-when-setp))))

  (verify-guards relation-fix
    :hints(("Goal" :in-theory (enable relation-p relation-p1
                                      emptyp-when-setp))))

  (defretd in-of-<fn>
    (iff (in e new-x)
         (and (edge-p e) (in e x))))

  (fty::deffixtype relation
    :pred relation-p
    :fix relation-fix
    :equiv relation-equiv
    :define t :forward t))

(local (defthm cardinality-of-tail
         (implies (not (emptyp x))
                  (equal (cardinality (tail x))
                         (- (cardinality x) 1)))
         :hints (("goal" :expand ((cardinality x))))))


(define empty-relation ()
  :returns (rel relation-p)
  nil)

(local (defthmd emptyp-iff-in-head
         (iff (emptyp x)
              (not (in (head x) x)))))


(define event-set-elem ((x event-set-p))
  :returns (e event-p)
  :guard (not (emptyp x))
  (event-fix (head (event-set-fix x)))
  ///
  (defret in-of-event-set-elem
    (implies (equal x1 (event-set-fix x))
             (iff (in e x1)
                  (not (emptyp (event-set-fix x)))))
    :hints (("goal" :use ((:instance in-of-event-set-fix
                           (e (head (event-set-fix x)))))
             :in-theory (e/d (emptyp-iff-in-head)
                             (set::in-head
                              set::head-when-emptyp
                              in-of-event-set-fix))))))

;; (local (defthm in-tail-of-event-set-fix
;;          (implies (not (equal e (head (event-set-fix x))))
;;                   (equal (in e (tail (event-set-fix x)))
;;                          (and (not (emptyp (event-set-fix x)))
;;                               (event-p e)
;;                               (in e x))))
;;          :hints (("goal" :use in-of-event-set-fix
;;                   :expand ((in e (event-set-fix x)))
;;                   :in-theory (disable in-of-event-set-fix)))))

;; (local (defthm not-in-tail-of-event-set-fix
;;          (implies (not (and (not (emptyp (event-set-fix x)))
;;                             (event-p e)
;;                             (in e x)))
;;                   (not (in e (tail (event-set-fix x)))))
;;          :hints (("goal" :use in-of-event-set-fix
;;                   :expand ((in e (event-set-fix x)))
;;                   :in-theory (disable in-of-event-set-fix)))))

;; (local (defthm head-of-event-set-fix-in-x
;;          (implies (not (emptyp (event-set-fix x)))
;;                   (in (head (event-set-fix x)) x))
;;          :hints (("goal" :in-theory (e/d (emptyp-iff-in-head)
;;                                          (set::in-head
;;                                           set::head-when-emptyp))))))


(define relidentity ((x event-set-p))
  :returns (rel relation-p)
  :verify-guards nil
  :measure (cardinality (event-set-fix x))
  (b* ((x (event-set-fix x)))
    (if (emptyp x)
        nil
      (insert (edge (head x) (head x))
              (relidentity (tail x)))))
  ///
  (verify-guards relidentity)
  (defret in-of-<fn>
    (iff (in pair rel)
         (and (edge-p pair)
              (equal (edge->src pair) (edge->dst pair))
              (in (edge->src pair) (event-set-fix x))))))

(define cartesian1 ((x event-p)
                    (y event-set-p))
  :returns (prod relation-p)
  :measure (cardinality (event-set-fix y))
  :verify-guards nil
  (b* ((y (event-set-fix y)))
    (if (emptyp y)
        nil
      (insert (edge x (head y))
              (cartesian1 x (tail y)))))
  ///
  (verify-guards cartesian1)
  (defretd in-of-<fn>
    (iff (in pair prod)
         (and (edge-p pair)
              (Equal (edge->src pair) (event-fix x))
              (in (edge->dst pair) (event-set-fix y))))))

(define relprod ((x event-set-p)
                   (y event-set-p))
  :returns (prod relation-p)
  :verify-guards nil
  :measure (cardinality (event-set-fix x))
  (b* ((x (event-set-fix x)))
    (if (emptyp x)
        nil
      (union (cartesian1 (head x) y)
             (relprod (tail x) y))))
  ///
  (verify-guards relprod)
  
  (defretd in-of-<fn>
    (iff (in pair prod)
         (and (edge-p pair)
              (in (edge->src pair) (event-set-fix x))
              (in (edge->dst pair) (event-set-fix y))))
    :hints(("Goal" :in-theory (enable in-of-cartesian1)))))


(local (defthm in-event-set-fix-forward-event-p
         (implies (in w (event-set-fix x))
                  (event-p w))
         :hints(("Goal" :in-theory (enable event-set-p-implies-not-in-when-not-event)))
         :rule-classes :forward-chaining))



(local (defthm edge-of-dst-and-equiv-src
         (implies (event-equiv src (edge->src x) )
                  (equal (edge src (edge->dst x))
                         (edge-fix x)))))

(local (defthm edge-of-src-and-equiv-dst
         (implies (event-equiv dst (edge->dst x))
                  (equal (edge (edge->src x) dst)
                         (edge-fix x)))))

(define setimage ((s event-set-p) (r relation-p))
  :returns (im event-set-p)
  :measure (cardinality (relation-fix r))
  :verify-guards nil
  (b* ((r (relation-fix r)))
    (b* (((when (emptyp r)) nil)
         ((edge x) (head r))
         (rest (setimage s (tail r))))
      (if (in x.src (event-set-fix s))
          (insert x.dst rest)
        rest)))
  ///
  (verify-guards setimage)
  (defret in-of-setimage-suff
    (implies (and (in (edge w v) (relation-fix r))
                  (in (event-fix w) (event-set-fix s))
                  (event-p v))
             (in v im))
    :hints (("goal" :induct <call>
             :expand ((in (edge w v) (relation-fix r))))))
  
  (defret in-of-setimage-suff2
    (implies (and (in w (event-set-fix s))
                  (in (edge w v) (relation-fix r))
                  (event-p v))
             (in v im)))

  (defret in-of-setimage-suff3
    (implies (and (in w s)
                  (in (edge w v) (relation-fix r))
                  (event-p w)
                  (event-p v))
             (in v im))
    :hints(("Goal" :in-theory (enable in-of-event-set-fix)))))

(define setimage-witness ((v event-p) (s event-set-p) (r relation-p))
  :returns (w event-p)
  :measure (cardinality (relation-fix r))
  :verify-guards nil
  (b* ((r (relation-fix r)))
    (b* (((when (emptyp r)) (some-event))
         ((edge x) (head r))
         ((when (and (event-equiv v x.dst)
                     (in x.src (event-set-fix s))))
          x.src))
      (setimage-witness v s (tail r))))
  ///
  (verify-guards setimage-witness)
  
  (defret setimage-witness-when-in-setimage
    (implies (in v (setimage s r))
             (and (in w (event-set-fix s))
                  (in (edge w v) (relation-fix r))))
    :hints(("Goal" :in-theory (enable setimage))))

  (defretd in-of-setimage-rw
    (implies (and (acl2::rewriting-negative-literal `(in ,v (setimage ,s ,r))))
             (iff (in v (setimage s r))
                  (and (event-p v)
                       (in w (event-set-fix s))
                       (in (edge w v) (relation-fix r)))))
    :hints(("Goal" :in-theory (e/d (event-set-p-implies-not-in-when-not-event)
                                   (setimage-witness))))))

(define setpreimage ((r relation-p) (s event-set-p))
  :returns (im event-set-p)
  :measure (cardinality (relation-fix r))
  :verify-guards nil
  (b* ((r (relation-fix r)))
    (b* (((when (emptyp r)) nil)
         ((edge x) (head r))
         (rest (setpreimage (tail r) s)))
      (if (in x.dst (event-set-fix s))
          (insert x.src rest)
        rest)))
  ///
  (verify-guards setpreimage)
  
  (defret in-of-setpreimage-suff
    (implies (and (in (edge v w) (relation-fix r))
                  (in (event-fix w) (event-set-fix s))
                  (event-p v))
             (in v im))
    :hints (("goal" :induct <call>
             :expand ((in (edge v w) (relation-fix r))))))
  
  (defret in-of-setpreimage-suff2
    (implies (and (in w (event-set-fix s))
                  (in (edge v w) (relation-fix r))
                  (event-p v))
             (in v im)))

  (defret in-of-setpreimage-suff3
    (implies (and (in w s)
                  (in (edge v w) (relation-fix r))
                  (event-p w)
                  (event-p v))
             (in v im))
    :hints(("Goal" :in-theory (enable in-of-event-set-fix)))))

(define setpreimage-witness ((v event-p) (r relation-p) (s event-set-p))
  :returns (w event-p)
  :measure (cardinality (relation-fix r))
  :verify-guards nil
  (b* ((r (relation-fix r)))
    (b* (((when (emptyp r)) (some-event))
         ((edge x) (head r))
         ((when (and (event-equiv x.src v)
                     (in x.dst (event-set-fix s))))
          x.dst))
      (setpreimage-witness v (tail r) s)))
  ///
  (verify-guards setpreimage-witness)
  
  (defret setpreimage-witness-when-in-setpreimage
    (implies (in v (setpreimage r s))
             (and (in w (event-set-fix s))
                  (in (edge v w) (relation-fix r))))
    :hints(("Goal" :in-theory (enable setpreimage))))

  (defretd in-of-setpreimage-rw
    (implies (and (acl2::rewriting-negative-literal `(in ,v (setpreimage ,r ,s))))
             (iff (in v (setpreimage r s))
                  (and (event-p v)
                       (in w (event-set-fix s))
                       (in (edge v w) (relation-fix r)))))
    :hints(("Goal" :in-theory (e/d (event-set-p-implies-not-in-when-not-event)
                                   (setpreimage-witness))))))




;; For any pair (dst, dst2) in x, includes (src, dst2) in result.
(define compose1 ((src event-p) (dst event-p)
                  (x relation-p))
  :returns (compose relation-p)
  :measure (cardinality (relation-fix x))
  :verify-guards nil
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        nil
      (if (event-equiv dst (edge->src (head x)))
          (insert (edge src (edge->dst (head x)))
                  (compose1 src dst (tail x)))
        (compose1 src dst (tail x)))))
  ///
  (verify-guards compose1)
  (defretd in-of-<fn>
    (iff (in pair compose)
         (and (edge-p pair)
              (event-equiv (edge->src pair) src)
              (in (edge dst (edge->dst pair))
                  (relation-fix x))))
    :hints(("Goal" :in-theory (enable in)))))

(define relcompose ((x relation-p)
                    (y relation-p))
  :returns (compose relation-p)
  :measure (cardinality (relation-fix x))
  :verify-guards nil
  (b* ((x (relation-fix x)))
    (if (emptyp x)
      nil
      (union (compose1 (edge->src (head x))
                       (edge->dst (head x))
                       y)
             (relcompose (tail x) y))))
  ///
  (verify-guards relcompose)
  (defretd in-of-relcompose-suff
    (implies (and (edge-p pair)
                  (in (edge (edge->src pair) mid) (relation-fix x))
                  (in (edge mid (edge->dst pair)) (relation-fix y)))
             (in pair compose))
    :hints(("Goal" :in-theory (enable in-of-compose1))))

  (defretd in-of-relcompose-suff2
    (implies (and (edge-p pair)
                  (in (edge mid (edge->dst pair)) (relation-fix y))
                  (in (edge (edge->src pair) mid) (relation-fix x)))
             (in pair compose))
    :hints(("Goal" :in-theory (enable in-of-compose1))))

  (defretd in-of-relcompose-suff-rw
    (implies (and (in (edge src mid) (relation-fix x))
                  (in (edge mid dst) (relation-fix y)))
             (in (edge src dst) compose))
    :hints(("Goal" :in-theory (enable in-of-compose1))))

  (defretd in-of-relcompose-suff-rw2
    (implies (and (in (edge mid dst) (relation-fix y))
                  (in (edge src mid) (relation-fix x)))
             (in (edge src dst) compose))
    :hints(("Goal" :in-theory (enable in-of-relcompose-suff-rw)))))

(local (include-book "std/util/termhints" :dir :system))

(define relcompose-midpoint ((src event-p)
                          (dst event-p)
                          (x relation-p)
                          (y relation-p))
  :returns (mid event-p)
  :measure (cardinality (relation-fix x))
  ;; Witness for compose membership. If (src . dst) are in the composition of x
  ;; and y, then (relcompose-midpoint src dst x y) produces mid such that (src
  ;; . mid) is in x and (mid . dst) is in y.
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        (some-event)
      (if (and (event-equiv src (edge->src (head x)))
               (in (edge (edge->dst (head x)) dst)
                   (relation-fix y)))
          (edge->dst (head x))
        (relcompose-midpoint src dst (tail x) y))))
  ///
  ;; (local (defthm in-cons-relation
  ;;          (implies (And (relation-p y)
  ;;                        (not (and (evt-p dst)
  ;;                                  (evt-p src))))
  ;;                   (not (in-equal (cons src dst) y)))))

  ;; (local (defthm in-relation-not-consp
  ;;          (implies (And (relation-p y)
  ;;                        (not (edge-p pair)))
  ;;                   (not (in-equal pair y)))))

  (defret relcompose-midpoint-when-in-relcompose
    (implies (in (edge src dst) (relcompose x y))
             (and (in (edge src mid) (relation-fix x))
                  (in (edge mid dst) (relation-fix y))))
    :hints(("Goal" :in-theory (enable relcompose
                                      in-of-compose1))))
  
  (defret relcompose-midpoint-witnesses
    (implies (and (in (edge src mid1) (relation-fix x))
                  (in (edge mid1 dst) (relation-fix y)))
             (and (in (edge src mid) (relation-fix x))
                  (in (edge mid dst) (relation-fix y))))
    :hints(("Goal" :in-theory (enable in))
           (and stable-under-simplificationp
                '(:induct (relcompose-midpoint src dst x y))))
    :otf-flg t)

  (defretd in-of-relcompose-necc
    :pre-bind ((src (edge->src pair))
               (dst (edge->dst pair)))
    (implies (not (and (in (edge (edge->src pair) mid) (relation-fix x))
                       (in (edge mid (edge->dst pair)) (relation-fix y))))
             (not (in pair (relcompose x y))))
    :hints(("Goal" :in-theory (enable relcompose
                                      in
                                      in-of-relcompose-suff
                                      in-of-compose1)))
    :otf-flg t)

  (fty::deffixequiv relcompose-midpoint)
  
  (defretd in-of-relcompose-implies-fix
    :pre-bind ((pair (edge src dst)))
    (implies (and (in pair (relcompose x y)))
             (and (in (edge src mid) (relation-fix x))
                  (in (edge mid dst) (relation-fix y))))
    :hints(("Goal" :use ((:instance in-of-relcompose-necc
                          (pair (edge src dst)))))))
  
  (defretd in-of-relcompose-implies
    :pre-bind ((pair (edge src dst)))
    (implies (and (in pair (relcompose x y)))
             (and (implies (relation-p x)
                           (in (edge src mid) x))
                  (implies (relation-p y)
                           (in (edge mid dst) y))))
    :hints(("Goal" :use ((:instance in-of-relcompose-necc
                          (pair (edge src dst)))))))
                         
  (defretd in-of-relcompose
    :pre-bind ((src (edge->src pair))
               (dst (edge->dst pair)))
    (iff (in pair (relcompose x y))
         (and (edge-p pair)
              (in (edge (edge->src pair) mid) (relation-fix x))
              (in (edge mid (edge->dst pair)) (relation-fix y))))
    :hints(("Goal" :in-theory (enable in-of-relcompose-necc
                                      in-of-relcompose-suff
                                      relation-p-implies-not-in-when-not-edge))))

  (defretd in-of-relcompose-rw
    :pre-bind ((src (edge->src pair))
               (dst (edge->dst pair)))
    (implies (acl2::rewriting-negative-literal `(in ,pair (relcompose ,x ,y)))
             (iff (in pair (relcompose x y))
                  (and (edge-p pair)
                       (in (edge (edge->src pair) mid) (relation-fix x))
                       (in (edge mid (edge->dst pair)) (relation-fix y)))))
    :hints(("Goal" :in-theory (enable in-of-relcompose))))


  (defthm relcompose-associative
    (equal (relcompose (relcompose x y) z)
           (relcompose x (relcompose y z)))
    :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                      set::double-containment-no-backchain-limit))
           (SET::PICK-A-POINT-SUBSET-HINT ID acl2::CLAUSE
                                          WORLD STABLE-UNDER-SIMPLIFICATIONP)
           (and stable-under-simplificationp
                (acl2::use-termhint
                 (b* ((elem set::arbitrary-element)
                      ((edge elem)))
                   (if (in elem (relcompose (relcompose x y) z))
                       (b* ((step2 (relcompose-midpoint elem.src elem.dst (relcompose x y) z))
                            (step1 (relcompose-midpoint elem.src step2 x y))
                            (pair1 (edge step1 elem.dst)))
                         `(:use ((:instance acl2::mark-clause-is-true (x '(in elem (relcompose (relcompose x y) z))))
                                 (:instance in-of-relcompose-suff
                                  (x x) (y (relcompose y z))
                                  (pair ,(acl2::hq elem))
                                  (mid ,(acl2::hq step1)))
                                 (:instance in-of-relcompose-suff
                                  (x y) (y z)
                                  (pair ,(acl2::hq pair1))
                                  (mid ,(acl2::hq step2))))
                           :in-theory (enable in-of-relcompose-rw)))
                     (b* ((step1 (relcompose-midpoint elem.src elem.dst x (relcompose y z)))
                          (step2 (relcompose-midpoint step1 elem.dst y z))
                          (pair2 (edge elem.src step2)))
                       `(:use ((:instance acl2::mark-clause-is-true (x '(in elem (relcompose x (relcompose y z)))))
                               (:instance in-of-relcompose-suff
                                (x (relcompose x y)) (y z)
                                (pair ,(acl2::hq elem))
                                (mid ,(acl2::hq step2)))
                               (:instance in-of-relcompose-suff
                                (x x) (y y)
                                (pair ,(acl2::hq pair2))
                                (mid ,(acl2::hq step1))))
                         :in-theory (enable in-of-relcompose-rw))))))))))



(define domain ((x relation-p))
  :returns (dom event-set-p)
  :measure (cardinality (relation-fix x))
  :verify-guards nil
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        nil
      (insert (edge->src (head x))
              (domain (tail x)))))
  ///
  (verify-guards domain)
  (defretd in-of-domain-suff
    (implies (and (in (edge src dst) (relation-fix x))
                  (event-p src))
             (in src dom))
    :hints(("Goal" :in-theory (enable in))))

  (defretd in-of-domain-suff-free
    (implies (and (in (edge src dst) some-rel)
                  (in (edge src dst) (relation-fix x))
                  (event-p src))
             (in src dom))
    :hints(("Goal" :in-theory (enable in-of-domain-suff))))

  (defret in-src-of-domain
    (implies (in pair (relation-fix x))
             (in (edge->src pair) dom))
    :hints(("Goal" :in-theory (enable in)))))

(define domain-witness ((src event-p) (x relation-p))
  :returns (dst event-p)
  :measure (cardinality (relation-fix x))
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        (some-event)
      (if (event-equiv src (edge->src (head x)))
          (edge->dst (head x))
        (domain-witness src (tail x)))))
  ///

  (defret domain-witness-witnesses
    (implies (in (edge src dst1) (relation-fix x))
             (in (edge src dst) (relation-fix x)))
    :hints(("Goal" :in-theory (enable in))))
  
  (defretd in-of-domain-necc
    (implies (not (in (edge src dst) (relation-fix x)))
             (not (in src (domain x))))
    :hints(("Goal" :in-theory (enable domain in))))

  (defretd in-of-domain
    (iff (in src (domain x))
         (and (event-p src)
              (in (edge src dst) (relation-fix x))))
    :hints(("Goal" :in-theory (enable in-of-domain-necc
                                      in-of-domain-suff
                                      domain)))
    :otf-flg t)

  (defretd in-of-domain-rw
    (implies (acl2::rewriting-negative-literal `(in ,src (domain ,x)))
             (iff (in src (domain x))
                  (and (event-p src)
                       (in (edge src dst) (relation-fix x)))))
    :hints(("Goal" :in-theory (enable in-of-domain))))

  (defthm domain-of-union
    (implies (and (relation-p x)
                  (relation-p y))
             (equal (domain (union x y))
                    (union (domain x) (domain y))))
    :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                      pick-a-point-subset-strategy
                                      in-of-domain-rw
                                      in-of-domain-suff-free)))))


(define range ((x relation-p))
  :returns (rng event-set-p)
  :measure (cardinality (relation-fix x))
  :verify-guards nil
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        nil
      (insert (edge->dst (head x))
              (range (tail x)))))
  ///
  (verify-guards range)
  (defretd in-of-range-suff
    (implies (and (in (edge src dst) (relation-fix x))
                  (event-p dst))
             (in dst rng))
    :hints(("Goal" :in-theory (enable in))))

  (defretd in-of-range-suff-free
    (implies (and (in (edge src dst) some-rel)
                  (in (edge src dst) (relation-fix x))
                  (event-p dst))
             (in dst rng))
    :hints(("Goal" :in-theory (enable in-of-range-suff))))

  (defret in-src-of-range
    (implies (in pair (relation-fix x))
             (in (edge->dst pair) rng))
    :hints(("Goal" :in-theory (enable in)))))

(define range-witness ((dst event-p) (x relation-p))
  :returns (src event-p)
  :measure (cardinality (relation-fix x))
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        (some-event)
      (if (event-equiv dst (edge->dst (head x)))
          (edge->src (head x))
        (range-witness dst (tail x)))))
  ///

  (defret range-witness-witnesses
    (implies (in (edge src1 dst) (relation-fix x))
             (in (edge src dst) (relation-fix x)))
    :hints(("Goal" :in-theory (enable in))))
  
  (defretd in-of-range-necc
    (implies (not (in (edge src dst) (relation-fix x)))
             (not (in dst (range x))))
    :hints(("Goal" :in-theory (enable range in))))

  (defretd in-of-range
    (iff (in dst (range x))
         (and (event-p dst)
              (in (edge src dst) (relation-fix x))))
    :hints(("Goal" :in-theory (enable in-of-range-necc
                                      in-of-range-suff
                                      range)))
    :otf-flg t)

  (defretd in-of-range-rw
    (implies (acl2::rewriting-negative-literal `(in ,dst (range ,x)))
             (iff (in dst (range x))
                  (and (event-p dst)
                       (in (edge src dst) (relation-fix x)))))
    :hints(("Goal" :in-theory (enable in-of-range))))

  (defthm range-of-union
    (implies (and (relation-p x)
                  (relation-p y))
             (equal (range (union x y))
                    (union (range x) (range y))))
    :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                      pick-a-point-subset-strategy
                                      in-of-range-rw
                                      in-of-range-suff-free)))))



(local
 (defsection transitive-closure-termination-argument

   (local (in-theory (enable pick-a-point-subset-strategy
                             set::double-containment-no-backchain-limit)))

   (defthm domain-of-relcompose
     (subset (domain (relcompose x y))
             (domain x))
     :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                       in-of-relcompose
                                       in-of-domain-rw
                                       in-of-domain-suff))))

   (defthm range-of-relcompose
     (subset (range (relcompose x y))
             (range y))
     :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                       in-of-relcompose
                                       in-of-range-rw
                                       in-of-range-suff))))

   (defthm subset-of-relprod
     (implies (relation-p x)
              (subset x (relprod (union (domain x) (range x))
                                   (union (domain x) (range x)))))
     :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                       relation-p-implies-not-in-when-not-edge
                                       in-of-relprod))))

   (defthm cardinality-limited-by-relprod
     (<= (cardinality (relation-fix x))
         (cardinality (relprod (union (domain x) (range x))
                                 (union (domain x) (range x)))))
     :hints (("goal" :use ((:instance subset-of-relprod
                            (x (relation-fix x))))
              :in-theory (disable subset-of-relprod)))
     :rule-classes :linear)

   (defthm cardinality-of-union-increasing
     (implies (not (subset y x))
              (< (cardinality x)
                 (cardinality (union x y))))
     :hints (("goal" :use ((:instance set::proper-subset-cardinality
                            (x x) (y (union x y))))
              :in-theory (e/d (set::subset-in)
                              (set::proper-subset-cardinality))))
     :rule-classes :linear)

   (defthm union-of-subset
     (implies (subset x y)
              (equal (union y x) (sfix y)))
     :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                       set::subset-in
                                       set::double-containment-no-backchain-limit))))


   
   ;; (in-theory (disable acl2::commutativity-2-of-append-under-set-equiv
   ;;                     acl2::commutativity-of-append-under-set-equiv
   ;;                     set::expand-cardinality-of-union))
  
   ;; (defthm append-under-set-equiv-when-subsetp
   ;;   (implies (subsetp-equal y x)
   ;;            (acl2::set-equiv (append x y) x)))

   ;; (defthm append-under-set-equiv-when-subsetp-2
   ;;   (implies (subsetp-equal y x)
   ;;            (acl2::set-equiv (append x y z) (append x z)))
   ;;   :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw))))
   ))



(define relplus ((x relation-p))
  :measure (- (cardinality (relprod
                            (union (domain x) (range x))
                            (union (domain x) (range x))))
              (cardinality (relation-fix x)))
  :returns (closure relation-p)
  :hints(("Goal" :in-theory (disable set::expand-cardinality-of-union)))
  (b* ((comp (relcompose x x))
       (x (relation-fix x))
       ((when (subset comp x))
        x))
    (relplus (union x comp)))
  ///

  (defret relplus-is-superset
    (subset (relation-fix x) (relplus x))
    :hints(("Goal" :in-theory (enable set::subset-transitive))))

  (defret relplus-is-closed
    (subset (relcompose closure closure) closure)))


(fty::deflist event-list :elt-type event :true-listp t)

(define relation-path-p ((path event-list-p)
                         (x relation-p))
  (if (atom (cdr path))
      nil
    (and (in (edge (car path) (cadr path))
             (relation-fix x))
         (or (atom (cddr path))
             (relation-path-p (cdr path) x))))
  ///
  (defthm relation-path-p-of-relcompose
    (implies (and (relation-path-p a x)
                  (relation-path-p b x)
                  (event-equiv (car b)
                               (car (last a))))
             (relation-path-p (append a (cdr b)) x)))

  (defthmd relation-path-p-when-subset
    (implies (and (subset (relation-fix x)
                          (relation-fix y))
                  (relation-path-p path x))
             (relation-path-p path y))
    :hints(("Goal" :in-theory (enable relation-path-p
                                      set::subset-in))))

  (local (in-theory (enable event-list-fix))))



(define transitive-path-aux ((path event-list-p)
                             (x relation-p))
  :guard (relation-path-p path (union (relation-fix x) (relcompose x x)))
  :guard-hints (("goal" :in-theory (enable relation-path-p)))
  :returns (new-path event-list-p)
  :ruler-extenders :lambdas
  ;; If path is a path in (union (relation-fix x) (relcompose x x)),
  ;; we derive a path in x.
  (b* ((first (car path))
       (second (cadr path))
       (rest (if (consp (cddr path))
                 (transitive-path-aux (cdr path) x)
               (list (event-fix second))))
       ((when (in (edge first second) (relation-fix x)))
        (cons (event-fix first) rest)))
    (cons (event-fix first)
          (cons (relcompose-midpoint first second x x)
                rest)))
  ///
  (defret first-of-<fn>
    (equal (car new-path)
           (event-fix (car path))))

  (defret last-of-<fn>
    ;; (implies (relation-path-p path (union (relation-fix x) (relcompose x x)))
    (implies (consp (cdr path))
             (equal (car (last new-path))
                    (event-fix (car (last path)))))
    :hints(("Goal" :in-theory (disable (:d transitive-path-aux))
            :induct <call>
            :expand (<call>
                     (:free (y) (relation-path-p path y))))))

  (defret consp-cdr-of-<fn>
    (consp (cdr new-path)))


  (defret relation-path-p-of-<fn>
    (implies (relation-path-p path (union (relation-fix x) (relcompose x x)))
             (relation-path-p new-path x))
    :hints(("Goal" :in-theory (disable (:d transitive-path-aux))
            :induct <call>
            :expand (<call>
                     (:free (y) (relation-path-p path y))
                     (:free (a b) (relation-path-p (cons a b) x))))
           (and stable-under-simplificationp
                '(:in-theory (enable in-of-relcompose-rw)))))

  (defret len-of-<fn>
    (<= 2 (len new-path))
    :rule-classes :linear)

  (local (in-theory (enable event-list-fix))))
       


(define transitive-path ((src event-p) (dst event-p)
                         (x relation-p))
  :guard (in (edge src dst) (relplus x))
  :returns (path event-list-p)
  :measure (- (cardinality (relprod
                            (union (domain x) (range x))
                            (union (domain x) (range x))))
              (cardinality (relation-fix x)))
  :hints(("Goal" :in-theory (disable set::expand-cardinality-of-union)))
  :verify-guards nil
  (b* ((comp (relcompose x x))
       (x (relation-fix x))
       ((when (subset comp x))
        (list (event-fix src) (event-fix dst))))
    (transitive-path-aux (transitive-path src dst (union x comp)) x))
  ///
  (defret first-of-<fn>
    (equal (car path)
           (event-fix src)))

  (defret transitive-path-correct
    ;; This (along with the first- and last- properties of transitive-path)
    ;; form half of the correctness statement for relplus: If (src,
    ;; dst) are in (relplus x), then there is a path in x from src
    ;; to dst.
    (implies (in (edge src dst) (relplus x))
             (relation-path-p path x))
    :hints(("Goal" :in-theory (enable relplus
                                      relation-path-p))))
  
  (defret consp-cdr-of-<fn>
    (consp (cdr path)))
  
  (defret last-of-<fn>
    ;; (implies (in (edge src dst) (relplus x))
    (equal (car (last path))
           (event-fix dst))
    :hints(("Goal" :in-theory (enable relplus))))
  
  (verify-guards transitive-path
    :hints (("goal" :expand ((relplus x)))))

  (defret len-of-<fn>
    (<= 2 (len path))
    :rule-classes :linear))
  


(defthmd transitive-when-closed-under-self-composition
  (implies (and (relation-path-p path x)
                (subset (relcompose x x) (relation-fix x)))
           (in (edge (car path)
                     (car (last path)))
               (relation-fix x)))
  :hints(("Goal" :induct (relation-path-p path x)
          :in-theory (enable relation-path-p
                             set::subset-in))
         (and stable-under-simplificationp
              '(:use ((:instance in-of-relcompose-suff
                       (x x) (y x)
                       (pair (edge (car path) (caddr path)))
                       (mid (cadr path)))
                      (:instance in-of-relcompose-suff
                       (x x) (y x)
                       (pair (edge (car path) (car (last (cdr path)))))
                       (mid (cadr path))))))))

(defthm in-relplus-when-path
  ;; The other half of the correctness of relplus: If there is a
  ;; path from a to b in x, then (a, b) are in the transitive closure of x.
  (implies (relation-path-p path x)
           (in (edge (car path) (car (last path)))
               (relplus x)))
  :hints(("Goal" :use ((:instance transitive-when-closed-under-self-composition
                        (x (relplus x)))
                       (:instance relation-path-p-when-subset
                        (x x) (y (relplus x))))
          :in-theory (e/d (relplus-is-superset)
                          (relation-path-p-when-subset)))))
                
             
(defsection relplus-correctness
  (defun-sk exists-path (src dst x)
    (exists path
            (and (relation-path-p path x)
                 (event-equiv src (car path))
                 (event-equiv dst (car (last path))))))

  (in-theory (Disable exists-path))

  (fty::deffixcong event-equiv iff (exists-path src dst x) src
    :hints ((and stable-under-simplificationp
                 (b* ((lit (assoc 'not clause)))
                   `(:expand (,(cadr lit)))))))
  (fty::deffixcong event-equiv iff (exists-path src dst x) dst
    :hints ((and stable-under-simplificationp
                 (b* ((lit (assoc 'not clause)))
                   `(:expand (,(cadr lit)))))))

  (defthmd relplus-correct
    (iff (in pair (relplus x))
         (and (edge-p pair)
              (exists-path (edge->src pair)
                           (edge->dst pair)
                           x)))
    :hints ((acl2::use-termhint
             (b* (((edge pair)))
               (if (in pair (relplus x))
                   `(:computed-hint-replacement
                     ((and stable-under-simplificationp
                           '(:cases ((edge-p pair))))
                      (and stable-under-simplificationp
                           '(:in-theory (enable relation-p-implies-not-in-when-not-edge))))
                     :use ((:instance exists-path-suff
                            (path ,(acl2::hq (transitive-path pair.src pair.dst
                                                              x)))
                            (src ,(acl2::hq pair.src)) (dst ,(acl2::hq pair.dst))))
                     :in-theory (e/d ()
                                     (exists-path-suff)))
                 `(:in-theory (e/d (exists-path)
                                   (in-relplus-when-path))
                   :use ((:instance in-relplus-when-path
                          (path (exists-path-witness
                                 (edge->src pair)
                                 (edge->dst pair) x)))))))))
    :otf-flg t)

  
  (defthm transitive-path-when-exists-path
    (implies (exists-path src dst x)
             (let ((path (transitive-path src dst x)))
               (relation-path-p path x)))
    :hints(("Goal" :in-theory (enable relplus-correct)))))


(define relstar ((r relation-p))
  :returns (closure relation-p)
  (union (relidentity (universe))
         (relplus r)))




(define test-irreflexive ((x relation-p))
  :measure (cardinality (relation-fix x))
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        t
      (and (b* (((edge x1) (head x)))
             (not (equal x1.src x1.dst)))
           (test-irreflexive (tail x)))))
  ///
  (defthm test-irreflexive-necc
    (implies (in (edge evt evt) (relation-fix x))
             (not (test-irreflexive x)))))

(define test-irreflexive-badguy ((x relation-p))
  :measure (cardinality (relation-fix x))
  :returns (evt event-p)
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        (some-event)
      (b* (((edge x1) (head x)))
        (if (equal x1.src x1.dst)
            x1.src
          (test-irreflexive-badguy (tail x))))))
  ///
  (local (defthm edge-when-from-equal-to
           (b* (((edge pair)))
             (implies (equal pair.src pair.dst)
                      (equal (edge pair.src pair.src)
                             (edge-fix pair))))))
  
  (defret test-irreflexive-by-badguy
    (implies (not (in (edge evt evt) (relation-fix x)))
             (test-irreflexive x))
    :hints(("Goal" :in-theory (enable test-irreflexive in))))

  
  (defret self-pair-exists-when-not-test-irreflexive
    (implies (not (test-irreflexive x))
             (in (edge evt evt) (relation-fix x)))
    :hints(("Goal" :in-theory (enable test-irreflexive)))))


(define test-acyclic ((x relation-p))
  (test-irreflexive (relplus x)))


(define relinverse ((x relation-p))
  :returns (inv relation-p)
  :measure (cardinality (relation-fix x))
  :verify-guards nil
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        nil
      (insert (b* (((edge x1) (head x)))
                (edge x1.dst x1.src))
              (relinverse (tail x)))))
  ///
  (verify-guards relinverse)
  (defret in-of-relinverse
    (iff (in pair inv)
         (and (edge-p pair)
              (in (edge (edge->dst pair) (edge->src pair)) (relation-fix x))))))


(define emptyset () nil)

(define singleton ((x event-p))
  :returns (s event-set-p)
  (insert (event-fix x) nil)
  ///
  (defret in-of-singleton
    (iff (in e (singleton x))
         (equal e (event-fix x)))))

(define setunion ((x event-set-p) (y event-set-p))
  :returns (union event-set-p)
  (union (event-set-fix x) (event-set-fix y))
  ///
  (defret in-of-setunion
    (iff (in e union)
         (or (in e (event-set-fix x))
             (in e (event-set-fix y))))))

(define setintersect ((x event-set-p) (y event-set-p))
  :returns (intersect event-set-p)
  (intersect (event-set-fix x) (event-set-fix y))
  ///
  (defret in-of-setintersect
    (iff (in e intersect)
         (and (in e (event-set-fix x))
              (in e (event-set-fix y))))))

(define relunion ((r1 relation-p) (r2 relation-p))
  :returns (union relation-p)
  (union (relation-fix r1) (relation-fix r2))
  ///
  (defret in-of-<fn>
    (iff (in pair union)
         (or (in pair (relation-fix r1))
             (in pair (relation-fix r2))))))

(define relintersect ((r1 relation-p) (r2 relation-p))
  :returns (intersect relation-p)
  (intersect (relation-fix r1) (relation-fix r2))
  ///
  (defret in-of-<fn>
    (iff (in pair intersect)
         (and (in pair (relation-fix r1))
              (in pair (relation-fix r2))))))


(define relstar-bounded ((n natp) (x relation-p))
  :returns (star relation-p)
  :verify-guards nil
  (if (zp n)
      (relidentity (universe))
    (relunion (relidentity (universe))
              (relcompose x (relstar-bounded (1- n) x))))
  ///
  (verify-guards relstar-bounded))

(define pred-false ()
  :enabled t
  nil)

(define pred-true ()
  :enabled t
  t)

(define pred-nonempty ((s event-set-p))
  :enabled t
  (not (emptyp (event-set-fix s))))

(define pred-equal ((e1 event-p) (e2 event-p))
  :enabled t
  (event-equiv e1 e2))

(define pred-in-set ((e event-p) (s event-set-p))
  :enabled t
  (in (event-fix e) (event-set-fix s)))

(define pred-in-rel ((e1 event-p) (e2 event-p) (r relation-p))
  :enabled t
  (in (edge e1 e2) (relation-fix r)))


(define base-set-p (x)
  (declare (ignore x))
  :enabled t
  t)

(define base-rel-p (x)
  (declare (ignore x))
  :enabled t
  t)

(define not-singleton-set-p (x)
  (declare (ignore x))
  :enabled t
  t)

(define mentioned-event-p (e)
  (declare (ignore e))
  :enabled t
  t)

(acl2::def-ruleset! tac-functions
  '(emptyset singleton setunion setintersect
             setimage setimage-witness
             setpreimage setpreimage-witness
             relidentity relunion relintersect
             relcompose relcompose-midpoint
             relstar relstar-bounded relplus
             relinverse relprod
             pred-false pred-true pred-nonempty pred-equal pred-in-set pred-in-rel
             base-set-p base-rel-p not-singleton-set-p mentioned-event-p))

