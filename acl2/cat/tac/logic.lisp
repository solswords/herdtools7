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


(defprod edge
  ((src) (dst))
  :layout :list)

(fty::defset relation :elt-type edge)

(encapsulate
  (((universe) => * :guard t :formals ()))

  (local (defun universe () nil))
  (defthm setp-of-universe
    (setp (universe))))

(define event-p (x)
  (in x (universe)))

(define event-edge-p ((x edge-p))
  (b* (((edge x)))
    (and (event-p x.src)
         (event-p x.dst)))
  ///
  (defthm event-edge-p-of-edge
    (iff (event-edge-p (edge src dst))
         (and (event-p src) (event-p dst))))

  (defthm event-p-of-edge->src-when-event-edge-p
    (implies (event-edge-p x)
             (event-p (edge->src x))))

  (defthm event-p-of-edge->dst-when-event-edge-p
    (implies (event-edge-p x)
             (event-p (edge->dst x)))))

(local (defthm cardinality-of-tail
         (implies (not (emptyp x))
                  (equal (cardinality (tail x))
                         (- (cardinality x) 1)))
         :hints (("goal" :expand ((cardinality x))))))


(define event-set-p ((x setp))
  :measure (cardinality x)
  (if (emptyp x)
      t
    (and (event-p (head x))
         (event-set-p (tail x))))
  ///
  (defthm event-p-when-in-event-set
    (implies (and (event-set-p x)
                  (in e x))
             (event-p e))
    :hints(("Goal" :in-theory (enable in))))

  (defthm event-p-when-in-event-set-converse
    (implies (and (not (event-p e))
                  (in e x))
             (not (event-set-p x))))

  (defthmd event-set-p-of-universe-subset
    (implies (subset x (universe))
             (event-set-p x))
    :hints(("Goal" :in-theory (enable subset
                                      event-p))))
  
  (defthm event-set-p-of-universe
    (event-set-p (universe))
    :hints(("Goal" :in-theory (enable event-set-p-of-universe-subset))))

  (defthm subset-of-universe-when-event-set-p
    (implies (event-set-p x)
             (subset x (universe)))
    :hints(("Goal" :in-theory (enable subset event-p)))))

(define event-set-badguy ((x setp))
  :measure (cardinality x)
  :returns (badguy)
  :prepwork ((local (in-theory (enable event-set-p))))
  (if (emptyp x)
      nil
    (if (event-p (head x))
        (event-set-badguy (tail x))
      (head x)))
  ///
  (defret <fn>-when-not-event-set-p
    (implies (not (event-set-p x))
             (and (in badguy x)
                  (not (event-p badguy)))))

  (defret event-set-p-by-badguy
    (implies (not (and (in badguy x)
                       (not (event-p badguy))))
             (event-set-p x)))

  (defretd event-set-p-by-badguy-rw
    (implies (acl2::rewriting-positive-literal `(event-set-p ,x))
             (iff (event-set-p x)
                  (not (and (in badguy x)
                            (not (event-p badguy))))))))

(defsection event-set-p-ops
  (local (in-theory (enable event-set-p-by-badguy-rw)))
  
  (defthm event-set-p-of-insert
    (implies (and (event-p e)
                  (event-set-p x))
             (event-set-p (insert e x))))

  (defthm event-set-p-of-union
    (implies (and (event-set-p x)
                  (event-set-p y))
             (event-set-p (union x y))))

  (defthm event-set-p-of-intersect-1
    (implies (event-set-p x)
             (event-set-p (intersect x y))))

  (defthm event-set-p-of-intersect-2
    (implies (event-set-p y)
             (event-set-p (intersect x y)))))



(define event-rel-p ((x relation-p))
  :measure (cardinality (relation-fix x))
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        t
      (and (event-edge-p (head x))
           (event-rel-p (tail x)))))
  ///
  (defthm event-edge-p-when-in-event-rel
    (implies (and (event-rel-p x)
                  (in e (relation-fix x)))
             (event-edge-p e))
    :hints(("Goal" :in-theory (enable in))))

  (defthm event-edge-p-when-in-event-rel-2
    (implies (and (in e x)
                  (relation-p x)
                  (event-rel-p x))
             (event-edge-p e))
    :hints(("Goal" :in-theory (enable in))))

  (defthm event-edge-p-when-in-event-rel-converse
    (implies (and (not (event-edge-p e))
                  (in e (relation-fix x)))
             (not (event-rel-p x)))))

(define event-rel-badguy ((x relation-p))
  :measure (cardinality (relation-fix x))
  :returns (badguy)
  :prepwork ((local (in-theory (enable event-rel-p))))
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        nil
      (if (event-edge-p (head x))
          (event-rel-badguy (tail x))
        (head x))))
  ///
  (defret <fn>-when-not-event-rel-p
    (implies (not (event-rel-p x))
             (and (in badguy (relation-fix x))
                  (not (event-edge-p badguy)))))

  (defret event-rel-p-by-badguy
    (implies (not (and (in badguy (relation-fix x))
                       (not (event-edge-p badguy))))
             (event-rel-p x)))

  (defretd event-rel-p-by-badguy-rw
    (implies (acl2::rewriting-positive-literal `(event-rel-p ,x))
             (iff (event-rel-p x)
                  (not (and (in badguy (relation-fix x))
                            (not (event-edge-p badguy))))))))


(defsection event-rel-p-ops
  (local (in-theory (enable event-rel-p-by-badguy-rw)))
  
  (defthm event-rel-p-of-insert
    (implies (and (edge-p e)
                  (event-edge-p e)
                  (relation-p x)
                  (event-rel-p x))
             (event-rel-p (insert e x))))

  (defthm event-rel-p-of-union
    (implies (and (relation-p x)
                  (relation-p y)
                  (event-rel-p x)
                  (event-rel-p y))
             (event-rel-p (union x y))))

  (defthm event-rel-p-of-intersect-1
    (implies (and (relation-p x)
                  (event-rel-p x))
             (event-rel-p (intersect x y))))

  (defthm event-rel-p-of-intersect-2
    (implies (and (relation-p y)
                  (event-rel-p y))
             (event-rel-p (intersect x y)))))



(define empty-relation ()
  :returns (rel relation-p)
  nil)



(define id-relation ((x setp))
  :returns (rel relation-p)
  :verify-guards nil
  (if (emptyp x)
      nil
    (insert (edge (head x) (head x))
            (id-relation (tail x))))
  ///
  (verify-guards id-relation)
  (defret in-of-<fn>
    (iff (in pair rel)
         (and (edge-p pair)
              (equal (edge->src pair) (edge->dst pair))
              (in (edge->src pair) x))))

  (defret event-rel-p-of-<fn>
    (implies (event-set-p x)
             (event-rel-p rel))))

(define cartesian1 (x
                    (y setp))
  :returns (prod relation-p)
  :measure (cardinality y)
  :verify-guards nil
  (if (emptyp y)
      nil
    (insert (edge x (head y))
            (cartesian1 x (tail y))))
  ///
  (verify-guards cartesian1)
  (defretd in-of-<fn>
    (iff (in pair prod)
         (and (edge-p pair)
              (Equal (edge->src pair) x)
              (in (edge->dst pair) y))))

  (defret event-rel-p-of-<fn>
    (implies (and (event-p x)
                  (event-set-p y))
             (event-rel-p prod))))

(define cartesian ((x setp)
                   (y setp))
  :returns (prod relation-p)
  :verify-guards nil
  (if (emptyp x)
      nil
    (union (cartesian1 (head x) y)
           (cartesian (tail x) y)))
  ///
  (verify-guards cartesian)
  
  (defretd in-of-<fn>
    (iff (in pair prod)
         (and (edge-p pair)
              (in (edge->src pair) x)
              (in (edge->dst pair) y)))
    :hints(("Goal" :in-theory (enable in-of-cartesian1))))

  (defret event-rel-p-of-<fn>
    (implies (and (event-set-p x)
                  (event-set-p y))
             (event-rel-p prod))))


(define image ((s setp) (r relation-p))
  :returns (im setp)
  :measure (cardinality (relation-fix r))
  :verify-guards nil
  (b* ((r (relation-fix r)))
    (b* (((when (emptyp r)) nil)
         ((edge x) (head r))
         (rest (image s (tail r))))
      (if (in x.src s)
          (insert x.dst rest)
        rest)))
  ///
  (verify-guards image)
  (defret in-of-image-suff
    (implies (and (in (edge w v) (relation-fix r))
                  (in w s))
             (in v im)))

  (defret in-of-image-suff2
    (implies (and (in w s)
                  (in (edge w v) (relation-fix r)))
             (in v im)))

  (defret event-set-p-of-<fn>
    (implies (event-rel-p r)
             (event-set-p im))))

(define image-witness (v (s setp) (r relation-p))
  :returns (w)
  :measure (cardinality (relation-fix r))
  :verify-guards nil
  (b* ((r (relation-fix r)))
    (b* (((when (emptyp r)) nil)
         ((edge x) (head r))
         ((when (and (equal x.dst v)
                     (in x.src s)))
          x.src))
      (image-witness v s (tail r))))
  ///
  (verify-guards image-witness)
  
  (defret image-witness-when-in-image
    (implies (in v (image s r))
             (and (in w s)
                  (in (edge w v) (relation-fix r))))
    :hints(("Goal" :in-theory (enable image))))

  (defretd in-of-image-rw
    (implies (and (acl2::rewriting-negative-literal `(in ,v (image ,s ,r))))
             (iff (in v (image s r))
                  (and (in w s)
                       (in (edge w v) (relation-fix r)))))
    :hints(("Goal" :in-theory (e/d ()
                                   (image-witness))))))

(define preimage ((s setp) (r relation-p))
  :returns (im setp)
  :measure (cardinality (relation-fix r))
  :verify-guards nil
  (b* ((r (relation-fix r)))
    (b* (((when (emptyp r)) nil)
         ((edge x) (head r))
         (rest (preimage s (tail r))))
      (if (in x.dst s)
          (insert x.src rest)
        rest)))
  ///
  (verify-guards preimage)
  
  (defret in-of-preimage-suff
    (implies (and (in (edge v w) (relation-fix r))
                  (in w s))
             (in v im)))
  
  (defret in-of-preimage-suff2
    (implies (and (in w s)
                  (in (edge v w) (relation-fix r)))
             (in v im)))

  (defret evtset-p-of-preimage
    (implies (event-rel-p r)
             (event-set-p im))))

(define preimage-witness (v (s setp) (r relation-p))
  :returns (w)
  :measure (cardinality (relation-fix r))
  :verify-guards nil
  (b* ((r (relation-fix r)))
    (b* (((when (emptyp r)) nil)
         ((edge x) (head r))
         ((when (and (equal x.src v)
                     (in x.dst s)))
          x.dst))
      (preimage-witness v s (tail r))))
  ///
  (verify-guards preimage-witness)
  
  (defret preimage-witness-when-in-preimage
    (implies (in v (preimage s r))
             (and (in w s)
                  (in (edge v w) (relation-fix r))))
    :hints(("Goal" :in-theory (enable preimage))))

  (defretd in-of-preimage-rw
    (implies (and (acl2::rewriting-negative-literal `(in ,v (preimage ,s ,r))))
             (iff (in v (preimage s r))
                  (and (in w s)
                       (in (edge v w) (relation-fix r)))))
    :hints(("Goal" :in-theory (e/d ()
                                   (preimage-witness))))))




;; For any pair (dst, dst2) in x, includes (src, dst2) in result.
(define compose1 (src dst
                  (x relation-p))
  :returns (compose relation-p)
  :measure (cardinality (relation-fix x))
  :verify-guards nil
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        nil
      (if (equal dst (edge->src (head x)))
          (insert (edge src (edge->dst (head x)))
                  (compose1 src dst (tail x)))
        (compose1 src dst (tail x)))))
  ///
  (verify-guards compose1)
  (defretd in-of-<fn>
    (iff (in pair compose)
         (and (edge-p pair)
              (equal (edge->src pair) src)
              (in (edge dst (edge->dst pair))
                  (relation-fix x))))
    :hints(("Goal" :in-theory (enable in))))

  (defret event-rel-p-of-<fn>
    (implies (and (event-rel-p x)
                  (event-p src))
             (event-rel-p compose))))

(define compose ((x relation-p)
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
             (compose (tail x) y))))
  ///
  (verify-guards compose)
  (defretd in-of-compose-suff
    (implies (and (edge-p pair)
                  (in (edge (edge->src pair) mid) (relation-fix x))
                  (in (edge mid (edge->dst pair)) (relation-fix y)))
             (in pair compose))
    :hints(("Goal" :in-theory (enable in-of-compose1))))

  (defretd in-of-compose-suff2
    (implies (and (edge-p pair)
                  (in (edge mid (edge->dst pair)) (relation-fix y))
                  (in (edge (edge->src pair) mid) (relation-fix x)))
             (in pair compose))
    :hints(("Goal" :in-theory (enable in-of-compose1))))

  (defretd in-of-compose-suff-rw
    (implies (and (in (edge src mid) (relation-fix x))
                  (in (edge mid dst) (relation-fix y)))
             (in (edge src dst) compose))
    :hints(("Goal" :in-theory (enable in-of-compose1))))

  (defretd in-of-compose-suff-rw2
    (implies (and (in (edge mid dst) (relation-fix y))
                  (in (edge src mid) (relation-fix x)))
             (in (edge src dst) compose))
    :hints(("Goal" :in-theory (enable in-of-compose-suff-rw))))
  
  (defret event-rel-p-of-<fn>
    (implies (and (event-rel-p x)
                  (event-rel-p y))
             (event-rel-p compose))))

(local (include-book "std/util/termhints" :dir :system))

(define compose-midpoint (src
                          dst
                          (x relation-p)
                          (y relation-p))
  :returns (mid)
  :measure (cardinality (relation-fix x))
  ;; Witness for compose membership. If (src . dst) are in the composition of x
  ;; and y, then (compose-midpoint src dst x y) produces mid such that (src
  ;; . mid) is in x and (mid . dst) is in y.
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        nil
      (if (and (equal src (edge->src (head x)))
               (in (edge (edge->dst (head x)) dst)
                   (relation-fix y)))
          (edge->dst (head x))
        (compose-midpoint src dst (tail x) y))))
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

  (defret compose-midpoint-when-in-compose
    (implies (in (edge src dst) (compose x y))
             (and (in (edge src mid) (relation-fix x))
                  (in (edge mid dst) (relation-fix y))))
    :hints(("Goal" :in-theory (enable compose
                                      in-of-compose1))))
  
  (defret compose-midpoint-witnesses
    (implies (and (in (edge src mid1) (relation-fix x))
                  (in (edge mid1 dst) (relation-fix y)))
             (and (in (edge src mid) (relation-fix x))
                  (in (edge mid dst) (relation-fix y))))
    :hints(("Goal" :in-theory (enable in))
           (and stable-under-simplificationp
                '(:induct (compose-midpoint src dst x y))))
    :otf-flg t)

  (defretd in-of-compose-necc
    :pre-bind ((src (edge->src pair))
               (dst (edge->dst pair)))
    (implies (not (and (in (edge (edge->src pair) mid) (relation-fix x))
                       (in (edge mid (edge->dst pair)) (relation-fix y))))
             (not (in pair (compose x y))))
    :hints(("Goal" :in-theory (enable compose
                                      in
                                      in-of-compose-suff
                                      in-of-compose1)))
    :otf-flg t)

  (fty::deffixequiv compose-midpoint)
  
  (defretd in-of-compose-implies-fix
    :pre-bind ((pair (edge src dst)))
    (implies (and (in pair (compose x y)))
             (and (in (edge src mid) (relation-fix x))
                  (in (edge mid dst) (relation-fix y))))
    :hints(("Goal" :use ((:instance in-of-compose-necc
                          (pair (edge src dst)))))))
  
  (defretd in-of-compose-implies
    :pre-bind ((pair (edge src dst)))
    (implies (and (in pair (compose x y)))
             (and (implies (relation-p x)
                           (in (edge src mid) x))
                  (implies (relation-p y)
                           (in (edge mid dst) y))))
    :hints(("Goal" :use ((:instance in-of-compose-necc
                          (pair (edge src dst)))))))
                         
  (defretd in-of-compose
    :pre-bind ((src (edge->src pair))
               (dst (edge->dst pair)))
    (iff (in pair (compose x y))
         (and (edge-p pair)
              (in (edge (edge->src pair) mid) (relation-fix x))
              (in (edge mid (edge->dst pair)) (relation-fix y))))
    :hints(("Goal" :in-theory (enable in-of-compose-necc
                                      in-of-compose-suff))))

  (defretd in-of-compose-rw
    :pre-bind ((src (edge->src pair))
               (dst (edge->dst pair)))
    (implies (acl2::rewriting-negative-literal `(in ,pair (compose ,x ,y)))
             (iff (in pair (compose x y))
                  (and (edge-p pair)
                       (in (edge (edge->src pair) mid) (relation-fix x))
                       (in (edge mid (edge->dst pair)) (relation-fix y)))))
    :hints(("Goal" :in-theory (enable in-of-compose))))


  (defthm compose-associative
    (equal (compose (compose x y) z)
           (compose x (compose y z)))
    :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                      set::double-containment-no-backchain-limit))
           (SET::PICK-A-POINT-SUBSET-HINT ID acl2::CLAUSE
                                          WORLD STABLE-UNDER-SIMPLIFICATIONP)
           (and stable-under-simplificationp
                (acl2::use-termhint
                 (b* ((elem set::arbitrary-element)
                      ((edge elem)))
                   (if (in elem (compose (compose x y) z))
                       (b* ((step2 (compose-midpoint elem.src elem.dst (compose x y) z))
                            (step1 (compose-midpoint elem.src step2 x y))
                            (pair1 (edge step1 elem.dst)))
                         `(:use ((:instance acl2::mark-clause-is-true (x '(in elem (compose (compose x y) z))))
                                 (:instance in-of-compose-suff
                                  (x x) (y (compose y z))
                                  (pair ,(acl2::hq elem))
                                  (mid ,(acl2::hq step1)))
                                 (:instance in-of-compose-suff
                                  (x y) (y z)
                                  (pair ,(acl2::hq pair1))
                                  (mid ,(acl2::hq step2))))
                           :in-theory (enable in-of-compose-rw)))
                     (b* ((step1 (compose-midpoint elem.src elem.dst x (compose y z)))
                          (step2 (compose-midpoint step1 elem.dst y z))
                          (pair2 (edge elem.src step2)))
                       `(:use ((:instance acl2::mark-clause-is-true (x '(in elem (compose x (compose y z)))))
                               (:instance in-of-compose-suff
                                (x (compose x y)) (y z)
                                (pair ,(acl2::hq elem))
                                (mid ,(acl2::hq step2)))
                               (:instance in-of-compose-suff
                                (x x) (y y)
                                (pair ,(acl2::hq pair2))
                                (mid ,(acl2::hq step1))))
                         :in-theory (enable in-of-compose-rw))))))))))



(define domain ((x relation-p))
  :returns (dom setp)
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
    (implies (in (edge src dst) (relation-fix x))
             (in src dom))
    :hints(("Goal" :in-theory (enable in))))

  (defretd in-of-domain-suff-free
    (implies (and (in (edge src dst) some-rel)
                  (in (edge src dst) (relation-fix x)))
             (in src dom))
    :hints(("Goal" :in-theory (enable in-of-domain-suff))))

  (defret in-src-of-domain
    (implies (in pair (relation-fix x))
             (in (edge->src pair) dom))
    :hints(("Goal" :in-theory (enable in))))

  (defret event-set-p-of-<fn>
    (implies (event-rel-p x)
             (event-set-p dom))))

(define domain-witness (src (x relation-p))
  :returns (dst)
  :measure (cardinality (relation-fix x))
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        nil
      (if (equal src (edge->src (head x)))
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
         (in (edge src dst) (relation-fix x)))
    :hints(("Goal" :in-theory (enable in-of-domain-necc
                                      in-of-domain-suff
                                      domain)))
    :otf-flg t)

  (defretd in-of-domain-rw
    (implies (acl2::rewriting-negative-literal `(in ,src (domain ,x)))
             (iff (in src (domain x))
                  (in (edge src dst) (relation-fix x))))
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
  :returns (rng setp)
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
    (implies (in (edge src dst) (relation-fix x))
             (in dst rng))
    :hints(("Goal" :in-theory (enable in))))

  (defretd in-of-range-suff-free
    (implies (and (in (edge src dst) some-rel)
                  (in (edge src dst) (relation-fix x)))
             (in dst rng))
    :hints(("Goal" :in-theory (enable in-of-range-suff))))

  (defret in-src-of-range
    (implies (in pair (relation-fix x))
             (in (edge->dst pair) rng))
    :hints(("Goal" :in-theory (enable in))))

  (defret event-set-p-of-<fn>
    (implies (event-rel-p x)
             (event-set-p rng))))

(define range-witness (dst (x relation-p))
  :returns (src)
  :measure (cardinality (relation-fix x))
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        nil
      (if (equal dst (edge->dst (head x)))
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
         (in (edge src dst) (relation-fix x)))
    :hints(("Goal" :in-theory (enable in-of-range-necc
                                      in-of-range-suff
                                      range)))
    :otf-flg t)

  (defretd in-of-range-rw
    (implies (acl2::rewriting-negative-literal `(in ,dst (range ,x)))
             (iff (in dst (range x))
                  (in (edge src dst) (relation-fix x))))
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

   (defthm domain-of-compose
     (subset (domain (compose x y))
             (domain x))
     :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                       in-of-compose
                                       in-of-domain-rw
                                       in-of-domain-suff))))

   (defthm range-of-compose
     (subset (range (compose x y))
             (range y))
     :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                       in-of-compose
                                       in-of-range-rw
                                       in-of-range-suff))))

   (defthm subset-of-cartesian
     (implies (relation-p x)
              (subset x (cartesian (union (domain x) (range x))
                                   (union (domain x) (range x)))))
     :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                       in-of-cartesian))))

   (defthm cardinality-limited-by-cartesian
     (<= (cardinality (relation-fix x))
         (cardinality (cartesian (union (domain x) (range x))
                                 (union (domain x) (range x)))))
     :hints (("goal" :use ((:instance subset-of-cartesian
                            (x (relation-fix x))))
              :in-theory (disable subset-of-cartesian)))
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



(define transitive-closure ((x relation-p))
  :measure (- (cardinality (cartesian
                            (union (domain x) (range x))
                            (union (domain x) (range x))))
              (cardinality (relation-fix x)))
  :returns (closure relation-p)
  :hints(("Goal" :in-theory (disable set::expand-cardinality-of-union)))
  (b* ((comp (compose x x))
       (x (relation-fix x))
       ((when (subset comp x))
        x))
    (transitive-closure (union x comp)))
  ///

  (defret transitive-closure-is-superset
    (subset (relation-fix x) (transitive-closure x))
    :hints(("Goal" :in-theory (enable set::subset-transitive))))

  (defret transitive-closure-is-closed
    (subset (compose closure closure) closure))

  (defret event-rel-p-of-<fn>
    (implies (event-rel-p x)
             (event-rel-p closure))))


(define relation-path-p ((path true-listp)
                         (x relation-p))
  (if (atom (cdr path))
      nil
    (and (in (edge (car path) (cadr path))
             (relation-fix x))
         (or (atom (cddr path))
             (relation-path-p (cdr path) x))))
  ///
  (defthm relation-path-p-of-compose
    (implies (and (relation-path-p a x)
                  (relation-path-p b x)
                  (equal (car b)
                         (car (last a))))
             (relation-path-p (append a (cdr b)) x)))

  (defthmd relation-path-p-when-subset
    (implies (and (subset (relation-fix x)
                          (relation-fix y))
                  (relation-path-p path x))
             (relation-path-p path y))
    :hints(("Goal" :in-theory (enable relation-path-p
                                      set::subset-in)))))



(define transitive-path-aux ((path true-listp)
                             (x relation-p))
  :guard (relation-path-p path (union (relation-fix x) (compose x x)))
  :guard-hints (("goal" :in-theory (enable relation-path-p)))
  :returns (new-path true-listp)
  :ruler-extenders :lambdas
  ;; If path is a path in (union (relation-fix x) (compose x x)),
  ;; we derive a path in x.
  (b* ((first (car path))
       (second (cadr path))
       (rest (if (consp (cddr path))
                 (transitive-path-aux (cdr path) x)
               (list second)))
       ((when (in (edge first second) (relation-fix x)))
        (cons first rest)))
    (cons first
          (cons (compose-midpoint first second x x)
                rest)))
  ///
  (defret first-of-<fn>
    (equal (car new-path)
           (car path)))

  (defret last-of-<fn>
    (implies (relation-path-p path (union (relation-fix x) (compose x x)))
             (equal (car (last new-path))
                    (car (last path))))
    :hints(("Goal" :in-theory (disable (:d transitive-path-aux))
            :induct <call>
            :expand (<call>
                     (:free (y) (relation-path-p path y))))))

  (defret relation-path-p-of-<fn>
    (implies (relation-path-p path (union (relation-fix x) (compose x x)))
             (relation-path-p new-path x))
    :hints(("Goal" :in-theory (disable (:d transitive-path-aux))
            :induct <call>
            :expand (<call>
                     (:free (y) (relation-path-p path y))
                     (:free (a b) (relation-path-p (cons a b) x))))
           (and stable-under-simplificationp
                '(:in-theory (enable in-of-compose-rw)))))

  (defret len-of-<fn>
    (<= 2 (len new-path))
    :rule-classes :linear))
       


(define transitive-path (src dst
                         (x relation-p))
  :guard (in (edge src dst) (transitive-closure x))
  :returns (path true-listp)
  :measure (- (cardinality (cartesian
                            (union (domain x) (range x))
                            (union (domain x) (range x))))
              (cardinality (relation-fix x)))
  :hints(("Goal" :in-theory (disable set::expand-cardinality-of-union)))
  :verify-guards nil
  (b* ((comp (compose x x))
       (x (relation-fix x))
       ((when (subset comp x))
        (list src dst)))
    (transitive-path-aux (transitive-path src dst (union x comp)) x))
  ///
  (defret first-of-<fn>
    (equal (car path)
           src))

  (defret transitive-path-correct
    ;; This (along with the first- and last- properties of transitive-path)
    ;; form half of the correctness statement for transitive-closure: If (src,
    ;; dst) are in (transitive-closure x), then there is a path in x from src
    ;; to dst.
    (implies (in (edge src dst) (transitive-closure x))
             (relation-path-p path x))
    :hints(("Goal" :in-theory (enable transitive-closure
                                      relation-path-p))))
  
  (defret last-of-<fn>
    (implies (in (edge src dst) (transitive-closure x))
             (equal (car (last path)) dst))
    :hints(("Goal" :in-theory (enable transitive-closure))))
  
  (verify-guards transitive-path
    :hints (("goal" :expand ((transitive-closure x)))))

  (defret len-of-<fn>
    (<= 2 (len path))
    :rule-classes :linear))
  


(defthmd transitive-when-closed-under-self-composition
  (implies (and (relation-path-p path x)
                (subset (compose x x) (relation-fix x)))
           (in (edge (car path)
                     (car (last path)))
               (relation-fix x)))
  :hints(("Goal" :induct (relation-path-p path x)
          :in-theory (enable relation-path-p
                             set::subset-in))
         (and stable-under-simplificationp
              '(:use ((:instance in-of-compose-suff
                       (x x) (y x)
                       (pair (edge (car path) (caddr path)))
                       (mid (cadr path)))
                      (:instance in-of-compose-suff
                       (x x) (y x)
                       (pair (edge (car path) (car (last (cdr path)))))
                       (mid (cadr path))))))))

(defthm in-transitive-closure-when-path
  ;; The other half of the correctness of transitive-closure: If there is a
  ;; path from a to b in x, then (a, b) are in the transitive closure of x.
  (implies (relation-path-p path x)
           (in (edge (car path) (car (last path)))
               (transitive-closure x)))
  :hints(("Goal" :use ((:instance transitive-when-closed-under-self-composition
                        (x (transitive-closure x)))
                       (:instance relation-path-p-when-subset
                        (x x) (y (transitive-closure x))))
          :in-theory (e/d (transitive-closure-is-superset)
                          (relation-path-p-when-subset)))))
                
             
(defsection transitive-closure-correctnes
  (defun-sk exists-path (src dst x)
    (exists path
            (and (relation-path-p path x)
                 (equal src (car path))
                 (equal dst (car (last path))))))

  (in-theory (Disable exists-path))

  (defthmd transitive-closure-correct
    (iff (in pair (transitive-closure x))
         (and (edge-p pair)
              (exists-path (edge->src pair)
                           (edge->dst pair)
                           x)))
    :hints ((acl2::use-termhint
             (b* (((edge pair)))
               (if (in pair (transitive-closure x))
                   `(:use ((:instance exists-path-suff
                            (path ,(acl2::hq (transitive-path pair.src pair.dst
                                                              x)))
                            (src ,(acl2::hq pair.src)) (dst ,(acl2::hq pair.dst))))
                     :in-theory (disable exists-path-suff))
                 `(:in-theory (e/d (exists-path)
                                   (in-transitive-closure-when-path))
                   :use ((:instance in-transitive-closure-when-path
                          (path (exists-path-witness
                                 (edge->src pair)
                                 (edge->dst pair) x))))))))))

  
  (defthm transitive-path-when-exists-path
    (implies (exists-path src dst x)
             (let ((path (transitive-path src dst x)))
               (relation-path-p path x)))
    :hints(("Goal" :in-theory (enable transitive-closure-correct)))))


(define reflexive-transitive-closure ((r relation-p))
  :returns (closure relation-p)
  (union (id-relation (universe))
         (transitive-closure r))
  ///
  (defret event-rel-p-of-<fn>
    (implies (event-rel-p r)
             (event-rel-p closure))))




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
  :returns (evt)
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        nil
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
  (test-irreflexive (transitive-closure x)))


(define inverse ((x relation-p))
  :returns (inv relation-p)
  :measure (cardinality (relation-fix x))
  :verify-guards nil
  (b* ((x (relation-fix x)))
    (if (emptyp x)
        nil
      (insert (b* (((edge x1) (head x)))
                (edge x1.dst x1.src))
              (inverse (tail x)))))
  ///
  (verify-guards inverse)
  (defret in-of-inverse
    (iff (in pair inv)
         (and (edge-p pair)
              (in (edge (edge->dst pair) (edge->src pair)) (relation-fix x)))))

  (defret event-rel-p-of-<fn>
    (implies (event-rel-p x)
             (event-rel-p inv))))


(define emptyset () nil)

(define singleton (x)
  :returns (s setp)
  :enabled t
  (insert x nil)
  ///
  (defret event-set-p-of-<fn>
    (implies (event-p x)
             (event-set-p s))))

(define setunion ((x setp) (y setp))
  :returns (union setp)
  :enabled t
  (union x y)
  ///
  (defret event-set-p-of-<fn>
    (implies (and (event-set-p x)
                  (event-set-p y))
             (event-set-p (setunion x y)))))

(define setintersect ((x setp) (y setp))
  :returns (intersect setp)
  :enabled t
  (intersect x y)
  ///
  (defret event-set-p-of-<fn>
    (implies (or (event-set-p x)
                 (event-set-p y))
             (event-set-p (setintersect x y)))))

(define setimage ((s setp) (r relation-p))
  :returns (im setp)
  :enabled t
  (image s r)
  ///
  (defret event-set-p-of-<fn>
    (implies (event-rel-p r)
             (event-set-p im))))

(define setpreimage ((r relation-p) (s setp))
  :returns (im setp)
  :enabled t
  (preimage s r)
  ///
  (defret event-set-p-of-<fn>
    (implies (event-rel-p r)
             (event-set-p im))))


(define relidentity ((s setp))
  :returns (rel relation-p)
  :enabled t
  (id-relation s)
  ///
  (defret event-rel-p-of-<fn>
    (implies (event-set-p s)
             (event-rel-p rel))))

(define relunion ((r1 relation-p) (r2 relation-p))
  :returns (union relation-p)
  :enabled t
  (union (relation-fix r1) (relation-fix r2))
  ///
  (defret event-rel-p-of-<fn>
    (implies (and (event-rel-p r1)
                  (event-rel-p r2))
             (event-rel-p union))))

(define relintersect ((r1 relation-p) (r2 relation-p))
  :returns (intersect relation-p)
  :enabled t
  (intersect (relation-fix r1) (relation-fix r2))
  ///
  (defret event-rel-p-of-<fn>
    (implies (or (event-rel-p r1)
                 (event-rel-p r2))
             (event-rel-p intersect))))

(define relcompose ((r1 relation-p) (r2 relation-p))
  :returns (compose relation-p)
  :enabled t
  (compose r1 r2)
  ///
  (defret event-rel-p-of-<fn>
    (implies (and (event-rel-p r1)
                  (event-rel-p r2))
             (event-rel-p compose))))

(define relstar ((r relation-p))
  :returns (star relation-p)
  :enabled t
  (reflexive-transitive-closure r)
  ///
  (defret event-rel-p-of-<fn>
    (implies (event-rel-p r)
             (event-rel-p star))))


(define relstar-bounded ((n natp) (x relation-p))
  :returns (star relation-p)
  :verify-guards nil
  (if (zp n)
      (relidentity (universe))
    (relunion (relidentity (universe))
              (relcompose x (relstar-bounded (1- n) x))))
  ///
  (verify-guards relstar-bounded)

  (defret event-rel-p-of-<fn>
    (implies (event-rel-p x)
             (event-rel-p star))))


(define relplus ((r relation-p))
  :returns (plus relation-p)
  :enabled t
  (transitive-closure r)
  ///
  (defret event-rel-p-of-<fn>
    (implies (event-rel-p r)
             (event-rel-p plus))))

(define relinverse ((r relation-p))
  :returns (inv relation-p)
  :enabled t
  (inverse r)
  ///
  (defret event-rel-p-of-<fn>
    (implies (event-rel-p r)
             (event-rel-p inv))))

(define relprod ((s1 setp) (s2 setp))
  :returns (prod relation-p)
  :enabled t
  (cartesian s1 s2)
  ///
  (defret event-rel-p-of-<fn>
    (implies (and (event-set-p s1)
                  (event-set-p s2))
             (event-rel-p prod))))


(define pred-false ()
  :enabled t
  nil)

(define pred-true ()
  :enabled t
  t)

(define pred-nonempty ((s setp))
  :enabled t
  (not (emptyp s)))

(define not-pred-nonempty ((s setp))
  :enabled t
  (emptyp s))

(define pred-equal (e1 e2)
  :enabled t
  (equal e1 e2))

(define not-pred-equal (e1 e2)
  :enabled t
  (not (equal e1 e2)))

(define pred-in-set (e (s setp))
  :enabled t
  (in e s))

(define not-pred-in-set (e (s setp))
  :enabled t
  (not (in e s)))

(define pred-in-rel (e1 e2 (r relation-p))
  :enabled t
  (in (edge e1 e2) (relation-fix r)))

(define not-pred-in-rel (e1 e2 (r relation-p))
  :enabled t
  (not (in (edge e1 e2) (relation-fix r))))


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
  '(emptyset singleton setunion setintersect setimage setpreimage relidentity
             relunion relintersect relcompose relstar relstar-bounded relplus relinverse relprod
             pred-false pred-true pred-nonempty pred-equal pred-in-set pred-in-rel
             not-pred-nonempty not-pred-equal not-pred-in-set not-pred-in-rel
             base-set-p base-rel-p not-singleton-set-p mentioned-event-p))

