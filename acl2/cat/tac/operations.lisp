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
             relunion relintersect relcompose relstar relplus relinverse relprod
             pred-false pred-true pred-nonempty pred-equal pred-in-set pred-in-rel
             not-pred-nonempty not-pred-equal not-pred-in-set not-pred-in-rel
             base-set-p base-rel-p not-singleton-set-p mentioned-event-p))



(define relation-path*-p ((path true-listp)
                          (x relation-p))
  ;; Like relation-path-p, but also accepts a length-1 path regardless of the relation.
  (if (atom (cdr path))
      (consp path)
    (and (in (edge (car path) (cadr path))
             (relation-fix x))
         (relation-path*-p (cdr path) x)))
  ///
  (defthm relation-path*-p-of-compose
    (implies (and (relation-path*-p a x)
                  (relation-path*-p b x)
                  (equal (car b)
                         (car (last a))))
             (relation-path*-p (append a (cdr b)) x)))

  (defthmd relation-path*-p-when-subset
    (implies (and (subset (relation-fix x)
                          (relation-fix y))
                  (relation-path*-p path x))
             (relation-path*-p path y))
    :hints(("Goal" :in-theory (enable relation-path*-p
                                      set::subset-in))))

  (defthmd relation-path-p-when-relation-path*-p
    (implies (<= 2 (len path))
             (iff (relation-path*-p path x)
                  (relation-path-p path x)))
    :hints(("Goal" :in-theory (enable relation-path-p))))
  
  (defthm relation-path*-p-implies-in-relstar
    (implies (and (relation-path*-p path x)
                  (event-p (car (last path))))
             (in (edge (car path) (car (last path)))
                 (relstar x)))
    :hints(("Goal" :in-theory (e/d (relstar reflexive-transitive-closure
                                            transitive-closure-correct
                                            event-p)
                                   (relation-path*-p))
            :use relation-path-p-when-relation-path*-p
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:expand ((len path))
                  :in-theory (disable (event-p)))))
    :otf-flg t))




(define relstar-path (src dst (x relation-p))
  :returns (path true-listp)
  :guard (in (edge src dst) (relstar x))
  :guard-hints (("goal" :in-theory (enable reflexive-transitive-closure)))
  (if (equal src dst)
      (list src)
    (transitive-path src dst x))
  ///
  (defthmd in-relstar-implies-relstar-path
    (implies (in (edge src dst) (relstar x))
             (let ((path (relstar-path src dst x)))
               (and (relation-path*-p path x)
                    (equal (car path) src)
                    (equal (car (last path)) dst))))
    :hints(("Goal" :in-theory (e/d (reflexive-transitive-closure
                                    relation-path-p-when-relation-path*-p)
                                   ())
            :expand ((:free (src) (relation-path*-p (list src) x))))
           (and stable-under-simplificationp
                '(:in-theory (enable transitive-closure-correct))))
    :otf-flg t))

(defsection relstar-correctness
  (defun-sk exists-path* (src dst x)
    (exists path
            (and (relation-path*-p path x)
                 (equal src (car path))
                 (equal dst (car (last path))))))

  (in-theory (Disable exists-path*))

  (defthmd relstar-correct
    (implies (event-p (edge->dst pair))
             (iff (in pair (relstar x))
                  (and (edge-p pair)
                       (exists-path* (edge->src pair)
                                     (edge->dst pair)
                                     x))))
    :hints ((acl2::use-termhint
             (b* (((edge pair)))
               (if (in pair (relstar x))
                   `(:use ((:instance exists-path*-suff
                            (path ,(acl2::hq (relstar-path pair.src pair.dst x)))
                            (src ,(acl2::hq pair.src)) (dst ,(acl2::hq pair.dst))))
                     :in-theory (e/d (in-relstar-implies-relstar-path)
                                     (exists-path*-suff)))
                 `(:in-theory (e/d (exists-path*)
                                   (relation-path*-p-implies-in-relstar))
                   :use ((:instance relation-path*-p-implies-in-relstar
                          (path (exists-path*-witness
                                 (edge->src pair)
                                 (edge->dst pair) x))))))))))

  
  (defthm relstar-path-when-exists-path*
    (implies (and (exists-path* src dst x)
                  (event-p dst))
             (let ((path (relstar-path src dst x)))
               (relation-path*-p path x)))
    :hints(("Goal" :in-theory (e/d (relstar-correct
                                    in-relstar-implies-relstar-path)
                                   (relstar))))))
                      
         
  


(defsection exists-bounded-path*
  (defun-sk exists-bounded-path* (src dst len x)
    (exists path
            (and (relation-path*-p path x)
                 (equal src (car path))
                 (equal dst (car (last path)))
                 (<= (len path) (nfix len)))))

  (in-theory (disable exists-bounded-path*))

  (defthmd exists-path-when-exists-bounded-path*
    (implies (exists-bounded-path* src dst len x)
             (exists-path* src dst x))
    :hints(("Goal" :in-theory (enable exists-bounded-path*))))

  (defthmd exists-bounded-path-when-exists-path
    (implies (and (exists-path* src dst x)
                  (<= (len (exists-path*-witness src dst x)) (nfix len)))
             (exists-bounded-path* src dst len x))
    :hints(("Goal" :in-theory (enable exists-path*)))))


(define relstar-bounded ((n natp) (x relation-p))
  :returns (star relation-p)
  :verify-guards nil
  (if (zp n)
      (relidentity (universe))
    (relunion (relidentity (universe))
              (relcompose x (relstar-bounded (1- n) x))))
  ///
  (verify-guards relstar-bounded)

  (local (defun bound-path-ind (n path)
           (if (atom (cdr path))
               n
             (bound-path-ind (1- n) (cdr path)))))
  
  (defret in-relstar-bounded-when-relation-path-p
    (implies (and (relation-path*-p path x)
                  (<= (len path) (+ 1 (nfix n)))
                  (event-p (car (last path))))
             (in (edge (car path) (car (last path))) star))
    :hints(("Goal" :in-theory (enable len (:i relation-path*-p)
                                      in-of-compose-suff-rw
                                      in-of-compose-suff-rw2
                                      event-p)
            :induct (bound-path-ind n path)
            :expand (<call>
                     (relation-path*-p path x)))))

  
  
  (defthm in-relstar-bounded-when-exists-bounded-path*
    (implies (and (exists-bounded-path* (edge->src pair)
                                        (edge->dst pair) (+ 1 (nfix n)) x)
                  (edge-p pair)
                  (event-p (edge->dst pair)))
             (in pair (relstar-bounded n x)))
    :hints (("goal" :in-theory (e/d (exists-bounded-path*)
                                    (in-relstar-bounded-when-relation-path-p))
             :use ((:instance in-relstar-bounded-when-relation-path-p
                    (path (exists-bounded-path*-witness (edge->src pair)
                                        (edge->dst pair) (+ 1 (nfix n)) x))))
             :do-not-induct t)))

  (defret event-rel-p-of-<fn>
    (implies (event-rel-p x)
             (event-rel-p star))))



(define relstar-bounded-path ((src )
                              (dst )
                              (n natp) (x relation-p))
  :returns (path true-listp)
  :guard (in (edge src dst) (relstar-bounded n x))
  :measure (nfix n)
  :guard-hints (("goal" :expand ((relstar-bounded n x))
                 :in-theory (enable in-of-compose-necc)))
  (if (zp n)
      (list dst)
    (if (equal src dst)
        (list dst)
      (let ((closure (relstar-bounded (1- n) x)))
        (cons src
              (relstar-bounded-path (compose-midpoint src dst x closure) dst
                                    (1- n) x)))))
  ///
  (defret relation-path-p-of-<fn>
    (implies (in (edge src dst) (relstar-bounded n x))
             (and (relation-path*-p path x)
                  (equal (car path) src)
                  (equal (car (last path)) dst)))
    :hints(("Goal" :induct <call>
            :in-theory (enable in-of-compose-rw)
            :expand ((:free (a b) (relation-path*-p (cons a b) x))
                     (relstar-bounded n x)))))

  (defret len-of-<fn>
    (<= (len path) (+ 1 (nfix n)))
    :rule-classes :linear))

(defthmd relstar-bounded-correct
  (implies (event-p (edge->dst pair))
           (iff (in pair (relstar-bounded n x))
                (and (edge-p pair)
                     (exists-bounded-path* (edge->src pair)
                                           (edge->dst pair)
                                           (+ 1 (nfix n))
                                           x))))
  :hints (("goal" :use ((:instance exists-bounded-path*-suff
                         (path (relstar-bounded-path
                                (edge->src pair)
                                (edge->dst pair) n x))
                         (src (edge->src pair))
                         (dst (edge->dst pair))
                         (len (+ 1 (nfix n)))))
           :in-theory (disable exists-bounded-path*-suff))))





(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (not (consp x)))))

(define max-relstar-path-length ((rel relation-p) (x relation-p))
  :guard (subset rel (relstar x))
  :returns (max-len natp :rule-classes :type-prescription)
  :measure (acl2-count (relation-fix rel))
  :guard-hints (("goal" :expand ((subset rel (reflexive-transitive-closure x)))))
  (b* ((rel (relation-fix rel)))
    (if (emptyp rel)
        0
      (b* ((pair (head rel)))
        (max (if (in pair (relstar x))
                 (len (relstar-path (edge->src pair)
                                       (edge->dst pair)
                                       x))
               0)
             (max-relstar-path-length (tail rel) x)))))
  ///
  (defret path-length-less-than-<fn>
    (implies (and (in pair (relation-fix rel))
                  (in pair (relstar x)))
             (<= (len (relstar-path (edge->src pair)
                                       (edge->dst pair)
                                       x))
                 max-len))
    :hints (("Goal" :induct <call>
             :expand ((in pair (relation-fix rel)))))
    :rule-classes :linear)

  (defret max-len-when-nonempty
    (implies (and (not (emptyp (relation-fix rel)))
                  (subset (relation-fix rel) (relstar x)))
             (<= 1 max-len))
    :hints(("Goal" :induct <call>
            :in-theory (enable len)
            :expand ((subset (relation-fix rel) (reflexive-transitive-closure x)))))
    :rule-classes :linear))

(define relstar-bound ((x relation-p))
  :returns (bound natp :rule-classes :type-prescription)
  (let* ((closure (relstar x))
         (max-len (max-relstar-path-length closure x)))
    (max 0 (- max-len 1)))
  ///
  (defthmd in-relstar-when-in-relstar-bounded
    (implies (and (in pair (relstar-bounded n x))
                  (event-p (Edge->dst pair)))
             (in pair (relstar x)))
    :hints(("Goal" :in-theory (e/d (relstar-correct
                                      relstar-bounded-correct
                                      exists-path-when-exists-bounded-path*)
                                   (relstar)))))


  
  (defretd in-relstar-bounded-when-in-relstar
    (implies (and (in pair (relstar x))
                  (event-p (edge->dst pair)))
             (in pair (relstar-bounded bound x)))
    :hints(("Goal" :in-theory (e/d ;; relstar-correct
                               (relstar-bounded-correct
                                exists-path-when-exists-bounded-path*
                                in-relstar-implies-relstar-path)
                               (path-length-less-than-max-relstar-path-length
                                relstar))
            :use ((:instance exists-bounded-path*-suff
                   (src (edge->src pair))
                   (dst (edge->dst pair))
                   (len (max-relstar-path-length (relstar x) x))
                   (path (relstar-path (edge->src pair)
                                          (edge->dst pair)
                                          x)))
                  (:instance path-length-less-than-max-relstar-path-length
                   (rel (relstar x)))))))

  (defretd relstar-in-terms-of-bounded
    (implies (event-rel-p x)
             (equal (relstar x)
                    (relstar-bounded bound x)))
    :hints (("goal" :in-theory (e/d (set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-relstar-when-in-relstar-bounded
                                     in-relstar-bounded-when-in-relstar)
                                    (relstar-bound
                                     relstar)))
            (SET::PICK-A-POINT-SUBSET-HINT ID acl2::CLAUSE
                                           WORLD STABLE-UNDER-SIMPLIFICATIONP))))



(include-book "centaur/meta/fixed-evaluator" :dir :system)

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
   (not-pred-nonempty s)
   (not-pred-equal e1 e2)
   (not-pred-in-set e s)
   (not-pred-in-rel e1 e2 r)
   (base-set-p x)
   (base-rel-p x)
   (not-singleton-set-p x)
   (mentioned-event-p x)
   
   (event-p x)
   (setp x)
   (event-set-p x)
   (relation-p x)
   (event-rel-p x)

   (if a b c)
   (implies a b)
   (equal a b)
   (iff a b)
   (not x)
   (return-last x y z)

   (typespec-check ts x))
  :namedp t)

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
    (:set (and (setp val) (event-set-p val)))
    (:count (natp val))
    (:rel   (and (relation-p val) (event-rel-p val)))
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

(define tac-typed-vallist-p (vals (types tac-typelist-p))
  (if (atom types)
      t
    (and (consp vals)
         (tac-typed-val-p (car vals) (car types))
         (tac-typed-vallist-p (cdr vals) (cdr types)))))

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

  (defthm tac-typed-env-p-implies-lookup-event-rel-p
    (implies (and (tac-typed-env-p env ctx)
                  (equal (cdr (assoc-equal v (type-ctx-fix ctx))) :rel)
                  (pseudo-var-p v))
             (and  (relation-p (cdr (assoc-eq v env)))
                   (event-rel-p (cdr (assoc-eq v env)))))
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
    (not-pred-nonempty :set)
    (pred-equal :event :event)
    (not-pred-equal :event :event)
    (pred-in-set :event :set)
    (not-pred-in-set :event :set)
    (pred-in-rel :event :event :rel)
    (not-pred-in-rel :event :event :rel)))

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
    (not-pred-nonempty . :pred)
    (pred-equal . :pred)
    (not-pred-equal . :pred)
    (pred-in-set . :pred)
    (not-pred-in-set . :pred)
    (pred-in-rel . :pred)
    (not-pred-in-rel . :pred)))

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
                           (and (setp (tac-ev x env))
                                (event-set-p (tac-ev x env))))
                  (implies (equal type :rel)
                           (and (relation-p (tac-ev x env))
                                (event-rel-p (tac-ev x env))))
                  (implies (equal type :event)
                           (event-p (tac-ev x env)))))
    :hints (("Goal" :use tac-typed-val-p-when-term-type
             :in-theory (e/d (tac-typed-val-p)
                             (tac-typed-val-p-when-term-type))))
    :fn tac-term-type)

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

  (acl2::defopen tac-term-type-when-emptyset
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'emptyset))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-universe
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'universe))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-singleton
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'singleton))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-setunion
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'setunion))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-setintersect
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'setintersect))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-setimage
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'setimage))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-setpreimage
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'setpreimage))
    :hint (:expand ((tac-term-type x ctx))))

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

  (acl2::defopen tac-term-type-when-relidentity
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relidentity))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-relunion
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relunion))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-relintersect
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relintersect))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-relcompose
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relcompose))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-relstar
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relstar))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-relstar-bounded
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relstar-bounded))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-relplus
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relplus))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-relinverse
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relinverse))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-relprod
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relprod))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-pred-false
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'pred-false))
    :hint (:expand ((tac-term-type x ctx))))
  
  (acl2::defopen tac-term-type-when-pred-true
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'pred-true))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-pred-nonempty
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'pred-nonempty))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-not-pred-nonempty
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'not-pred-nonempty))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-pred-equal
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'pred-equal))
    :hint (:expand ((tac-term-type x ctx))))
  (acl2::defopen tac-term-type-when-not-pred-equal
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'not-pred-equal))
    :hint (:expand ((tac-term-type x ctx))))
  (acl2::defopen tac-term-type-when-pred-in-set
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'pred-in-set))
    :hint (:expand ((tac-term-type x ctx))))
  (acl2::defopen tac-term-type-when-not-pred-in-set
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'not-pred-in-set))
    :hint (:expand ((tac-term-type x ctx))))
  (acl2::defopen tac-term-type-when-pred-in-rel
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'pred-in-rel))
    :hint (:expand ((tac-term-type x ctx))))
  (acl2::defopen tac-term-type-when-not-pred-in-rel
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'not-pred-in-rel))
    :hint (:expand ((tac-term-type x ctx))))

  (acl2::defopen tac-term-type-when-bad-fncall
    (tac-term-type x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (not (member-equal (acl2::pseudo-term-fncall->fn x)
                                 '(emptyset universe singleton setunion setintersect
                                            setimage setpreimage
                                            relidentity relunion relintersect relcompose
                                            relstar relstar-bounded relplus relinverse relprod
                                            pred-false pred-true
                                            pred-nonempty not-pred-nonempty
                                            pred-equal not-pred-equal
                                            pred-in-set not-pred-in-set
                                            pred-in-rel not-pred-in-rel))))
    :hint (:expand ((tac-term-type x ctx))
           :in-theory (enable member-equal
                              tac-function-return-type)))

  (fty::deffixequiv-mutual tac-term-type))
               

(acl2::def-ruleset! tac-rewrites nil)

(defthm union-of-subset2
  (implies (subset y x)
           (equal (union y x) (sfix x)))
  :hints(("Goal" :in-theory (enable set::union-with-subset-left))))

(defthm intersect-with-subset
  (implies (subset y x)
           (equal (intersect y x) (sfix y)))
  :hints(("Goal" :in-theory (enable set::intersect-with-subset-left))))

(defthm intersect-with-subset2
  (implies (subset y x)
           (equal (intersect x y) (sfix y)))
  :hints(("Goal" :in-theory (enable set::intersect-with-subset-right))))

(defthm image-of-nil
  (equal (image nil x)
         nil)
  :hints(("Goal" :in-theory (enable image))))

(defthm image-of-id-relation
  (equal (image x (id-relation y))
         (intersect x y))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-image-rw
                                    in-of-image-suff)))
  :otf-flg t)

(defthm in-image-of-singleton
  (iff (in x (image (insert y nil) z))
       (in (edge y x) (relation-fix z)))
  :hints(("Goal" :in-theory (enable in-of-image-rw
                                    in-of-image-suff))))

(defthm in-universe-when-event-p
  (implies (event-p x)
           (in x (universe)))
  :hints(("Goal" :in-theory (enable event-p))))

(defthm image-of-singleton-in-universe
  (implies (event-p e)
           (equal (image (insert e nil) (cartesian (universe) (universe)))
                  (universe)))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-image-rw
                                    in-of-image-suff
                                    in-of-cartesian))
         (set::pick-a-point-subset-hint id clause world stable-under-simplificationp)
         (and stable-under-simplificationp
              '(:use ((:instance in-of-image-suff
                       (s (insert e nil))
                       (r (cartesian (universe) (universe)))
                       (w e)
                       (v set::arbitrary-element)))))))

(defthm image-of-union
  (equal (image (union x y) z)
         (union (image x z) (image y z)))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-image-rw
                                    in-of-image-suff)))
  :otf-flg t)

(defthm image-of-compose
  (equal (image x (compose y z))
         (image (image x y) z))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-image-rw
                                     in-of-compose-rw
                                     in-of-compose-suff))
          (set::pick-a-point-subset-hint id clause world stable-under-simplificationp)
          (and stable-under-simplificationp
               '(:use ((:instance in-of-image-suff
                        (v set::arbitrary-element)
                        (s x) (r (compose y z))
                        (w (image-witness (image-witness
                                           set::arbitrary-element
                                           (image x y) z)
                                          x y)))
                       (:instance in-of-compose-suff
                        (pair (edge (image-witness (image-witness
                                                    set::arbitrary-element
                                                    (image x y) z)
                                                   x y)
                                    set::arbitrary-element))
                        (x y) (y z)
                        (mid (image-witness set::arbitrary-element (image x y) z))))))))

(defthm image-of-inverse
  (equal (image x (inverse y))
         (preimage x y))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-image-rw
                                     in-of-preimage-rw
                                     in-of-image-suff
                                     in-of-preimage-suff
                                     in-of-inverse))))


(defthm image-of-singleton-intersect
  (implies (and (relation-p y) (relation-p z))
           (equal (image (insert x nil) (intersect y z))
                  (intersect (image (insert x nil) y) (image (insert x nil) z))))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-image-rw))))

(defthm preimage-of-nil
  (equal (preimage nil x)
         nil)
  :hints(("Goal" :in-theory (enable preimage))))

(defthm preimage-of-id-relation
  (equal (preimage x (id-relation y))
         (intersect y x))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-preimage-rw
                                    in-of-preimage-suff)))
  :otf-flg t)

(defthm preimage-of-singleton-in-universe
  (implies (event-p e)
           (equal (preimage (insert e nil) (cartesian (universe) (universe)))
                  (universe)))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-image-rw
                                    in-of-preimage-suff
                                    in-of-cartesian))
         (set::pick-a-point-subset-hint id clause world stable-under-simplificationp)
         (and stable-under-simplificationp
              '(:use ((:instance in-of-preimage-suff
                       (s (insert e nil))
                       (r (cartesian (universe) (universe)))
                       (w e)
                       (v set::arbitrary-element)))))))

(defthm preimage-of-union
  (equal (preimage (union x y) z)
         (union (preimage x z) (preimage y z)))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-preimage-rw
                                    in-of-preimage-suff)))
  :otf-flg t)

(defthm preimage-of-compose
  (equal (preimage x (compose z y))
         (preimage (preimage x y) z))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-preimage-rw
                                     in-of-compose-rw
                                     in-of-compose-suff))
          (set::pick-a-point-subset-hint id clause world stable-under-simplificationp)
          (and stable-under-simplificationp
               '(:use ((:instance in-of-preimage-suff
                        (v set::arbitrary-element)
                        (s x) (r (compose z y))
                        (w (preimage-witness (preimage-witness
                                           set::arbitrary-element
                                           (preimage x y) z)
                                          x y)))
                       (:instance in-of-compose-suff
                        (pair (edge set::arbitrary-element
                                    (preimage-witness (preimage-witness
                                                    set::arbitrary-element
                                                    (preimage x y) z)
                                                   x y)))
                        (x z) (y y)
                        (mid (preimage-witness set::arbitrary-element (preimage x y) z))))))))

(defthm preimage-of-inverse
  (equal (preimage x (inverse y))
         (image x y))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-image-rw
                                     in-of-preimage-rw
                                     in-of-image-suff
                                     in-of-preimage-suff
                                     in-of-inverse))))

(defthm in-preimage-of-singleton
  (iff (in x (preimage (insert y nil) z))
       (in (edge x y) (relation-fix z)))
  :hints(("Goal" :in-theory (enable in-of-preimage-rw
                                    in-of-preimage-suff))))

(defthm preimage-of-singleton-intersect
  (implies (and (relation-p y) (relation-p z))
           (equal (preimage (insert x nil) (intersect y z))
                  (intersect (preimage (insert x nil) y) (preimage (insert x nil) z))))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-preimage-rw))))



(defthm id-relation-of-union
  (equal (id-relation (union x y))
         (union (id-relation x) (id-relation y)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-id-relation))))

(defthm id-relation-of-intersect
  (equal (id-relation (intersect x y))
         (intersect (id-relation x) (id-relation y)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-id-relation))))



(defthm inverse-of-union
  (implies (and (relation-p x) (relation-p y))
           (equal (inverse (union x y))
                  (union (inverse x) (inverse y))))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-inverse))))

(defthm inverse-of-intersect
  (implies (and (relation-p x) (relation-p y))
           (equal (inverse (intersect x y))
                  (intersect (inverse x) (inverse y))))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-inverse))))


(defthm compose-singleton-prod-1
  (equal (compose x (cartesian (insert y nil) z))
         (cartesian (preimage (insert y nil) x) z))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-cartesian
                                    in-of-compose-rw
                                    in-of-compose-suff
                                    in-of-preimage-rw
                                    in-of-preimage-suff)))
  :otf-flg t)

(defthm compose-singleton-prod-2
  (equal (compose (cartesian z (insert y nil)) x)
         (cartesian z (image (insert y nil) x)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-cartesian
                                    in-of-compose-rw
                                    in-of-compose-suff2
                                    in-of-image-rw
                                    in-of-image-suff)))
  :otf-flg t)

(defthm compose-singleton-prod-3
  (equal (compose x (cartesian z (insert y nil)))
         (cartesian (preimage z x) (insert y nil)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-cartesian
                                    in-of-compose-rw
                                    in-of-compose-suff
                                    in-of-compose-suff2
                                    in-of-preimage-rw
                                    in-of-preimage-suff
                                    ))))

(defthm compose-singleton-prod-4
  (equal (compose (cartesian (insert y nil) z) x)
         (cartesian (insert y nil) (image z x)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-cartesian
                                    in-of-compose-rw
                                    in-of-compose-suff
                                    in-of-compose-suff2
                                    in-of-image-rw
                                    in-of-image-suff
                                    ))))


(defthm subset-of-universe-rel
  (implies (and (relation-p x)
                (event-rel-p x))
           (subset x (cartesian (universe) (universe))))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    in-of-cartesian)))
  :otf-flg t)


(defthm compose-of-nil
  (equal (compose nil x) nil)
  :hints(("Goal" :in-theory (enable compose))))

(defthm compose-of-nil-2
  (equal (compose x nil) nil)
  :hints(("Goal" :in-theory (enable compose compose1))))

(defthm relation-path-p-of-id-relation
  (implies (not (equal (car path)
                       (car (last path))))
           (not (relation-path-p path (id-relation x))))
  :hints(("Goal" :in-theory (enable relation-path-p))))


(local (defthm relation-path-p-implies-last-in-set
         (implies (not (in (car (last path)) x))
                  (not (relation-path-p path (id-relation x))))
         :hints(("Goal" :in-theory (enable relation-path-p)))))

(defthm exists-path-of-id-relation
  (iff (exists-path src dst (id-relation x))
       (and (equal src dst)
            (in src x)))
  :hints(("Goal" :in-theory (enable ;; exists-path
                                    relation-path-p)
          :use ((:instance exists-path-suff
                 (path (list src dst))
                 (x (id-relation x)))))
         (and stable-under-simplificationp
              '(:in-theory (enable exists-path))))
  :otf-flg t)


(defthm in-edge-when-not-event-p-dst
  (implies (and (event-rel-p x)
                (not (event-p dst)))
           (not (in (edge src dst) (relation-fix x))))
  :hints(("Goal" :in-theory (enable event-rel-p in))))

(defthm relation-path-p-when-not-event-p-dst
  (implies (and (event-rel-p x)
                (not (event-p (car (last path)))))
           (not (relation-path-p path x)))
  :hints(("Goal" :in-theory (enable relation-path-p))))

(defthm exists-path-when-not-event-p-last
  (implies (and (event-rel-p x)
                (not (event-p dst)))
           (not (exists-path src dst x)))
  :hints(("Goal" :in-theory (enable exists-path))))

(local (defthm not-event-p-when-not-in-universe
         (implies (not (in x (universe)))
                  (not (event-p x)))
         :hints(("Goal" :in-theory (enable event-p)))))

(defthm reflexive-transitive-closure-of-id-relation
  (implies (event-set-p s)
           (equal (reflexive-transitive-closure (id-relation s))
                  (id-relation (universe))))
  :hints(("Goal" :in-theory (enable reflexive-transitive-closure
                                    set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    transitive-closure-correct))))


(defthm transitive-closure-of-id-relation
  (implies (event-set-p s)
           (equal (transitive-closure (id-relation s))
                  (id-relation s)))
  :hints(("Goal" :in-theory (enable transitive-closure
                                    set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    transitive-closure-correct))))

(defthm exists-path-of-universe-rel
  (implies (and (event-p src)
                (event-p dst))
           (exists-path src dst (cartesian (universe) (universe))))
  :hints (("goal" :use ((:instance exists-path-suff
                         (path (list src dst))
                         (x (cartesian (universe) (universe)))))
           :in-theory (enable relation-path-p
                              in-of-cartesian))))

(defthm reflexive-transitive-closure-of-universe-rel
  (equal (reflexive-transitive-closure (cartesian (universe) (universe)))
         (cartesian (universe) (universe)))
  :hints(("Goal" :in-theory (enable reflexive-transitive-closure
                                    set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    transitive-closure-correct))))

(defthm transitive-closure-of-universe-rel
  (equal (transitive-closure (cartesian (universe) (universe)))
         (cartesian (universe) (universe)))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    transitive-closure-correct))))

(defthm inverse-of-id-relation
  (equal (inverse (id-relation r))
         (id-relation r))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-inverse))))

(defthm inverse-of-cartesian
  (equal (inverse (cartesian d r))
         (cartesian r d))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-inverse
                                    in-of-cartesian))))


(defthm cartesian-of-nil
  (equal (cartesian nil r) nil)
  :hints(("Goal" :in-theory (enable cartesian))))

(defthm cartesian-of-nil-2
  (equal (cartesian r nil) nil)
  :hints(("Goal" :in-theory (enable cartesian
                                    cartesian1))))


(defthm intersect-cartesian-singleton-1
  (implies (relation-p x)
           (equal (intersect x (cartesian (insert y nil) z))
                  (cartesian (insert y nil) (intersect (image (insert y nil) x) z))))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-cartesian
                                    in-of-image-rw
                                    in-of-image-suff
                                    ))))

(defthm intersect-cartesian-singleton-2
  (implies (relation-p x)
           (equal (intersect x (cartesian z (insert y nil)))
                  (cartesian (intersect (preimage (insert y nil) x) z) (insert y nil))))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-cartesian
                                    in-of-preimage-rw
                                    in-of-preimage-suff
                                    ))))

(defthm intersect-cartesian-singleton-3
  (implies (relation-p x)
           (equal (intersect (cartesian (insert y nil) z) x)
                  (cartesian (insert y nil) (intersect z (image (insert y nil) x)))))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-cartesian
                                    in-of-image-rw
                                    in-of-image-suff
                                    ))))

(defthm intersect-cartesian-singleton-4
  (implies (relation-p x)
           (equal (intersect (cartesian z (insert y nil)) x)
                  (cartesian (intersect z (preimage (insert y nil) x)) (insert y nil))))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-cartesian
                                    in-of-preimage-rw
                                    in-of-preimage-suff
                                    ))))




(defmacro def-tac-rewrite (name &rest args)
  `(progn (defthm ,name . ,args)
          (acl2::add-to-ruleset tac-rewrites ,name)))

;; All these rewrite rules have these properties
;; - If the LHS matches with a well-typed (set-term-p/rel-term-p) term,
;;   then the RHS also is well-typed (in the same sense).
;; - If the LHS matches with a well-typed term, then the hyps are true.


(def-tac-rewrite setunion-of-emptyset
  (implies (setp s)
           (equal (setunion (emptyset) s)
                  s)))

(def-tac-rewrite setunion-of-emptyset-2
  (implies (setp s)
           (equal (setunion s (emptyset))
                  s)))

(def-tac-rewrite setunion-of-universe
  (implies (event-set-p s)
           (equal (setunion (universe) s)
                  (universe))))

(def-tac-rewrite setunion-of-universe-2
  (implies (event-set-p s)
           (equal (setunion s (universe))
                  (universe))))

(def-tac-rewrite setintersect-of-emptyset
  (equal (setintersect (emptyset) s) (emptyset)))

(def-tac-rewrite setintersect-of-emptyset-2
  (equal (setintersect s (emptyset))
         (emptyset)))

(def-tac-rewrite setintersect-of-universe
  (implies (and (setp s)
                (event-set-p s))
           (equal (setintersect (universe) s)
                  s)))

(def-tac-rewrite setintersect-of-universe-2
  (implies (and (setp s)
                (event-set-p s))
           (equal (setintersect s (universe))
                  s)))

(def-tac-rewrite setimage-of-emptyset
  (equal (setimage (emptyset) s) (emptyset)))

(def-tac-rewrite setimage-of-relidentity
  (equal (setimage s1 (relidentity s2))
         (setintersect s1 s2)))

(def-tac-rewrite setimage-of-relcompose
  (equal (setimage x (relcompose y z))
         (setimage (setimage x y) z)))

(def-tac-rewrite setimage-of-relinverse
  (equal (setimage x (relinverse y))
         (setpreimage y x)))

(def-tac-rewrite setimage-of-singleon-universe
  (implies (event-p e)
           (equal (setimage (singleton e) (relprod (universe) (universe)))
                  (universe))))

(def-tac-rewrite setimage-of-singleton-intersect
  (equal (setimage (singleton e) (relintersect x y))
         (setintersect (setimage (singleton e) x)
                       (setimage (singleton e) y))))

(def-tac-rewrite setpreimage-of-emptyset
  (equal (setpreimage s (emptyset))
         (emptyset)))

(def-tac-rewrite setpreimage-of-relidentity
  (equal (setpreimage (relidentity s1) s2)
         (setintersect s1 s2)))

(def-tac-rewrite setunion-of-setimages
  (equal (setunion (setimage s1 r) (setimage s2 r))
         (setimage (setunion s1 s2) r)))

(def-tac-rewrite setunion-of-setpreimages
  (equal (setunion (setpreimage r s1) (setpreimage r s2))
         (setpreimage r (setunion s1 s2))))

(def-tac-rewrite setpreimage-of-relcompose
  (equal (setpreimage (relcompose y z) x)
         (setpreimage y (setpreimage z x))))

(def-tac-rewrite setpreimage-of-relinverse
  (equal (setpreimage (relinverse y) x)
         (setimage x y)))

(def-tac-rewrite setpreimage-of-singleton-intersect
  (equal (setpreimage (relintersect x y) (singleton e))
         (setintersect (setpreimage x (singleton e))
                       (setpreimage y (singleton e)))))

(def-tac-rewrite relunion-of-relidentitys
  (equal (relunion (relidentity s1) (relidentity s2))
         (relidentity (setunion s1 s2))))

(def-tac-rewrite relintersect-of-relidentitys
  (equal (relintersect (relidentity s1) (relidentity s2))
         (relidentity (setintersect s1 s2))))

(def-tac-rewrite relunion-of-empty
  (implies (relation-p r)
           (equal (relunion (relidentity (emptyset)) r)
                  r)))

(def-tac-rewrite relunion-of-empty-2
  (implies (relation-p r)
           (equal (relunion r (relidentity (emptyset)))
                  r)))

(def-tac-rewrite relunion-of-universe
  (implies (event-rel-p r)
           (equal (relunion (relprod (universe) (universe)) r)
                  (relprod (universe) (universe)))))

(def-tac-rewrite relunion-of-universe-2
  (implies (event-rel-p r)
           (equal (relunion r (relprod (universe) (universe)))
                  (relprod (universe) (universe)))))

(def-tac-rewrite relunion-of-relinverses
  (equal (relunion (relinverse x) (relinverse y))
         (relinverse (relunion x y))))

(def-tac-rewrite relintersect-of-relinverses
  (equal (relintersect (relinverse x) (relinverse y))
         (relinverse (relintersect x y)))) ;; or backward?

(def-tac-rewrite relintersect-of-emptyrel
  (equal (relintersect (relidentity (emptyset)) r)
         (relidentity (emptyset))))

(def-tac-rewrite relintersect-of-emptyrel-2
  (equal (relintersect r (relidentity (emptyset)))
         (relidentity (emptyset))))

(def-tac-rewrite relintersect-of-univrel
  (implies (and (relation-p r)
                (event-rel-p r))
           (equal (relintersect (relprod (universe) (universe)) r)
                  r)))

(def-tac-rewrite relintersect-of-univrel-2
  (implies (and (relation-p r)
                (event-rel-p r))
           (equal (relintersect r (relprod (universe) (universe)))
                  r)))

(def-tac-rewrite relprod-of-emptyset
  (equal (relprod (emptyset) s) (relidentity (emptyset))))

(def-tac-rewrite relprod-of-emptyset-2
  (equal (relprod s (emptyset)) (relidentity (emptyset))))

(def-tac-rewrite relcompose-of-emptyrel
  (equal (relcompose (relidentity (emptyset)) r)
         (relidentity (emptyset))))

(def-tac-rewrite relcompose-of-emptyrel-2
  (equal (relcompose r (relidentity (emptyset)))
         (relidentity (emptyset))))

(def-tac-rewrite relstar-of-relidentity
  (implies (event-set-p s)
           (equal (relstar (relidentity s))
                  (relidentity (universe)))))

(def-tac-rewrite relplus-of-relidentity
  (implies (event-set-p s)
           (equal (relplus (relidentity s))
                  (relidentity s))))

(def-tac-rewrite relstar-of-univrel
  (equal (relstar (relprod (universe) (universe)))
         (relprod (universe) (universe))))

(def-tac-rewrite relplus-of-univrel
  (equal (relplus (relprod (universe) (universe)))
         (relprod (universe) (universe))))

(def-tac-rewrite relinverse-of-relidentity
  (equal (relinverse (relidentity r))
         (relidentity r)))

(def-tac-rewrite relinverse-of-relprod
  (equal (relinverse (relprod s1 s2))
         (relprod s2 s1)))



(def-tac-rewrite relcompose-singleton-prod-1
  (equal (relcompose x (relprod (singleton y) z))
         (relprod (setpreimage x (singleton y)) z)))

(def-tac-rewrite relcompose-singleton-prod-2
  (equal (relcompose (relprod z (singleton y)) x)
         (relprod z (setimage (singleton y) x)))
  :otf-flg t)

(def-tac-rewrite relcompose-singleton-prod-3
  (equal (relcompose x (relprod z (singleton y)))
         (relprod (setpreimage x z) (singleton y))))

(def-tac-rewrite relcompose-singleton-prod-4
  (equal (relcompose (relprod (singleton y) z) x)
         (relprod (singleton y) (setimage z x))))

(def-tac-rewrite relintersect-relprod-singleton-1
  (equal (relintersect x (relprod (singleton y) z))
         (relprod (singleton y) (setintersect (setimage (singleton y) x) z))))

(def-tac-rewrite relintersect-relprod-singleton-2
  (equal (relintersect x (relprod z (singleton y)))
         (relprod (setintersect (setpreimage x (singleton y)) z) (singleton y))))

(def-tac-rewrite relintersect-relprod-singleton-3
  (equal (relintersect (relprod (singleton y) z) x)
         (relprod (singleton y) (setintersect z (setimage (singleton y) x)))))

(def-tac-rewrite relintersect-relprod-singleton-4
  (equal (relintersect (relprod z (singleton y)) x)
         (relprod (setintersect z (setpreimage x (singleton y))) (singleton y))))



(include-book "centaur/meta/parse-rewrite" :dir :system)
(include-book "centaur/meta/unify-strict" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "std/util/defconsts" :dir :system)

(define tac-collect-rewrites-aux ((names symbol-listp)
                                  (wrld plist-worldp))
  :returns (mv err rules)
  (if (atom names)
      (mv nil nil)
    (b* ((formula (acl2::meta-extract-formula-w (car names) wrld))
         ((unless (pseudo-termp formula))
          (mv (msg "~x0 not pseudo-termp: ~x1" (car names) formula) nil))
         ((mv err rules1)
          (cmr::parse-rewrites-from-term formula wrld))
         ((when err)
          (mv err nil))
         ((mv err rules2)
          (tac-collect-rewrites-aux (cdr names) wrld))
         ((when err)
          (mv err nil)))
      (mv nil (append rules1 rules2)))))

(encapsulate nil

  (acl2::defconsts *tac-rewrites*
    (b* (((mv err rewrites)
          (tac-collect-rewrites-aux
           (acl2::get-ruleset 'tac-rewrites (w state))
           (w state))))
      (if err
          (er hard? '*tac-rewrites* "~@0" err)
        rewrites)))

  (define tac-rewrites ()
    :returns (rewrites cmr::rewritelist-p)
    *tac-rewrites*
    ///
    (in-theory (disable (tac-rewrites)))))

(defsection tac-rewrite-rhs-preserved
  (defun-sk tac-rewrite-rhs-preserved (rule)
    (forall (x ctx)
            (b* (((cmr::rewrite rule))
                 ((mv unify-ok subst) (cmr::term-unify-strict rule.lhs x nil)))
              (implies (and unify-ok
                            (tac-term-type x ctx))
                       (equal (tac-term-type (cmr::term-subst-strict rule.rhs subst) ctx)
                              (tac-term-type x ctx)))))
    :rewrite :direct)

  (in-theory (disable tac-rewrite-rhs-preserved)))

(define tac-rewrites-rhs-preserved (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (tac-rewrite-rhs-preserved (car rules))
         (tac-rewrites-rhs-preserved (cdr rules))))
  ///
  (local (defthm car-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (car x) a))))
  (local (defthm cdr-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (cdr x) b))))
  
  (defthm tac-rewrites-rhs-preserved-of-tac-rewrites
    (tac-rewrites-rhs-preserved (tac-rewrites))
    :hints (("goal" :expand ((:free (x) (tac-rewrite-rhs-preserved x))
                             (:free (a b) (tac-rewrites-rhs-preserved (cons a b))))
             :in-theory (e/d (cmr::term-subst-strict
                              cmr::termlist-subst-strict
                              cmr::equal-of-pseudo-term-fncall
                              (tac-rewrites))
                             (tac-rewrite-rhs-preserved-necc))))))


(define tac-ev-cube ((x pseudo-term-listp) (env alistp))
  :verify-guards nil
  (if (atom x)
      t
    (and (tac-ev (car x) env)
         (tac-ev-cube (cdr x) env))))

(defsection tac-rewrite-hyps-ok
  (defun-sk tac-rewrite-hyps-ok (rule)
    (forall (x ctx env)
            (b* (((cmr::rewrite rule))
                 ((mv unify-ok subst) (cmr::term-unify-strict rule.lhs x nil)))
              (implies (and unify-ok
                            (tac-term-type x ctx)
                            (tac-typed-env-p env ctx))
                       (tac-ev-cube (cmr::termlist-subst-strict rule.hyps subst) env))))
    :rewrite :direct)

  (in-theory (disable tac-rewrite-hyps-ok)))

(define tac-rewrites-hyps-ok (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (tac-rewrite-hyps-ok (car rules))
         (tac-rewrites-hyps-ok (cdr rules))))
  ///
  (local (defthm car-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (car x) a))))
  (local (defthm cdr-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (cdr x) b))))
  
  (defthm tac-rewrites-hyps-ok-of-tac-rewrites
    (tac-rewrites-hyps-ok (tac-rewrites))
    :hints (("goal" :expand ((:free (x) (tac-rewrite-hyps-ok x))
                             (:free (a b) (tac-rewrites-hyps-ok (cons a b))))
             :in-theory (e/d (cmr::term-subst-strict
                              cmr::termlist-subst-strict
                              cmr::equal-of-pseudo-term-fncall
                              tac-ev-cube
                              (tac-rewrites))
                             (tac-rewrite-hyps-ok-necc))))))




(include-book "std/basic/two-nats-measure" :Dir :system)

(acl2::def-ev-theoremp tac-ev)

(define tac-ev-theorem-rewritesp (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (tac-ev-theoremp (cmr::rewrite-term (car rules)))
         (tac-ev-theorem-rewritesp (cdr rules))))
  ///
  (defthm tac-ev-theorem-rewritesp-of-tac-rewrites
    (tac-ev-theorem-rewritesp (tac-rewrites))
    :hints(("Goal" :in-theory (enable (tac-rewrites))
            :expand ((:Free (a b) (tac-ev-theorem-rewritesp (cons a b))))))))

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

(defthm tac-ev-of-conjoin
  (iff (tac-ev (acl2::conjoin lst) env)
       (tac-ev-cube lst env))
  :hints(("Goal" :in-theory (enable tac-ev-cube))))

(defthm pseudo-term-fncall->fn-of-cons
  (implies (and (atom fn)
                (not (eq fn 'quote)))
           (equal (pseudo-term-fncall->fn (cons fn args))
                  (pseudo-fnsym-fix fn)))
  :hints(("Goal" :in-theory (enable pseudo-term-fncall->fn
                                    pseudo-term-fix
                                    pseudo-term-kind
                                    pseudo-fnsym-fix
                                    pseudo-fnsym-p))))

(defthm pseudo-term-call->args-of-cons
  (implies (and (symbolp fn)
                (not (eq fn 'quote)))
           (equal (pseudo-term-call->args (cons fn args))
                  (pseudo-term-list-fix args)))
  :hints(("Goal" :in-theory (enable pseudo-term-call->args
                                    pseudo-term-kind
                                    pseudo-fnsym-fix
                                    pseudo-fnsym-p)
          :expand ((pseudo-term-fix (cons fn args))))))

(define tac-rewrite-apply-rule ((rule cmr::rewrite-p)
                                (fn pseudo-fnsym-p)
                                (args pseudo-term-listp))
  :returns (mv ok
               (rhs pseudo-termp)
               (subst cmr::pseudo-term-subst-p))
  (b* (((cmr::rewrite rule))
       ((unless (and (eq rule.equiv 'equal)
                     (pseudo-term-case rule.lhs :fncall)))
        (mv nil nil nil))
       ((pseudo-term-fncall rule.lhs))
       ((unless (eq rule.lhs.fn (pseudo-fnsym-fix fn)))
        (mv nil nil nil))
       ((mv ok subst) (cmr::termlist-unify-strict rule.lhs.args args nil))
       ((unless ok)
        (mv nil nil nil)))
    (mv t rule.rhs subst))
  ///
  (local (in-theory (enable tac-ev-of-fncall-args)))
  
  (local (defthm tac-ev-list-equal-of-termlist-subst-strict
           (implies (equal (pseudo-term-list-fix x)
                           (cmr::termlist-subst-strict pat subst))
                    (equal (tac-ev-lst x a)
                           (tac-ev-lst pat (tac-ev-alist subst a))))
           :hints (("goal" :use ((:instance tac-ev-lst-of-pseudo-term-list-fix-x
                                  (x x) (a a)))
                    :in-theory (disable tac-ev-lst-of-pseudo-term-list-fix-x
                                        tac-ev-lst-pseudo-term-list-equiv-congruence-on-x)))))
  
  (defret <fn>-correct
    (implies (and ok
                  (tac-ev-theoremp (cmr::rewrite-term rule))
                  (tac-rewrite-hyps-ok rule)
                  (tac-typed-env-p env ctx)
                  (tac-term-type (pseudo-term-fncall fn args) ctx))
             (equal (tac-ev rhs (tac-ev-alist subst env))
                    (tac-ev (pseudo-term-fncall fn args) env)))
    :hints(("Goal" :in-theory (e/d (cmr::rewrite-term)
                                   (tac-rewrite-hyps-ok-necc))
            :expand ((CMR::TERM-UNIFY-STRICT (CMR::REWRITE->LHS RULE)
                                             (pseudo-term-fncall fn args) NIL))
            :use ((:instance tac-ev-falsify
                   (a (tac-ev-alist (mv-nth 1 (cmr::termlist-unify-strict
                                               (pseudo-term-call->args (cmr::rewrite->lhs rule))
                                               args nil))
                                    env))
                   (x (cmr::rewrite-term rule)))
                  (:instance tac-rewrite-hyps-ok-necc
                   (x (pseudo-term-fncall fn args)))))))

  (defret <fn>-preserves-type
    (implies (and ok
                  (tac-rewrite-rhs-preserved rule)
                  (equal type (tac-term-type (pseudo-term-fncall fn args) ctx))
                  type)
             (equal (tac-term-type (cmr::term-subst-strict rhs subst) ctx)
                    type))
    :hints (("goal" :use ((:instance tac-rewrite-rhs-preserved-necc
                           (x (pseudo-term-fncall fn args))))
            :expand ((CMR::TERM-UNIFY-STRICT (CMR::REWRITE->LHS RULE)
                                             (pseudo-term-fncall fn args) NIL))
             :in-theory (disable tac-rewrite-rhs-preserved-necc)))))
                           

(local (defthm alistp-when-pseudo-term-subst-p
         (implies (cmr::pseudo-term-subst-p x)
                  (alistp x))))

(defines tac-rewrite
  (define tac-rewrite ((clk natp)
                       (x pseudo-termp)
                       (subst cmr::pseudo-term-subst-p))
    :measure (acl2::nat-list-measure (list clk 0 (pseudo-term-count x) 0 0))
    :returns (new-x pseudo-termp)
    :verify-guards nil
    (pseudo-term-case x
      :fncall (b* ((args (tac-rewrite-list clk x.args subst)))
                (tac-rewrite-fncall clk x.fn args))
      :var (cdr (assoc-equal x.name (cmr::pseudo-term-subst-fix subst)))
      :otherwise (cmr::term-subst-strict x subst)))

  (define tac-rewrite-list ((clk natp)
                            (x pseudo-term-listp)
                            (subst cmr::pseudo-term-subst-p))
    :measure (acl2::nat-list-measure (list clk 0 (pseudo-term-list-count x) 0 0))
    :returns (new-x (and (pseudo-term-listp new-x)
                         (Equal (len new-x) (len x))))
    (if (atom x)
        nil
      (cons (tac-rewrite clk (car x) subst)
            (tac-rewrite-list clk (cdr x) subst))))

  (define tac-rewrite-fncall ((clk natp)
                              (fn pseudo-fnsym-p)
                              (args pseudo-term-listp))
    :measure (acl2::nat-list-measure (list clk 0 0 1 0))
    :returns (new-x pseudo-termp)
    (tac-rewrite-apply-rules clk (tac-rewrites) fn args))

  (define tac-rewrite-apply-rules ((clk natp)
                                   (rules cmr::rewritelist-p)
                                   (fn pseudo-fnsym-p)
                                   (args pseudo-term-listp))
    :measure (acl2::nat-list-measure (list clk 0 0 0 (len rules)))
    :returns (new-x pseudo-termp)
    (if (atom rules)
        (pseudo-term-fncall fn args)
      (b* (((mv ok rhs subst) (tac-rewrite-apply-rule (car rules) fn args))
           ((when (and ok (not (zp clk))))
            (tac-rewrite (1- clk) rhs subst)))
        (tac-rewrite-apply-rules clk (cdr rules) fn args))))
  ///
  (verify-guards tac-rewrite)

  (defun termlists-types-preserved (x y subst ctx)
    (if (atom x)
        t
      (and (let ((orig (tac-term-type (cmr::term-subst-strict (car x) subst) ctx)))
             (or (not orig)
                 (equal orig (tac-term-type (car y) ctx))))
           (termlists-types-preserved (cdr x) (cdr y) subst ctx))))

  (local (defthm open-prefixp
           (equal (acl2::prefixp (cons a b) x)
                  (and (consp x)
                       (equal (car x) a)
                       (acl2::prefixp b (cdr x))))
           :hints(("Goal" :in-theory (enable acl2::prefixp)))))

  (local (defthm prefixp-of-nil
           (acl2::prefixp nil x)
           :hints(("Goal" :in-theory (enable acl2::prefixp)))))
  
  
  (local
   (defthm term-type-when-termlists-types-preserved
     (implies (and (bind-free '((subst . subst)) (subst))
                   (termlists-types-preserved (pseudo-term-call->args x) rw-args subst ctx)
                   (equal xsubst  (cmr::term-subst-strict x subst))
                   (equal type (tac-term-type xsubst ctx))
                   type
                   (equal (len rw-args) (len (pseudo-term-call->args x)))
                   (pseudo-term-case x :fncall))
              (equal (tac-term-type (pseudo-term-fncall
                                     (pseudo-term-fncall->fn x) rw-args)
                                    ctx)
                     type))
     :hints(("Goal"
             :in-theory (e/d (tac-function-argument-types)
                             (termlists-types-preserved))
             :do-not-induct t
             :expand ((cmr::term-subst-strict x subst)
                      (cmr::termlist-subst-strict nil subst)
                      (cmr::termlist-subst-strict (pseudo-term-call->args x) subst)
                      (cmr::termlist-subst-strict (cdr (pseudo-term-call->args x)) subst)
                      (:free (fn args) (tac-term-type (pseudo-term-fncall fn args) ctx))))
            (and stable-under-simplificationp
                 '(:expand ((termlists-types-preserved (pseudo-term-call->args x) rw-args subst ctx)
                            (termlists-types-preserved (cdr (pseudo-term-call->args x)) (cdr rw-args) subst ctx))))
            (and stable-under-simplificationp
                 '(:expand ((cmr::termlist-subst-strict (cddr (pseudo-term-call->args x)) subst)
                            (cmr::termlist-subst-strict nil subst)
                            (termlists-types-preserved (cddr (pseudo-term-call->args x)) (cddr rw-args) subst ctx)))))))

  (std::defret-mutual tac-rewrite-types-preserved
    (defret tac-rewrite-types-preserved
      (let ((type (tac-term-type (cmr::term-subst-strict x subst) ctx)))
        (implies type
                 (equal (tac-term-type new-x ctx) type)))
      :hints ('(:expand (<call>)
                :do-not-induct t)
              (and stable-under-simplificationp
                   '(:expand ((cmr::term-subst-strict x subst)))))
      :fn tac-rewrite)

    (defret tac-rewrite-list-types-preserved
      (termlists-types-preserved x new-x subst ctx)
      :hints ('(:expand (<call>
                         (:free (newx) (termlists-types-preserved x newx subst ctx))
                         (:free (newx) (termlists-types-preserved nil newx subst ctx)))))
      :fn tac-rewrite-list)

    (defret tac-rewrite-fncall-types-preserved
      (let ((type (tac-term-type (pseudo-term-fncall fn args) ctx)))
        (implies type
                 (equal (tac-term-type new-x ctx) type)))
      :hints ('(:expand (<call>)))
      :fn tac-rewrite-fncall)

    (defret tac-rewrite-apply-rules-types-preserved
      (implies (tac-rewrites-rhs-preserved rules)
               (let ((type (tac-term-type (pseudo-term-fncall fn args) ctx)))
                 (implies type
                          (equal (tac-term-type new-x ctx) type))))
      :hints ('(:expand (<call>
                         (tac-rewrites-rhs-preserved rules))))
      :fn tac-rewrite-apply-rules))

  (defun tac-rewrite-list-evals-preserved (x new-x subst env ctx)
    (if (atom x)
        t
      (and (implies (or (not (pseudo-term-case (car x) :fncall))
                        (tac-term-type (cmr::term-subst-strict (car x) subst) ctx))
                    (equal (tac-ev (car new-x) env)
                           (tac-ev (car x) (tac-ev-alist subst env))))
           (tac-rewrite-list-evals-preserved (cdr x) (cdr new-x) subst env ctx))))

  (local (defthm fncall-of-term-subst-strict
           (implies (pseudo-term-case x :fncall)
                    (pseudo-term-case (cmr::term-subst-strict x subst) :fncall))
           :hints(("Goal" :expand ((cmr::term-subst-strict x subst))))))

  (defthm eval-preserved-of-rel-term-when-arg-evals-preserved
    (implies (and (tac-rewrite-list-evals-preserved
                   args rw-args subst env ctx)
                  (equal (len args) (len rw-args))
                  (tac-term-type (pseudo-term-fncall fn
                                                     (cmr::termlist-subst-strict args subst))
                                 ctx)
                  (pseudo-fnsym-p fn))
             (equal (tac-ev (cons fn rw-args) env)
                    (tac-ev (cons fn args) (tac-ev-alist subst env))))
    :hints (("goal" :expand ((:free (args)
                              (tac-term-type (pseudo-term-fncall fn args)
                                          ctx))
                             (cmr::termlist-subst-strict args subst)
                             (cmr::termlist-subst-strict (cdr args) subst)
                             (tac-rewrite-list-evals-preserved
                              args rw-args subst env ctx)
                             (tac-rewrite-list-evals-preserved
                              (cdr args) (cdr rw-args) subst env ctx))
             :in-theory (enable tac-function-return-type
                                tac-function-argument-types)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((cmr::termlist-subst-strict (cddr args) subst)
                             (tac-rewrite-list-evals-preserved
                              (cddr args) (cddr rw-args) subst env ctx))))))
  
  (std::defret-mutual tac-rewrite-correct
    (defret tac-rewrite-correct
      (implies (and (tac-term-type (cmr::term-subst-strict x subst) ctx)
                    (tac-typed-env-p env ctx))
               (equal (tac-ev new-x env)
                      (tac-ev x (tac-ev-alist subst env))))
      :hints ('(:expand (<call>)
                :do-not-induct t)
              (and stable-under-simplificationp
                   '(:expand ((cmr::term-subst-strict x subst))))
              (and stable-under-simplificationp
                   '(:cases ((equal (pseudo-term-kind x) :quote)
                             (equal (pseudo-term-kind x) :lambda)))))
      :fn tac-rewrite)

    (defret tac-rewrite-list-correct
      (implies (tac-typed-env-p env ctx)
               (tac-rewrite-list-evals-preserved x new-x subst env ctx))
      :hints ('(:expand (<call>
                         (:free (newx) (tac-rewrite-list-evals-preserved x newx subst env ctx))
                         (:free (newx) (tac-rewrite-list-evals-preserved nil newx subst env ctx)))))
      :fn tac-rewrite-list)

    (defret tac-rewrite-fncall-correct
      (implies (and (tac-term-type (pseudo-term-fncall fn args) ctx)
                    (tac-typed-env-p env ctx))
               (equal (tac-ev new-x env)
                      (tac-ev (pseudo-term-fncall fn args) env)))
      :hints ('(:expand (<call>)))
      :fn tac-rewrite-fncall)

    (defret tac-rewrite-apply-rules-correct
      (implies (and (tac-term-type (pseudo-term-fncall fn args) ctx)
                    (tac-typed-env-p env ctx)
                    (tac-ev-theorem-rewritesp rules)
                    (tac-rewrites-hyps-ok rules)
                    (tac-rewrites-rhs-preserved rules))
               (equal (tac-ev new-x env)
                      (tac-ev (pseudo-term-fncall fn args) env)))
      :hints ('(:expand (<call>
                         (tac-ev-theorem-rewritesp rules)
                         (tac-rewrites-hyps-ok rules)
                         (tac-rewrites-rhs-preserved rules))))
      :fn tac-rewrite-apply-rules)))




;; Positive normalization rules that already exist
;; idL/R -- setimage/preimage-of-relidentity, setintersect-of-universe
;; \bot2L/R -- setimage/preimage-of-relidentity, setintersect-of-empty
;; \top2L/R -- setimage/preimage-of-singleton-universe
;; .2,2L/R -- setimage/preimage-of-relcompose
;; .-1L/R -- setimage/preimage-of-inverse
;; \cup2L/R -- setimage/preimage-of-intersect


;; Missing positive normalization rules
;; XL/R 
;; U2L 
;; *L
;; U1
;; eL
;; \bot1

(defthm emptyp-when-in
  (implies (in e x)
           (not (emptyp x))))

(defthm emptyp-rw
  (implies (acl2::rewriting-positive-literal `(emptyp ,x))
           (iff (emptyp x)
                (not (in (head x) x)))))

(local (in-theory (disable set::in-head
                           set::in-tail-or-head)))

(acl2::def-ruleset! tac-positive-normalize-rules nil)

(defmacro def-tac-positive-normalize (name &rest args)
  `(progn (defthm ,name . ,args)
          (acl2::add-to-ruleset tac-positive-normalize-rules ,name)))

;; XL 
(def-tac-positive-normalize in-setimage-singleton-prod
  (iff (pred-in-set w (setimage (singleton e1)
                       (relprod (singleton e2) s)))
       (and (pred-equal e1 e2)
            (pred-in-set w s)))
  :hints(("Goal" :in-theory (e/d (in-of-cartesian))))
  :otf-flg t)

;; XR
(def-tac-positive-normalize in-setpreimage-singleton-prod
  (iff (pred-in-set w (setpreimage (relprod s (singleton e2))
                          (singleton e1)))
       (and (pred-equal e1 e2)
            (pred-in-set w s)))
  :hints(("Goal" :in-theory (e/d (in-of-cartesian))))
  :otf-flg t)

;; U2L
(def-tac-positive-normalize in-setimage-singleton-union
  (iff (pred-in-set w (setimage (singleton e) (relunion r1 r2)))
       (or (pred-in-set w (setimage (singleton e) r1))
           (pred-in-set w (setimage (singleton e) r2)))))

;; U2R
(def-tac-positive-normalize in-setpreimage-singleton-union
  (iff (pred-in-set w (setpreimage (relunion r1 r2) (singleton e)))
       (or (pred-in-set w (setpreimage r1 (singleton e)))
           (pred-in-set w (setpreimage r2 (singleton e))))))


(defthm image-of-relunion
  (implies (and (relation-p r1)
                (relation-p r2))
           (equal (image s (union r1 r2))
                  (union (image s r1) (image s r2))))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-image-rw))))

(defthm compose-of-relunion
  (implies (and (relation-p r1)
                (relation-p r2))
           (equal (compose r (union r1 r2))
                  (union (compose r r1) (compose r r2))))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-compose-rw
                                     in-of-compose-suff
                                     in-of-compose-suff2))))

(defthm compose-of-relunion-2
  (implies (and (relation-p r1)
                (relation-p r2))
           (equal (compose (union r1 r2) r)
                  (union (compose r1 r) (compose r2 r))))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-compose-rw
                                     in-of-compose-suff
                                     in-of-compose-suff2))))


(defthmd in-of-transitive-closure-split
  (iff (in pair (transitive-closure r))
       (or (in pair (relation-fix r))
           (in pair (compose r (transitive-closure r)))))
  :hints (("goal" :in-theory (enable transitive-closure-correct
                                     in-of-compose-rw))
          (acl2::use-termhint
           (cond ((in pair (transitive-closure r))
                  (let ((path (exists-path-witness
                               (edge->src pair) (edge->dst pair) r)))
                    `(:expand ((exists-path (edge->src pair)
                                            (edge->dst pair)
                                            r)
                               (relation-path-p ,(acl2::hq path) r))
                      . ,(and (consp (cddr path))
                              `(:use ((:instance in-of-compose-suff
                                       (x r) (y (transitive-closure r))
                                       (pair pair)
                                       (mid (cadr ,(acl2::hq path))))))))))
                 ((in pair (relation-fix r))
                  `(:use ((:instance exists-path-suff
                           (path (list (edge->src pair)
                                       (edge->dst pair)))
                           (src (edge->src pair))
                           (dst (edge->dst pair))
                           (x r)))
                    :expand ((:Free (a b) (relation-path-p (list a b) r)))))
                 (t (b* ((mid (compose-midpoint (edge->src pair)
                                                (edge->dst pair)
                                                r (transitive-closure r)))
                         (?path (exists-path-witness mid (edge->dst pair) r)))
                      `(:expand ((exists-path ,(acl2::hq mid)
                                              (edge->dst pair)
                                              r)
                                 (:free (a b) (relation-path-p (cons a b) r))
                                 (relation-path-p ,(acl2::hq path) r))
                        :use ((:instance exists-path-suff
                               (path (cons (edge->src pair)
                                           ,(acl2::hq path)))
                               (src (edge->src pair))
                               (dst (edge->dst pair))
                               (x r)))
                        ))))))
  :otf-flg t)

(defthm car-last-of-append
  (implies (consp y)
           (equal (car (last (append x y)))
                  (car (last y)))))

(defthm relation-path-p-of-append
  (iff (relation-path-p (append x y) r)
       (cond ((atom x)
              (relation-path-p y r))
             ((atom y)
              (relation-path-p x r))
             ((atom (cdr x))
              (and (in (edge (car x) (car y)) (relation-fix r))
                   (or (atom (cdr y))
                       (relation-path-p y r))))
             (t (and (relation-path-p x r)
                     (in (edge (car (last x)) (car y)) (relation-fix r))
                     (or (atom (cdr y))
                         (relation-path-p y r))))))
  :hints(("Goal" :in-theory (enable relation-path-p))))
                  

(local (include-book "std/lists/take" :dir :system))
(defthm car-last-of-take
  (equal (car (last (take n x)))
         (if (zp n)
             nil
           (nth (- n 1) x)))
  :hints(("Goal" :in-theory (enable nth take))))

(local (include-book "arithmetic/top" :dir :system))

;; (local (defthm car-last-cdr
;;          (equal (car (last (cdr x)))
;;                 (and (consp (cdr x))
;;                      (car (last x))))))

;; (local (in-theory (disable last)))


(local
 (defthmd relation-path-p-implies-last-edge-lemma
   (implies (relation-path-p path r)
            (in (edge (nth (- (len path) 2) path) (car (last path))) (relation-fix r)))
   :hints(("Goal" :in-theory (enable relation-path-p)))))

(local
 (defthmd relation-path-p-implies-last-edge
   (implies (and (relation-path-p path r)
                 (equal dst (car (last path)))
                 (equal n (- (len path) 2)))
            (in (edge (nth n path) dst) (relation-fix r)))
   :hints(("Goal" :in-theory (enable relation-path-p-implies-last-edge-lemma)))))

(defthm relation-path-p-of-take
  (implies (and (relation-path-p path r)
                (case-split (<= 2 (nfix n)))
                (<= (nfix n) (len path)))
           (relation-path-p (take n path) r))
  :hints(("Goal" :in-theory (enable relation-path-p))))


(defthmd compose-transitive-closure-invert
  (iff (in pair (compose (transitive-closure r) r))
       (in pair (compose r (transitive-closure r))))
  :hints (("goal" :in-theory (enable transitive-closure-correct
                                     in-of-compose-rw))
          (acl2::use-termhint
           (b* (((edge pair)))
             (cond ((in pair (compose (transitive-closure r) r))
                    (b* ((mid (compose-midpoint pair.src pair.dst
                                                (transitive-closure r) r))
                         (path1 (exists-path-witness
                                 pair.src mid r))
                         (path (append path1 (list pair.dst))))
                      `(:expand ((exists-path ,(acl2::hq pair.src)
                                              ,(acl2::hq mid)
                                              r)
                                 (relation-path-p ,(acl2::hq path1) r)
                                 (:free (a b) (relation-path-p (list a b) r)))
                        :use ((:instance in-of-compose-suff
                               (pair pair)
                               (mid ,(acl2::hq (cadr path)))
                               (x r) (y (transitive-closure r)))
                              (:instance exists-path-suff
                               (src ,(acl2::hq (cadr path)))
                               (dst ,(acl2::hq pair.dst))
                               (path ,(acl2::hq (cdr path)))
                               (x r)))
                        :in-theory (e/d (transitive-closure-correct
                                         in-of-compose-rw)
                                        (exists-path-suff)))))
                   (t (b* ((mid (compose-midpoint pair.src pair.dst
                                                  r (transitive-closure r)))
                           (path1 (exists-path-witness
                                   mid pair.dst r))
                           (path (cons pair.src path1))
                           (new-path (take (len path1) path))
                           (new-mid (car (last new-path))))
                      `(:expand ((exists-path ,(acl2::hq mid)
                                              ,(acl2::hq pair.dst)
                                              r)
                                 (relation-path-p ,(acl2::hq path1) r)
                                 (:free (a b) (relation-path-p (cons a b) r)))
                        :use ((:instance in-of-compose-suff
                               (pair pair)
                               (mid ,(acl2::hq new-mid))
                               (x (transitive-closure r)) (y r))
                              (:instance exists-path-suff
                               (src ,(acl2::hq pair.src))
                               (dst ,(acl2::hq new-mid))
                               (path ,(acl2::hq new-path))
                               (x r)))
                        :in-theory (e/d (transitive-closure-correct
                                         in-of-compose-rw
                                         relation-path-p-implies-last-edge)
                                        (exists-path-suff)))))))))
  :otf-flg t)

(defthmd in-of-transitive-closure-split2
  (iff (in pair (transitive-closure r))
       (or (in pair (relation-fix r))
           (in pair (compose (transitive-closure r) r))))
  :hints (("goal" :use in-of-transitive-closure-split
           :in-theory (e/d (compose-transitive-closure-invert)))))
                              

(defthmd image-of-compose-inverse
  (equal (image (image x y) z)
         (image x (compose y z))))


;; *L
(def-tac-positive-normalize pred-nonempty-setimage-singleton-star
  (implies (and (event-p e)
                (event-p w))
           (iff (pred-in-set w (setimage (singleton e) (relstar r)))
                (or (pred-in-set w (singleton e))
                    (pred-in-set w (setimage (setimage (singleton e) r)
                                             (relstar r))))))
  :hints(("Goal" :in-theory (e/d (reflexive-transitive-closure
                                  image-of-compose-inverse)
                                 (image-of-compose
                                  in-of-compose-rw)))
         (and stable-under-simplificationp
              '(:use ((:instance in-of-transitive-closure-split
                       (pair (edge e w)))
                      (:instance in-of-compose-suff
                       (x r) (y (id-relation (universe)))
                       (pair (edge e w)) (mid w)))
                :in-theory (enable in-of-compose-rw))))
  :otf-flg t)

;; +L
(def-tac-positive-normalize pred-nonempty-setimage-singleton-plus
  (implies (and (event-p e)
                (event-p w))
           (iff (pred-in-set w (setimage (singleton e) (relplus r)))
                (or (pred-in-set w (setimage (singleton e) r))
                    (pred-in-set w (setimage (setimage (singleton e) r)
                                             (relplus r))))))
  :hints(("Goal" :in-theory (e/d (transitive-closure
                                  image-of-compose-inverse)
                                 (image-of-compose
                                  in-of-compose-rw)))
         (and stable-under-simplificationp
              '(:use ((:instance in-of-transitive-closure-split
                       (pair (edge e w)))
                      (:instance in-of-compose-suff
                       (x r) (y (id-relation (universe)))
                       (pair (edge e w)) (mid w)))
                :in-theory (enable in-of-compose-rw))))
  :otf-flg t)

(defthmd preimage-of-compose-inverse
  (equal (preimage (preimage x y) z)
         (preimage x (compose z y))))

;; *R
(def-tac-positive-normalize pred-nonempty-setpreimage-singleton-star
  (implies (and (event-p e)
                (event-p w))
           (iff (pred-in-set w (setpreimage (relstar r) (singleton e)))
                (or (pred-in-set w (singleton e))
                    (pred-in-set w (setpreimage (relstar r)
                                       (setpreimage r (singleton e)))))))
  :hints(("Goal" :in-theory (e/d (reflexive-transitive-closure
                                  preimage-of-compose-inverse)
                                 (preimage-of-compose
                                  in-of-compose-rw)))
         (and stable-under-simplificationp
              '(:use ((:instance in-of-transitive-closure-split2
                       (pair (edge w e)))
                      (:instance in-of-compose-suff
                       (x (id-relation (universe))) (y r)
                       (pair (edge w e)) (mid w))
                      )
                :in-theory (enable in-of-compose-rw))))
  :otf-flg t)

;; +R
(def-tac-positive-normalize pred-nonempty-setpreimage-singleton-plus
  (implies (and (event-p e)
                (event-p w))
           (iff (pred-in-set w (setpreimage (relplus r) (singleton e)))
                (or (pred-in-set w (setpreimage r (singleton e)))
                    (pred-in-set w (setpreimage (relplus r)
                                                (setpreimage r (singleton e)))))))
  :hints(("Goal" :in-theory (e/d (reflexive-transitive-closure
                                  preimage-of-compose-inverse)
                                 (preimage-of-compose
                                  in-of-compose-rw)))
         (and stable-under-simplificationp
              '(:use ((:instance in-of-transitive-closure-split2
                       (pair (edge w e)))
                      (:instance in-of-compose-suff
                       (x (id-relation (universe))) (y r)
                       (pair (edge w e)) (mid w))
                      )
                :in-theory (enable in-of-compose-rw))))
  :otf-flg t)


;; U1
(def-tac-positive-normalize in-setunion
  (iff (pred-in-set w (setunion s1 s2))
       (or (pred-in-set w s1)
           (pred-in-set w s2))))
;; eL
(def-tac-positive-normalize in-singleton-intersect
  (iff (pred-in-set w (setintersect (singleton e1) (singleton e2)))
       (and (pred-equal e1 e2)
            (pred-in-set w (singleton e1)))))

;; \bot1
(def-tac-positive-normalize in-emptyset
  (iff (pred-in-set w (emptyset))
       (pred-false)))


(encapsulate nil

  (acl2::defconsts *tac-positive-normalize-rules*
    (b* (((mv err rewrites)
          (tac-collect-rewrites-aux
           (acl2::get-ruleset 'tac-positive-normalize-rules (w state))
           (w state))))
      (if err
          (er hard? '*tac-positive-normalize-rules* "~@0" err)
        rewrites)))

  (define tac-positive-normalize-rules ()
    :returns (rewrites cmr::rewritelist-p)
    *tac-positive-normalize-rules*
    ///
    (in-theory (disable (tac-positive-normalize-rules)))))


(define collect-if-branches ((x pseudo-termp))
  :returns (branches pseudo-term-listp)
  :measure (pseudo-term-count x)
  (pseudo-term-case x
    :fncall (if (eq x.fn 'if)
                (b* (((list a b c) x.args)
                     ((when (equal c ''nil))
                      (append (collect-if-branches a)
                              (collect-if-branches b)))
                     ((when (equal a b))
                      (append (collect-if-branches a)
                              (collect-if-branches c))))
                  (list (pseudo-term-fix x)))
              (list (pseudo-term-fix x)))
    :otherwise (list (pseudo-term-fix x))))
                     


(defsection tac-pred-rewrite-rhs-typed
  (defun-sk tac-pred-rewrite-rhs-typed (rule)
    (forall (x ctx)
            (b* (((cmr::rewrite rule))
                 ((mv unify-ok subst) (cmr::term-unify-strict rule.lhs x nil)))
              (implies (and unify-ok
                            (equal (tac-term-type x ctx) :pred))
                       (subsetp (tac-termlist-types (collect-if-branches (cmr::term-subst-strict rule.rhs subst)) ctx)
                                '(:pred)))))
    :rewrite :direct)

  (in-theory (disable tac-pred-rewrite-rhs-typed)))



(define tac-pred-rewrites-rhs-typed (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (tac-pred-rewrite-rhs-typed (car rules))
         (tac-pred-rewrites-rhs-typed (cdr rules))))
  ///
  (local (defthm car-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (car x) a))))
  (local (defthm cdr-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (cdr x) b))))
  
  (defthm tac-pred-rewrites-rhs-typed-of-tac-positive-normalize-rules
    (tac-pred-rewrites-rhs-typed (tac-positive-normalize-rules))
    :hints (("goal" :expand ((:free (x) (tac-pred-rewrite-rhs-typed x))
                             (:free (a b) (tac-pred-rewrites-rhs-typed (cons a b))))
             :in-theory (e/d (cmr::term-subst-strict
                              tac-termlist-types
                              collect-if-branches
                              cmr::termlist-subst-strict
                              cmr::equal-of-pseudo-term-fncall
                              (tac-positive-normalize-rules))
                             (tac-pred-rewrite-rhs-typed-necc))))))




(encapsulate nil
  (local (defthm car-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (car x) a))))
  (local (defthm cdr-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (cdr x) b))))
  
  (defthm tac-rewrites-hyps-ok-of-tac-positive-normalize-rules
    (tac-rewrites-hyps-ok (tac-positive-normalize-rules))
    :hints (("goal" :expand ((:free (x) (tac-rewrite-hyps-ok x))
                             (:free (a b) (tac-rewrites-hyps-ok (cons a b))))
             :in-theory (e/d (cmr::term-subst-strict
                              cmr::termlist-subst-strict
                              cmr::equal-of-pseudo-term-fncall
                              tac-ev-cube
                              (tac-positive-normalize-rules))
                             (tac-rewrite-hyps-ok-necc))))))

(defthm tac-ev-theorem-rewritesp-of-tac-positive-normalize-rules
    (tac-ev-theorem-rewritesp (tac-positive-normalize-rules))
    :hints(("Goal" :in-theory (acl2::e/d* ((tac-positive-normalize-rules))
                                          (tac-functions
                                           (emptyset)
                                           (pred-false)))
            :expand ((:Free (a b) (tac-ev-theorem-rewritesp (cons a b)))))))


;; Missing negative normalization rules
;; ~aL/R
;; ~*L/R
;; ~U2L/R
;; ~=L
;; ~XL/R
;; ~A
;; ~U1
;; ~T1  -- special -- introduces new conjuncts for all e
;; ~eL/R
;; ~.1,2L/R
;; ~.2,1L/R
;; ~\cup1L/R
;; ~\cup_e
;; ~1XL/R
;; ~X1L/R
;; ~0
;; ~=


(acl2::def-ruleset! tac-negative-normalize-rules nil)

(defmacro def-tac-negative-normalize (name &rest args)
  `(progn (defthm ,name . ,args)
          (acl2::add-to-ruleset tac-negative-normalize-rules ,name)))
;; ~aL
(def-tac-negative-normalize not-in-singleton-image-when-pair
  (implies (and (pred-in-rel e1 e2 a)
                (relation-p a))
           (iff (not-pred-in-set w (image (singleton e1) a))
                (and (not-pred-in-set w (image (singleton e1) a))
                     (not-pred-in-set w (singleton e2))))))

;; ~aR
(def-tac-negative-normalize not-in-singleton-preimage-when-pair
  (implies (and (in (edge e2 e1) a)
                (relation-p a))
           (iff (not-pred-in-set w (setpreimage a (singleton e1)))
                (and (not-pred-in-set w (setpreimage a (singleton e1)))
                     (not-pred-in-set w (singleton e2))))))


(defthm in-compose-id
  (implies (event-p (edge->dst pair))
           (iff (in pair
                    (compose r (id-relation (universe))))
                (in pair (relation-fix r))))
  :hints (("goal" :in-theory (enable in-of-compose-rw)
           :use ((:instance in-of-compose-suff
                  (pair pair)
                  (mid (edge->dst pair))
                  (x r) (y (id-relation (universe))))))))

(defthm in-compose-id2
  (implies (event-p (edge->src pair))
           (iff (in pair
                    (compose (id-relation (universe)) r))
                (in pair (relation-fix r))))
  :hints (("goal" :in-theory (enable in-of-compose-rw)
           :use ((:instance in-of-compose-suff
                  (pair pair)
                  (mid (edge->src pair))
                  (x (id-relation (universe))) (y r))))))

;; ~*L
(def-tac-negative-normalize not-in-singleton-star-image
  (implies (event-p w)
           (iff (not-pred-in-set w (setimage (singleton e) (relstar r)))
                (and (not-pred-in-set w (singleton e))
                     (not-pred-in-set w (setimage (setimage (singleton e) r) (relstar r))))))
  :hints(("Goal" :in-theory (e/d (reflexive-transitive-closure
                                  image-of-compose-inverse
                                  in-of-compose-suff
                                  in-of-compose-suff2
                                  in-of-compose-rw)
                                 (image-of-compose))
          :use ((:instance in-of-transitive-closure-split
                 (pair (edge e w)))))))

;; ~+L
(def-tac-negative-normalize not-in-singleton-plus-image
  (implies (event-p w)
           (iff (not-pred-in-set w (setimage (singleton e) (relplus r)))
                (and (not-pred-in-set w (setimage (singleton e) r))
                     (not-pred-in-set w (setimage (setimage (singleton e) r) (relplus r))))))
  :hints(("Goal" :in-theory (e/d (reflexive-transitive-closure
                                  image-of-compose-inverse
                                  in-of-compose-suff
                                  in-of-compose-suff2
                                  in-of-compose-rw)
                                 (image-of-compose))
          :use ((:instance in-of-transitive-closure-split
                 (pair (edge e w)))))))

;; ~*R
(def-tac-negative-normalize not-in-singleton-star-preimage
  (implies (event-p w)
           (iff (not-pred-in-set w (setpreimage (relstar r) (singleton e)))
                (and (not-pred-in-set w (singleton e))
                     (not-pred-in-set w (setpreimage (relstar r) (setpreimage r (singleton e)))))))
  :hints(("Goal" :in-theory (e/d (reflexive-transitive-closure
                                  preimage-of-compose-inverse
                                  in-of-compose-suff
                                  in-of-compose-suff2
                                  in-of-compose-rw)
                                 (preimage-of-compose))
          :use ((:instance in-of-transitive-closure-split2
                 (pair (edge w e)))))))


;; ~+R
(def-tac-negative-normalize not-in-singleton-plus-preimage
  (implies (event-p w)
           (iff (not-pred-in-set w (setpreimage (relplus r) (singleton e)))
                (and (not-pred-in-set w (setpreimage r (singleton e)))
                     (not-pred-in-set w (setpreimage (relplus r) (setpreimage r (singleton e)))))))
  :hints(("Goal" :in-theory (e/d (reflexive-transitive-closure
                                  preimage-of-compose-inverse
                                  in-of-compose-suff
                                  in-of-compose-suff2
                                  in-of-compose-rw)
                                 (preimage-of-compose))
          :use ((:instance in-of-transitive-closure-split2
                 (pair (edge w e)))))))

;; ~U2L
(def-tac-negative-normalize not-in-singleton-union-image
  (iff (not-pred-in-set w (setimage (singleton e) (relunion r1 r2)))
       (and (not-pred-in-set w (setimage (singleton e) r1))
            (not-pred-in-set w (setimage (singleton e) r2)))))

;; ~U2R
(def-tac-negative-normalize not-in-singleton-union-preimage
  (iff (not-pred-in-set w (setpreimage (relunion r1 r2) (singleton e)))
       (and (not-pred-in-set w (setpreimage r1 (singleton e)))
            (not-pred-in-set w (setpreimage r2 (singleton e))))))

;; ~=L
(def-tac-negative-normalize not-in-singleton
  (implies (pred-equal e1 e2)
           (iff (not-pred-in-set w (singleton e1))
                (and (not-pred-in-set w (singleton e1))
                     (not-pred-in-set w (singleton e2))))))

;; ~XL
(def-tac-negative-normalize not-in-singleton-image-prod
  (iff (not-pred-in-set w (setimage (singleton e) (relprod s1 s2)))
       (or (not (pred-nonempty (setintersect (singleton e) s1)))
           (not-pred-in-set w s2)))
  :hints(("Goal" :in-theory (enable in-of-cartesian))))
  
;; ~XR
(def-tac-negative-normalize not-in-singleton-preimage-prod
  (iff (not-pred-in-set w (setpreimage (relprod s1 s2) (singleton e)))
       (or (not (pred-nonempty (setintersect (singleton e) s2)))
           (not-pred-in-set w s1)))
  :hints(("Goal" :in-theory (enable in-of-cartesian))))



;; ~A
(def-tac-negative-normalize not-in-base-set
  (implies (and (pred-in-set e a)
                (base-set-p a))
           (iff (not-pred-in-set w a)
                (and (not-pred-in-set w a)
                     (not-pred-in-set w (singleton e))))))
           
;; ~U1
(def-tac-negative-normalize not-in-setunion
  (iff (not-pred-in-set w (setunion s1 s2))
       (and (not-pred-in-set w s1)
            (not-pred-in-set w s2))))


;; ~T1  -- special -- introduces new conjuncts for all e
(def-tac-negative-normalize not-in-universe
  (implies (and (mentioned-event-p e)
                (event-p e))
           (iff (not-pred-in-set w (universe))
                (and (not-pred-in-set w (universe))
                     (not-pred-in-set w (singleton e))))))
;; ~eL
(def-tac-negative-normalize not-in-singleton-intersect-1
  (iff (not-pred-in-set w (setintersect (singleton e) s))
       (or (not-pred-in-set w (singleton e))
           (not (pred-nonempty (setintersect (singleton e) s))))))

;; ~eR
(def-tac-negative-normalize not-in-singleton-intersect-2
  (iff (not-pred-in-set w (setintersect s (singleton e)))
       (or (not-pred-in-set w (singleton e))
           (not (pred-nonempty (setintersect s (singleton e)))))))



;; (defthm singleton-intersect-image
;;   (equal (intersect (insert e nil) (image s r))
;;          (intersect (preimage (insert e nil) r) s))
;;   :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
;;                                      pick-a-point-subset-strategy))))


;; ~.1,2L
(def-tac-negative-normalize nonempty-singleton-intersect-image-1
  (implies (not-singleton-set-p s)
           (iff (not-pred-nonempty (setintersect (singleton e) (setimage s r)))
                (not-pred-nonempty (setintersect (setpreimage r (singleton e)) s))))
  :hints(("Goal" :in-theory (e/d (in-of-image-rw)))
         (and stable-under-simplificationp
              '(:in-theory (e/d (in-of-image-rw)
                                (emptyp-when-in
                                 set::never-in-empty))
                :use ((:instance emptyp-when-in
                       (x (setintersect (setpreimage r (singleton e)) s))
                       (e (image-witness e s r)))))))
  :otf-flg t)

;; ~.1,2R
(def-tac-negative-normalize nonempty-singleton-intersect-image-2
  (implies (not-singleton-set-p s)
           (iff (not-pred-nonempty (setintersect (setimage s r) (singleton e)))
                (not-pred-nonempty (setintersect s (setpreimage r (singleton e))))))
  :hints(("Goal" :in-theory (e/d (in-of-image-rw)))
         (and stable-under-simplificationp
              '(:in-theory (e/d (in-of-image-rw)
                                (emptyp-when-in
                                 set::never-in-empty))
                :use ((:instance emptyp-when-in
                       (x (setintersect s (setpreimage r (singleton e))))
                       (e (image-witness e s r)))))))
  :otf-flg t)




;; ~.2,1L
(def-tac-negative-normalize nonempty-singleton-intersect-image-3
  (implies (not-singleton-set-p s)
           (iff (not-pred-nonempty (setintersect (singleton e) (setpreimage r s)))
                (not-pred-nonempty (setintersect (setimage (singleton e) r) s))))
  :hints(("Goal" :in-theory (e/d (in-of-preimage-rw)))
         (and stable-under-simplificationp
              '(:in-theory (e/d (in-of-preimage-rw)
                                (emptyp-when-in
                                 set::never-in-empty))
                :use ((:instance emptyp-when-in
                       (x (setintersect (setimage (singleton e) r) s))
                       (e (preimage-witness e s r)))))))
  :otf-flg t)
;; ~.2,1R
(def-tac-negative-normalize nonempty-singleton-intersect-image-4
  (implies (not-singleton-set-p s)
           (iff (not-pred-nonempty (setintersect (setpreimage r s) (singleton e)))
                (not-pred-nonempty (setintersect s (setimage (singleton e) r)))))
  :hints(("Goal" :in-theory (e/d (in-of-preimage-rw)))
         (and stable-under-simplificationp
              '(:in-theory (e/d (in-of-preimage-rw)
                                (emptyp-when-in
                                 set::never-in-empty))
                :use ((:instance emptyp-when-in
                       (x (setintersect s (setimage (singleton e) r)))
                       (e (preimage-witness e s r)))))))
  :otf-flg t)

;; ~\cap1L
(def-tac-negative-normalize nonempty-singleton-intersect-intersect-1
  (iff (not-pred-nonempty (setintersect (singleton e) (setintersect s1 s2)))
       (or (not-pred-nonempty (setintersect (singleton e) s1))
           (not-pred-nonempty (setintersect (singleton e) s2)))))
;; ~\cap1R
(def-tac-negative-normalize nonempty-singleton-intersect-intersect-2
  (iff (not-pred-nonempty (setintersect (setintersect s1 s2) (singleton e)))
       (or (not-pred-nonempty (setintersect s1 (singleton e)))
           (not-pred-nonempty (setintersect s2 (singleton e))))))

;; ~\cap_e
(def-tac-negative-normalize nonempty-singleton-intersect-singleton
  (iff (not-pred-nonempty (setintersect (singleton e1) (singleton e2)))
       (not (pred-equal e1 e2))))

;; ~1XL
(def-tac-negative-normalize not-in-image-product-singleton-1
  (iff (not-pred-in-set w (setimage s1 (relprod (singleton e) s2)))
       (or (not-pred-in-set w s2)
           (not-pred-nonempty (setintersect s1 (singleton e)))))
  :hints(("Goal" :in-theory (enable in-of-image-rw
                                    in-of-cartesian))))
;; ~1XR
(def-tac-negative-normalize not-in-image-product-singleton-2
  (iff (not-pred-in-set w (setpreimage (relprod s2 (singleton e)) s1))
       (or (not-pred-in-set w s2)
           (not-pred-nonempty (setintersect s1 (singleton e)))))
  :hints(("Goal" :in-theory (enable in-of-preimage-rw
                                    in-of-cartesian))))
;; ~X1L
(def-tac-negative-normalize not-in-image-product-singleton-3
  (iff (not-pred-in-set w (setpreimage (relprod (singleton e) s1) s2))
       (or (not-pred-in-set w (singleton e))
           (not-pred-nonempty (setintersect s1 s2))))
  :hints(("Goal" :in-theory (e/d (in-of-preimage-rw
                                  in-of-cartesian)
                                 (emptyp-when-in
                                  set::never-in-empty))
          :use ((:instance emptyp-when-in
                 (e (preimage-witness w s2 (cartesian (insert e nil) s1)))
                 (x (intersect s1 s2)))))))

;; ~X1R
(def-tac-negative-normalize not-in-image-product-singleton-4
  (iff (not-pred-in-set w (setimage s2 (relprod s1 (singleton e))))
       (or (not-pred-in-set w (singleton e))
           (not-pred-nonempty (setintersect s1 s2))))
  :hints(("Goal" :in-theory (e/d (in-of-image-rw
                                  in-of-cartesian)
                                 (emptyp-when-in
                                  set::never-in-empty))
          :use ((:instance emptyp-when-in
                 (e (image-witness w s2 (cartesian s1 (insert e nil))))
                 (x (intersect s1 s2)))))))
;; ~0
(def-tac-negative-normalize not-pred-nonempty-of-singleton
  (iff (not-pred-nonempty (singleton e))
       nil))

;; ~=
(def-tac-negative-normalize not-pred-equal-same
  (iff (not-pred-equal e e)
       nil))




;; Propagation thms
(defthm propagate-into-setimage
  (iff (pred-in-set w (setimage s r))
       (and (pred-in-set (image-witness w s r) s)
            (pred-in-rel (image-witness w s r) w r))))

(defthm propagate-into-setpreimage
  (iff (pred-in-set w (setpreimage r s))
       (and (pred-in-set (preimage-witness w s r) s)
            (pred-in-rel w (preimage-witness w s r) r))))

(defthm propagate-into-relidentity
  (iff (pred-in-rel w1 w2 (relidentity s))
       (and (equal w1 w2)
            (pred-in-set w1 s))))

(defthm propagate-into-relcompose
  (iff (pred-in-rel w1 w2 (relcompose r1 r2))
       (and (pred-in-rel w1 (compose-midpoint w1 w2 r1 r2) r1)
            (pred-in-rel (compose-midpoint w1 w2 r1 r2) w2 r2)))
  :hints(("Goal" :in-theory (enable in-of-compose-suff-rw
                                    in-of-compose-rw))))

(defthm propagate-into-relinverse
  (iff (pred-in-rel w1 w2 (relinverse r))
       (pred-in-rel w2 w1 r)))

(defthm propagate-into-relprod
  (iff (pred-in-rel w1 w2 (relprod s1 s2))
       (and (pred-in-set w1 s1)
            (pred-in-set w2 s2)))
  :hints(("Goal" :in-theory (enable in-of-cartesian))))

(defthm propagate-into-setintersect
  (iff (pred-in-set w (setintersect s1 s2))
       (and (pred-in-set w s1)
            (pred-in-set w s2))))

(defthm propagate-into-relintersect
  (iff (pred-in-rel w1 w2 (relintersect r1 r2))
       (and (pred-in-rel w1 w2 r1)
            (pred-in-rel w1 w2 r2))))

;; implemented:
;; ~2XL/R -- relcompose-singleton-prod-1 relcompose-singleton-prod-2
;; ~X2L/R -- relcompose-singleton-prod-3 relcompose-singleton-prod-4
;; ~x-1L/R -- relinverse-of-relprod
;; ~\capXL/R -- relintersect-relprod-singleton-1 relintersect-relprod-singleton-2
;; ~X\capL/R -- relintersect-relprod-singleton-3 relintersect-relprod-singleton-4


(fty::deflist pseudo-term-list-list :elt-type pseudo-term-listp
  :pred acl2::pseudo-term-list-listp
  :true-listp t)

(defprod tac-positive-rule-result-branch
  ((assums pseudo-term-listp)
   (ctx-results pseudo-term-listp))) ;; all conjoined

;; all disjoined
(deflist tac-positive-rule-result-branchlist :elt-type tac-positive-rule-result-branch :true-listp t)

(defprod tac-positive-rule-result-branch-args
  ((assums pseudo-term-listp)
   (ctx-results acl2::pseudo-term-list-listp)))

(deflist tac-positive-rule-result-branch-argslist :elt-type tac-positive-rule-result-branch-args :true-listp t)


;; ------------- Types of tac-positive-rule-result objects


(define tac-positive-rule-result-branch-typed ((x tac-positive-rule-result-branch-p)
                                               (type tac-type-p)
                                               (ctx type-ctx-p))
  (b* (((tac-positive-rule-result-branch x)))
    (and (subsetp (tac-termlist-types x.assums ctx) '(:pred))
         (let ((type (tac-type-fix type)))
           (or (not type)
               (subsetp (tac-termlist-types x.ctx-results ctx) (list type))))))
  ///
  (defthm tac-positive-rule-result-branch-typed-when-nil
    (implies (tac-positive-rule-result-branch-typed x type ctx)
             (tac-positive-rule-result-branch-typed x nil ctx))))

(define tac-positive-rule-result-branchlist-typed ((x tac-positive-rule-result-branchlist-p)
                                                   (type tac-type-p)
                                                   (ctx type-ctx-p))
  (if (atom x)
      t
    (and (tac-positive-rule-result-branch-typed (car x) type ctx)
         (tac-positive-rule-result-branchlist-typed (cdr x) type ctx)))
  ///
  (defthm tac-positive-rule-result-branchlist-typed-of-append
    (iff (tac-positive-rule-result-branchlist-typed (append x y) type ctx)
         (and (tac-positive-rule-result-branchlist-typed x type ctx)
              (tac-positive-rule-result-branchlist-typed y type ctx))))
  
  (defthm tac-positive-rule-result-branchlist-typed-when-nil
    (implies (tac-positive-rule-result-branchlist-typed x type ctx)
             (tac-positive-rule-result-branchlist-typed x nil ctx))))

(deflist tac-typelistlist :elt-type tac-typelist :true-listp t)

(define tac-termlistlist-types ((x acl2::pseudo-term-list-listp)
                                (ctx type-ctx-p))
  :returns (types tac-typelistlist-p)
  (if (atom x)
      nil
    (cons (tac-termlist-types (car x) ctx)
          (tac-termlistlist-types (cdr x) ctx))))

(define prefixp-of-all (x y)
  (if (atom y)
      t
    (and (acl2::prefixp x (car y))
         (prefixp-of-all x (cdr y))))
  ///
  (defthm prefixp-of-all-of-nil
    (prefixp-of-all nil y)
    :hints(("Goal" :in-theory (enable acl2::prefixp)))))

(define tac-positive-rule-result-branch-args-typed ((x tac-positive-rule-result-branch-args-p)
                                                    (types tac-typelist-p)
                                                    (ctx type-ctx-p))
  (b* (((tac-positive-rule-result-branch-args x)))
    (and (subsetp (tac-termlist-types x.assums ctx) '(:pred))
         (prefixp-of-all (tac-typelist-fix types) (tac-termlistlist-types x.ctx-results ctx))))
  ///
  (defthm tac-positive-rule-result-branch-args-typed-of-nil
    (implies (tac-positive-rule-result-branch-args-typed x types ctx)
             (tac-positive-rule-result-branch-args-typed x nil ctx))))

(define tac-positive-rule-result-branch-argslist-typed ((x tac-positive-rule-result-branch-argslist-p)
                                                        (types tac-typelist-p)
                                                        (ctx type-ctx-p))
  (if (atom x)
      t
    (and (tac-positive-rule-result-branch-args-typed (car x) types ctx)
         (tac-positive-rule-result-branch-argslist-typed (cdr x) types ctx)))
  ///
  (defthm tac-positive-rule-result-branch-argslist-typed-of-nil
    (implies (tac-positive-rule-result-branch-argslist-typed x types ctx)
             (tac-positive-rule-result-branch-argslist-typed x nil ctx))))

;; ------------- Evaluation of of tac-positive-rule-result objects


(define tac-rule-conjoin-ctx-results ((x pseudo-term-listp) elem env)
  :verify-guards nil
  (if (atom x)
      t
    (and (in elem (tac-ev (car x) env))
         (tac-rule-conjoin-ctx-results (cdr x) elem env)))
  ///
  (defthm tac-rule-conjoin-ctx-results-of-append
    (equal (tac-rule-conjoin-ctx-results (append x y) elem env)
           (and (tac-rule-conjoin-ctx-results x elem env)
                (tac-rule-conjoin-ctx-results y elem env)))))


(define tac-eval-positive-rule-result-branch ((x tac-positive-rule-result-branch-p)
                                              elem
                                              env)
  :verify-guards nil
  (b* (((tac-positive-rule-result-branch x)))
    (and (tac-ev-cube x.assums env)
         (tac-rule-conjoin-ctx-results x.ctx-results elem env))))



(define tac-eval-positive-rule-results ((x tac-positive-rule-result-branchlist-p)
                                        elem
                                        env)
  :verify-guards nil
  (if (atom x)
      nil
    (or (tac-eval-positive-rule-result-branch (car x) elem env)
        (tac-eval-positive-rule-results (cdr x) elem env)))
  ///
  (defthm tac-eval-positive-rule-results-of-append
    (equal (tac-eval-positive-rule-results (append x y) elem env)
           (or (tac-eval-positive-rule-results x elem env)
               (tac-eval-positive-rule-results y elem env)))))


(define tac-rule-conjoin-ctx-elem-inclusions ((x pseudo-term-listp)
                                              (elems true-listp) env)
  :verify-guards nil
  (if (atom elems)
      t
    (and (in (car elems) (tac-ev (car x) env))
         (tac-rule-conjoin-ctx-elem-inclusions (cdr x) (cdr elems) env)))
  ///
  (defthm tac-rule-conjoin-ctx-elem-inclusions-of-nil
    (tac-rule-conjoin-ctx-elem-inclusions x nil env)))

(define tac-rule-conjoin-ctx-result-inclusions ((x acl2::pseudo-term-list-listp)
                                                (elems true-listp)
                                                env)
  :verify-guards nil
  (if (atom x)
      t
    (and (tac-rule-conjoin-ctx-elem-inclusions (car x) elems env)
         (tac-rule-conjoin-ctx-result-inclusions (cdr x) elems env)))
  ///
  (defthm tac-rule-conjoin-ctx-result-inclusions-of-nil
    (tac-rule-conjoin-ctx-result-inclusions x nil env)))

(define tac-eval-positive-rule-result-branch-args ((x tac-positive-rule-result-branch-args-p)
                                                   (elems true-listp)
                                                   env)
  :verify-guards nil
  (b* (((tac-positive-rule-result-branch-args x)))
    (and (tac-ev-cube x.assums env)
         (tac-rule-conjoin-ctx-result-inclusions x.ctx-results elems env))))


(define tac-eval-positive-rule-result-args ((x tac-positive-rule-result-branch-argslist-p)
                                            (elems true-listp)
                                            env)
  :verify-guards nil
  (if (atom x)
      nil
    (or (tac-eval-positive-rule-result-branch-args (car x) elems env)
        (tac-eval-positive-rule-result-args (cdr x) elems env)))
  ///
  (defthm tac-eval-positive-rule-result-args-of-append
    (equal (tac-eval-positive-rule-result-args (append x y) elem env)
           (or (tac-eval-positive-rule-result-args x elem env)
               (tac-eval-positive-rule-result-args y elem env))))

  (defthmd tac-eval-positive-rule-result-args-of-no-elems
    (implies (tac-eval-positive-rule-result-args x elems env)
             (tac-eval-positive-rule-result-args x nil env))
    :hints(("Goal" :in-theory (enable tac-eval-positive-rule-result-args
                                      tac-eval-positive-rule-result-branch-args)))))


;; ------------ Variables of tac-positive-rule-result objects
(local (Defthm union-of-pseudo-var-list
         (implies (and (cmr::pseudo-var-list-p x)
                       (cmr::pseudo-var-list-p y))
                  (cmr::pseudo-var-list-p (union-equal x y)))))

(local (defthm symbol-listp-when-pseudo-var-list-p
         (implies (cmr::pseudo-var-list-p x)
                  (symbol-listp x))))

(define tac-positive-rule-result-branch-vars ((x tac-positive-rule-result-branch-p))
  :returns (vars cmr::pseudo-var-list-p)
  (b* (((tac-positive-rule-result-branch x)))
    (union-eq (cmr::termlist-vars x.assums)
              (cmr::termlist-vars x.ctx-results))))

(define tac-positive-rule-result-branchlist-vars ((x tac-positive-rule-result-branchlist-p))
  :returns (vars cmr::pseudo-var-list-p)
  (if (atom x)
      nil
    (union-eq (tac-positive-rule-result-branch-vars (car x))
              (tac-positive-rule-result-branchlist-vars (cdr x)))))

(define term-list-list-vars ((x acl2::pseudo-term-list-listp))
  :returns (vars cmr::pseudo-var-list-p)
  (if (atom x)
      nil
    (union-eq (cmr::termlist-vars (car x))
              (term-list-list-vars (cdr x)))))

(define tac-positive-rule-result-branch-args-vars ((x tac-positive-rule-result-branch-args-p))
  :returns (vars cmr::pseudo-var-list-p)
  (b* (((tac-positive-rule-result-branch-args x)))
    (union-eq (cmr::termlist-vars x.assums)
              (term-list-list-vars x.ctx-results))))

(define tac-positive-rule-result-branch-argslist-vars ((x tac-positive-rule-result-branch-argslist-p))
  :returns (vars cmr::pseudo-var-list-p)
  (if (atom x)
      nil
    (union-eq (tac-positive-rule-result-branch-args-vars (car x))
              (tac-positive-rule-result-branch-argslist-vars (cdr x)))))

;; ------------- Parsing of of tac-positive-rule-result objects



(define tac-parse-positive-rule-result-base ((x pseudo-termp))
  :returns (mv ok (ctx-res pseudo-termp))
  (pseudo-term-case x
    :fncall (if (and (eq x.fn 'pred-in-set)
                     (eq (first x.args) 'tac-w))
                (mv t (second x.args))
              (mv nil nil))
    :otherwise (mv nil nil))
  ///
  (defret <fn>-correct
    (implies ok
             (equal (in (cdr (assoc 'tac-w env))
                                 (tac-ev ctx-res env))
                    (tac-ev x env))))

  (defret <fn>-typed
    (implies (and ok
                  (subsetp (tac-termlist-types (collect-if-branches x) ctx) '(:pred)))
             (equal (tac-term-type ctx-res ctx) :set))
    :hints(("Goal" :in-theory (enable collect-if-branches
                                      tac-termlist-types)))))

                
(local (in-theory (disable acl2::pseudo-termp-opener)))

(defthm tac-ev-cube-of-append
  (equal (tac-ev-cube (append x y) a)
         (and (tac-ev-cube x a)
              (tac-ev-cube y a)))
  :hints(("Goal" :in-theory (enable tac-ev-cube))))


;; (define tac-parse-positive-rule-result-conj1 ((x pseudo-termp))
;;   :returns (mv (ok)
;;                (assums pseudo-term-listp))
;;   :measure (pseudo-term-count x)
;;   :verify-guards nil
;;   (pseudo-term-case x
;;     :fncall (if (eq x.fn 'if)
;;                 (b* (((list a b c) x.args))
;;                   (cond ((equal c ''nil)
;;                          (b* (((mv ok assums1) (tac-parse-positive-rule-result-conj1 a))
;;                               ((unless ok) (mv nil nil))
;;                               ((mv ok assums2) (tac-parse-positive-rule-result-conj1 b)))
;;                            (if ok
;;                                (mv t (append assums1 assums2))
;;                              (mv nil nil))))
;;                         (t (mv nil nil))))
;;               (mv t (list (pseudo-term-fix x))))
;;     :const (if x.val
;;                (mv t nil)
;;              (mv nil nil))
;;     :otherwise (mv nil nil))
;;   ///
;;   (verify-guards tac-parse-positive-rule-result-conj1)
;;   (defret <fn>-correct
;;     (implies ok
;;              (iff (tac-ev-cube assums env)
;;                   (tac-ev x env)))
;;     :hints(("Goal" :in-theory (enable tac-ev-cube)))))


(define tac-parse-positive-rule-result-conj ((x pseudo-termp))
  :returns (mv (ok)
               (assums pseudo-term-listp)
               (ctx-results pseudo-term-listp))
  :measure (pseudo-term-count x)
  :verify-guards nil
  (pseudo-term-case x
    :fncall (if (eq x.fn 'if)
                (b* (((list a b c) x.args))
                  (cond ((equal c ''nil)
                         (b* (((mv ok assums1 ctx-results1) (tac-parse-positive-rule-result-conj a))
                              ((unless ok) (mv nil nil nil))
                              ((mv ok assums2 ctx-results2) (tac-parse-positive-rule-result-conj b))
                              ((unless ok) (mv nil nil nil)))
                           (mv t (append assums1 assums2) (append ctx-results1 ctx-results2))))
                        (t (mv nil nil nil))))
              (b* (((mv ok ctx-res) (tac-parse-positive-rule-result-base x))
                   ((when ok) (mv t nil (list ctx-res))))
                (mv t (list (pseudo-term-fix x)) nil)))
    :const (if x.val
               (mv t nil nil)
             (mv nil nil nil))
    :otherwise (mv nil nil nil))
  ///
  (verify-guards tac-parse-positive-rule-result-conj)
  (local (in-theory (disable pred-in-set)))
  (defret <fn>-correct
    (implies ok
             (iff (tac-ev x env)
                  (and (tac-ev-cube assums env)
                       (tac-rule-conjoin-ctx-results ctx-results
                                                     (cdr (assoc 'tac-w env))
                                                     env))))
    :hints(("Goal" :in-theory (enable tac-ev-cube
                                      tac-rule-conjoin-ctx-results)
            :induct <call>))
    :rule-classes nil)

  (defret <fn>-correct-rw
    (implies ok
             (iff (tac-eval-positive-rule-result-branch
                   (tac-positive-rule-result-branch assums ctx-results)
                   (cdr (assoc 'tac-w env))
                   env)
                  (tac-ev x env)))
    :hints(("Goal" :in-theory (enable tac-eval-positive-rule-result-branch)
            :use <fn>-correct)))

  (defret <fn>-typed
    (implies (subsetp (tac-termlist-types (collect-if-branches x) ctx) '(:pred))
             (and (subsetp (tac-termlist-types assums ctx) '(:pred))
                  (subsetp (tac-termlist-types ctx-results ctx) '(:set))))
    :hints(("Goal" :in-theory (enable tac-termlist-types
                                      collect-if-branches)))))


(define tac-parse-positive-rule-result ((x pseudo-termp))
  :returns (mv (ok)
               (results tac-positive-rule-result-branchlist-p))
  :measure (pseudo-term-count x)
  :verify-guards nil
  (if (pseudo-term-case x
        :fncall (and (eq x.fn 'if)
                     (equal (first x.args) (second x.args)))
        :otherwise nil)
      (b* (((list a & c) (acl2::pseudo-term-fncall->args x))
           ((mv ok results1) (tac-parse-positive-rule-result a))
           ((unless ok) (mv nil nil))
           ((mv ok results2) (tac-parse-positive-rule-result c))
           ((unless ok) (mv nil nil)))
        (mv t (append results1 results2)))
    (b* (((mv ok assums ctx-results) (tac-parse-positive-rule-result-conj x))
         ((unless ok) (mv nil nil)))
      (mv ok (list (tac-positive-rule-result-branch assums ctx-results)))))
  ///
  (verify-guards tac-parse-positive-rule-result)
  (defret <fn>-correct
    (implies ok
             (iff (tac-eval-positive-rule-results results
                                                  (cdr (assoc 'tac-w env))
                                                  env)
                  (tac-ev x env)))
    :hints(("Goal" :in-theory (enable tac-eval-positive-rule-results)))
    :rule-classes nil)

  (defret <fn>-typed
    (implies (subsetp (tac-termlist-types (collect-if-branches x) ctx) '(:pred))
             (tac-positive-rule-result-branchlist-typed results :set ctx))
    :hints(("Goal" :in-theory (enable tac-positive-rule-result-branchlist-typed
                                      tac-positive-rule-result-branch-typed
                                      collect-if-branches)))))






(local (defthm prefixp-transitive
         (implies (and (acl2::prefixp a b)
                       (acl2::prefixp b c))
                  (acl2::prefixp a c))
         :hints(("Goal" :in-theory (enable acl2::prefixp)))))
(local (defthm prefixp-reflexive
         (acl2::prefixp x x)
         :hints(("Goal" :in-theory (enable acl2::prefixp)))))

(define apply-fn-to-arglists ((fn pseudo-fnsym-p)
                              (args acl2::pseudo-term-list-listp))
  :returns (apps pseudo-term-listp)
  (if (atom args)
      nil
    (cons (pseudo-term-fncall fn (car args))
          (apply-fn-to-arglists fn (cdr args))))
  ///
  
  (defret types-of-apply-fn-to-arglists
    (implies (and (equal rettype (tac-function-return-type fn))
                  rettype
                  (prefixp-of-all argtypes (tac-termlistlist-types args ctx))
                  (acl2::prefixp (tac-function-argument-types fn) argtypes)
                  (tac-typelist-p argtypes))
             (subsetp (tac-termlist-types apps ctx) (list rettype)))
    :hints(("Goal" :in-theory (enable tac-termlist-types
                                      prefixp-of-all
                                      tac-termlistlist-types)
            :induct <call>)
           (And stable-under-simplificationp
                '(:expand ((:free (args) (tac-term-type (pseudo-term-fncall fn args) ctx))))))))

(define apply-fn-to-result-branches ((fn pseudo-fnsym-p)
                                     (results tac-positive-rule-result-branch-argslist-p))
  :returns (apps tac-positive-rule-result-branchlist-p)
  (if (atom results)
      nil
    (cons (b* (((tac-positive-rule-result-branch-args x) (car results)))
            (tac-positive-rule-result-branch x.assums
                                             (apply-fn-to-arglists fn x.ctx-results)))
          (apply-fn-to-result-branches fn (cdr results))))
  ///
  (defret types-of-apply-fn-to-result-branches
    (implies (and (equal rettype (tac-function-return-type fn))
                  rettype
                  (tac-positive-rule-result-branch-argslist-typed results argtypes ctx)
                  (acl2::prefixp (tac-function-argument-types fn) argtypes)
                  (tac-typelist-p argtypes))
             (tac-positive-rule-result-branchlist-typed apps rettype ctx))
    :hints(("Goal" :in-theory (enable tac-positive-rule-result-branchlist-typed
                                      prefixp-of-all
                                      tac-positive-rule-result-branch-typed
                                      TAC-POSITIVE-RULE-RESULT-BRANCH-ARGS-TYPED
                                      TAC-POSITIVE-RULE-RESULT-BRANCH-ARGSLIST-TYPED)
            :induct <call>)))

  (defret types-of-apply-fn-to-result-branches-bind
    (implies (and (equal rettype (tac-function-return-type fn))
                  rettype
                  (equal argtypes (tac-function-argument-types fn))
                  (tac-positive-rule-result-branch-argslist-typed results argtypes ctx)
                  (acl2::prefixp (tac-function-argument-types fn) argtypes)
                  (tac-typelist-p argtypes))
             (tac-positive-rule-result-branchlist-typed apps rettype ctx))))

(define append-args-to-each ((firsts pseudo-term-listp) (args pseudo-term-listp))
  :returns (arglists acl2::pseudo-term-list-listp)
  (if (atom firsts)
      nil
    (cons (cons (pseudo-term-fix (car firsts)) (pseudo-term-list-fix args))
          (append-args-to-each (cdr firsts) args)))
  ///
  (defret types-of-append-args-to-each
    (implies (and (subsetp (tac-termlist-types firsts ctx) (list (car types)))
                  (acl2::prefixp (cdr types) (tac-termlist-types args ctx)))
             (prefixp-of-all types (tac-termlistlist-types arglists ctx)))
    :hints(("Goal" :in-theory (enable tac-termlistlist-types
                                      tac-termlist-types
                                      prefixp-of-all
                                      acl2::prefixp)))))

(define cons-arg-to-each ((arg pseudo-termp) (arglists acl2::pseudo-term-list-listp))
  :returns (new-arglists acl2::pseudo-term-list-listp)
  (if (atom arglists)
      nil
    (cons (cons (pseudo-term-fix arg) (pseudo-term-list-fix (car arglists)))
          (cons-arg-to-each arg (cdr arglists))))
  ///
  (defret types-of-cons-arg-to-each
    (implies (and (equal (tac-term-type arg ctx) (car types))
                  (prefixp-of-all (cdr types) (tac-termlistlist-types arglists ctx)))
             (prefixp-of-all types (tac-termlistlist-types new-arglists ctx)))
    :hints(("Goal" :in-theory (enable tac-termlistlist-types
                                      acl2::prefixp
                                      prefixp-of-all
                                      tac-termlist-types))))

  (defret tac-rule-conjoin-ctx-result-inclusions-of-cons-arg-to-each
    (equal (tac-rule-conjoin-ctx-result-inclusions
            new-arglists elems env)
           (or (atom elems)
               (atom arglists)
               (and (in (car elems) (tac-ev arg env))
                    (tac-rule-conjoin-ctx-result-inclusions arglists (cdr elems) env))))
    :hints(("Goal" :in-theory (enable tac-rule-conjoin-ctx-result-inclusions
                                      tac-rule-conjoin-ctx-elem-inclusions)))))

(define tac-positive-rule-result-branchlist-append-args
  ((branches tac-positive-rule-result-branchlist-p)
   (args pseudo-term-listp))
  :returns (new-branches tac-positive-rule-result-branch-argslist-p)
  (if (atom branches)
      nil
    (cons (B* (((tac-positive-rule-result-branch x) (car branches)))
            (tac-positive-rule-result-branch-args
             x.assums
             (append-args-to-each x.ctx-results args)))
          (tac-positive-rule-result-branchlist-append-args (cdr branches) args)))
  ///
  (defret type-of-<fn>
    (implies (and (acl2::prefixp (cdr types) (tac-termlist-types args ctx))
                  (car types)
                  (tac-positive-rule-result-branchlist-typed branches (car types) ctx)
                  (tac-typelist-p types))
             (tac-positive-rule-result-branch-argslist-typed new-branches types ctx))
    :hints(("Goal" :in-theory (enable tac-positive-rule-result-branch-argslist-typed
                                      tac-positive-rule-result-branch-args-typed
                                      tac-positive-rule-result-branchlist-typed
                                      tac-positive-rule-result-branch-typed
                                      prefixp-of-all
                                      tac-typelist-fix))))

  (defret type-of-<fn>-no-types
    (implies (tac-positive-rule-result-branchlist-typed branches nil ctx)
             (tac-positive-rule-result-branch-argslist-typed new-branches nil ctx))
    :hints(("Goal" :in-theory (enable tac-positive-rule-result-branch-argslist-typed
                                      tac-positive-rule-result-branch-args-typed
                                      tac-positive-rule-result-branchlist-typed
                                      tac-positive-rule-result-branch-typed
                                      prefixp-of-all
                                      tac-typelist-fix)))))

(define tac-positive-rule-result-branch-argslist-cons-arg
  ((arg pseudo-termp)
   (branches tac-positive-rule-result-branch-argslist-p))
  :returns (new-branches tac-positive-rule-result-branch-argslist-p)
  (if (atom branches)
      nil
    (cons (B* (((tac-positive-rule-result-branch-args x) (car branches)))
            (tac-positive-rule-result-branch-args
             x.assums
             (cons-arg-to-each arg x.ctx-results)))
          (tac-positive-rule-result-branch-argslist-cons-arg arg (cdr branches))))
  ///
  (defret type-of-<fn>
    (implies (and (equal (tac-term-type arg ctx) (car types))
                  (tac-positive-rule-result-branch-argslist-typed branches (cdr types) ctx))
             (tac-positive-rule-result-branch-argslist-typed new-branches types ctx))
    :hints(("Goal" :in-theory (enable tac-positive-rule-result-branch-argslist-typed
                                      tac-positive-rule-result-branch-args-typed
                                      tac-positive-rule-result-branchlist-typed
                                      tac-positive-rule-result-branch-typed))))

  (defret type-of-<fn>-no-types
    (implies (tac-positive-rule-result-branch-argslist-typed branches nil ctx)
             (tac-positive-rule-result-branch-argslist-typed new-branches nil ctx))
    :hints(("Goal" :in-theory (enable tac-positive-rule-result-branch-argslist-typed
                                      tac-positive-rule-result-branch-args-typed
                                      tac-positive-rule-result-branchlist-typed
                                      tac-positive-rule-result-branch-typed))))

  (defret tac-eval-positive-rule-result-args-of-<fn>
    (iff (tac-eval-positive-rule-result-args new-branches elems env)
         (if (atom elems)
             (tac-eval-positive-rule-result-args branches nil env)
           (and
            (tac-eval-positive-rule-result-args branches (cdr elems) env)
            (or (tac-eval-positive-rule-result-args branches nil env)
                (in (car elems) (tac-ev arg env))))))
    :hints(("Goal" :in-theory (enable tac-eval-positive-rule-result-args
                                      tac-eval-positive-rule-result-branch-args
                                      TAC-RULE-CONJOIN-CTX-RESULT-INCLUSIONS
                                      tac-eval-positive-rule-result-args-of-no-elems)))))

(define tac-try-basic-rewrites ((rules cmr::rewritelist-p)
                                (fn pseudo-fnsym-p)
                                (args pseudo-term-listp))
  :returns (mv rewrittenp (result pseudo-termp))
  (if (atom rules)
      (mv nil nil)
    (b* (((mv ok rhs subst) (tac-rewrite-apply-rule (car rules) fn args))
         ((when ok) (mv t (cmr::term-subst-strict rhs subst))))
      (tac-try-basic-rewrites (cdr rules) fn args)))
  ///
  (defret <fn>-correct
    (implies (and rewrittenp
                  (tac-ev-theorem-rewritesp rules)
                  (tac-rewrites-hyps-ok rules)
                  (tac-typed-env-p env ctx)
                  (tac-term-type (pseudo-term-fncall fn args) ctx))
             (equal (tac-ev result env)
                    (tac-ev (pseudo-term-fncall fn args) env)))
    :hints(("Goal" :in-theory (enable tac-ev-theorem-rewritesp
                                      tac-rewrites-hyps-ok))))

  (defret <fn>-preserves-type
    (implies (and rewrittenp
                  (tac-rewrites-rhs-preserved rules)
                  (equal type (tac-term-type (pseudo-term-fncall fn args) ctx))
                  type)
             (equal (tac-term-type result ctx) type))
    :hints(("Goal" :in-theory (enable tac-rewrites-rhs-preserved)))))



(include-book "centaur/meta/subst-vars" :dir :system)

(define tac-rewrite-pred-apply-rule ((rule cmr::rewrite-p)
                                     (fn pseudo-fnsym-p)
                                     (args pseudo-term-listp))
  :returns (mv ok
               (rhs pseudo-termp)
               (subst cmr::pseudo-term-subst-p))
  (b* (((cmr::rewrite rule))
       ((unless (and (or (eq rule.equiv 'equal)
                         (eq rule.equiv 'iff))
                     (pseudo-term-case rule.lhs :fncall)))
        (mv nil nil nil))
       ((pseudo-term-fncall rule.lhs))
       ((unless (eq rule.lhs.fn (pseudo-fnsym-fix fn)))
        (mv nil nil nil))
       ((mv ok subst) (cmr::termlist-unify-strict rule.lhs.args args nil))
       ((unless ok)
        (mv nil nil nil)))
    (mv t rule.rhs subst))
  ///
  (local (in-theory (enable tac-ev-of-fncall-args)))
  
  (local (defthm tac-ev-list-equal-of-termlist-subst-strict
           (implies (equal (pseudo-term-list-fix x)
                           (cmr::termlist-subst-strict pat subst))
                    (equal (tac-ev-lst x a)
                           (tac-ev-lst pat (tac-ev-alist subst a))))
           :hints (("goal" :use ((:instance tac-ev-lst-of-pseudo-term-list-fix-x
                                  (x x) (a a)))
                    :in-theory (disable tac-ev-lst-of-pseudo-term-list-fix-x
                                        tac-ev-lst-pseudo-term-list-equiv-congruence-on-x)))))
  
  (defret <fn>-correct
    (implies (and ok
                  (tac-ev-theoremp (cmr::rewrite-term rule))
                  (tac-rewrite-hyps-ok rule)
                  (tac-typed-env-p env ctx)
                  (tac-term-type (pseudo-term-fncall fn args) ctx))
             (iff (tac-ev rhs (tac-ev-alist subst env))
                  (tac-ev (pseudo-term-fncall fn args) env)))
    :hints(("Goal" :in-theory (e/d (cmr::rewrite-term)
                                   (tac-rewrite-hyps-ok-necc))
            :expand ((CMR::TERM-UNIFY-STRICT (CMR::REWRITE->LHS RULE)
                                             (pseudo-term-fncall fn args) NIL))
            :use ((:instance tac-ev-falsify
                   (a (tac-ev-alist (mv-nth 1 (cmr::termlist-unify-strict
                                               (pseudo-term-call->args (cmr::rewrite->lhs rule))
                                               args nil))
                                    env))
                   (x (cmr::rewrite-term rule)))
                  (:instance tac-rewrite-hyps-ok-necc
                   (x (pseudo-term-fncall fn args)))))))

  (defret <fn>-preserves-type
    (implies (and ok
                  (tac-pred-rewrite-rhs-typed rule)
                  (equal (tac-term-type (pseudo-term-fncall fn args) ctx) :pred))
             (subsetp (tac-termlist-types (collect-if-branches
                                           (cmr::term-subst-strict rhs subst))
                                          ctx) '(:pred)))
    :hints (("goal" :use ((:instance tac-pred-rewrite-rhs-typed-necc
                           (x (pseudo-term-fncall fn args))))
            :expand ((CMR::TERM-UNIFY-STRICT (CMR::REWRITE->LHS RULE)
                                             (pseudo-term-fncall fn args) NIL))
            :in-theory (disable tac-pred-rewrite-rhs-typed-necc))))

  (defret term-subst-vars-of-<fn>
    (implies (not (member v (cmr::termlist-vars args)))
             (not (member v (cmr::term-subst-vars subst))))))




(defsection tac-pred-rewrite-rhs-vars-subset
  (defun-sk tac-pred-rewrite-rhs-vars-subset (rule)
    (forall (v x)
            (b* (((mv ok1 rhs subst) (tac-rewrite-pred-apply-rule rule 'pred-in-set (list 'tac-w x)))
                 (res-term (cmr::term-subst-strict rhs subst))
                 ((mv ok2 result) (tac-parse-positive-rule-result res-term)))
              (implies (and (not (member v (cmr::term-vars x)))
                            ok1 ok2)
                       (not (member v (tac-positive-rule-result-branchlist-vars result))))))
    :rewrite :direct)

  (in-theory (disable tac-pred-rewrite-rhs-vars-subset)))



(define tac-pred-rewrites-rhs-vars-subset (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (tac-pred-rewrite-rhs-vars-subset (car rules))
         (tac-pred-rewrites-rhs-vars-subset (cdr rules))))
  ///
  (local (defthm car-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (car x) a))))
  (local (defthm cdr-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (cdr x) b))))

  (local (defthm member-tac-positive-rule-result-branchlist-vars-of-cons
           (iff (member v (tac-positive-rule-result-branchlist-vars (cons a b)))
                (or (member v (tac-positive-rule-result-branch-vars a))
                    (member v (tac-positive-rule-result-branchlist-vars b))))
           :hints(("Goal" :in-theory (enable tac-positive-rule-result-branchlist-vars)))))

  (local (defthm tac-positive-rule-result-branch-vars-of-tac-positive-rule-result-branch
           (equal (tac-positive-rule-result-branch-vars
                   (tac-positive-rule-result-branch assums ctx-results))
                  (union-equal (cmr::termlist-vars assums)
                               (cmr::termlist-vars ctx-results)))
           :hints(("Goal" :in-theory (enable tac-positive-rule-result-branch-vars)))))

  (local (defthm termlist-vars-of-cons
           (equal (cmr::termlist-vars (cons a b))
                  (union-equal (cmr::termlist-vars b)
                               (cmr::term-vars a)))
           :hints(("Goal" :in-theory (enable cmr::termlist-vars)))))
  (local (defthm term-vars-when-pseudo-term-fncall
           (implies (pseudo-term-case x :fncall)
                    (equal (cmr::term-vars x)
                           (cmr::termlist-vars (pseudo-term-call->args x))))
           :hints(("Goal" :expand ((cmr::term-vars x))))))
  
  (defthm tac-pred-rewrites-rhs-vars-subset-of-tac-positive-normalize-rules
    (tac-pred-rewrites-rhs-vars-subset (tac-positive-normalize-rules))
    :hints (("goal" :expand ((:free (x) (tac-pred-rewrite-rhs-vars-subset x))
                             (:free (a b) (tac-pred-rewrites-rhs-vars-subset (cons a b))))
             :in-theory (e/d (cmr::term-subst-strict
                              tac-termlist-types
                              tac-rewrite-pred-apply-rule
                              tac-parse-positive-rule-result
                              tac-parse-positive-rule-result-conj
                              tac-parse-positive-rule-result-base
                              collect-if-branches
                              cmr::termlist-subst-strict
                              cmr::equal-of-pseudo-term-fncall
                              (tac-positive-normalize-rules))
                             (tac-pred-rewrite-rhs-vars-subset-necc))
             :do-not-induct t))))




(defthm tac-term-type-when-function-return-type
  (implies (and (tac-term-type x ctx)
                (pseudo-term-case x :fncall))
           (equal (tac-term-type x ctx)
                  (tac-function-return-type (pseudo-term-call->fn x))))
  :hints(("Goal" :expand ((tac-term-type x ctx)))))




(defthm tac-termlist-types-when-term-type
  (implies (and (tac-term-type x ctx)
                (pseudo-term-case x :fncall))
           (acl2::prefixp (tac-function-argument-types (pseudo-term-fncall->fn x))
                          (tac-termlist-types (pseudo-term-call->args x) ctx)))
  :hints(("Goal" :expand ((tac-term-type x ctx)))))

(defthm tac-ev-when-agree-on-term-vars
  (implies (cmr::eval-alists-agree (cmr::term-vars x) a b)
           (equal (equal (tac-ev x a)
                         (tac-ev x b))
                  t))
  :hints (("goal" :use ((:instance (:functional-instance
                                    cmr::base-ev-when-agree-on-term-vars
                                    (cmr::base-ev tac-ev)
                                    (cmr::base-ev-list tac-ev-lst))
                         (x x) (a a) (b b))))))

(defthm tac-ev-lst-when-agree-on-termlist-vars
  (implies (cmr::eval-alists-agree (cmr::termlist-vars x) a b)
           (equal (equal (tac-ev-lst x a)
                         (tac-ev-lst x b))
                  t))
  :hints (("goal" :use ((:instance (:functional-instance
                                    cmr::base-ev-list-when-agree-on-termlist-vars
                                    (cmr::base-ev tac-ev)
                                    (cmr::base-ev-list tac-ev-lst))
                         (x x) (a a) (b b))))))
 

(define tac-try-pred-rewrite ((rule cmr::rewrite-p)
                              (args pseudo-term-listp))
  :returns (mv rewrittenp (results tac-positive-rule-result-branchlist-p))
  (b* (((mv rewrittenp rhs subst)
        (tac-rewrite-pred-apply-rule rule 'pred-in-set args))
       ((unless rewrittenp) (mv nil nil)))
    (tac-parse-positive-rule-result (cmr::term-subst-strict rhs subst)))
  ///
  (defthm tac-typed-env-p-aux-of-add-var
    (implies (and (tac-typed-env-p-aux vars env ctx)
                  (tac-typed-val-p val type))
             (tac-typed-env-p-aux vars
                                  (cons (cons var val) env)
                                  (cons (cons var type) ctx)))
    :hints(("Goal" :in-theory (enable tac-typed-env-p-aux))))
  
  (defthm tac-typed-env-p-of-add-var
    (implies (and (tac-typed-env-p env ctx)
                  (tac-typed-val-p val type))
             (tac-typed-env-p (cons (cons var val) env)
                              (cons (cons var type) ctx)))
    :hints(("Goal" :in-theory (enable tac-typed-env-p
                                      tac-typed-env-p-aux
                                      acl2::alist-keys))))

  (local (defthm eval-alists-agree-of-cons-non-member
           (implies (not (member v vars))
                    (acl2::eval-alists-agree vars (cons (cons v val) env) env))
           :hints(("Goal" :in-theory (enable acl2::eval-alists-agree-by-bad-guy)))))

  (local (defthm tac-ev-of-add-unused-var
           (implies (not (member-equal v (cmr::term-vars x)))
                    (equal (tac-ev x (cons (cons v val) env))
                           (tac-ev x env)))
           :hints(("Goal" :in-theory (enable tac-ev-when-agree-on-term-vars
                                             acl2::eval-alists-agree-by-bad-guy)))))

  (local (defthm tac-ev-cube-of-add-unused-var
           (implies (not (member-equal v (cmr::termlist-vars x)))
                    (equal (tac-ev-cube x (cons (cons v val) env))
                           (tac-ev-cube x env)))
           :hints(("Goal" :in-theory (enable tac-ev-cube)
                   :induct (len x)
                   :expand ((cmr::termlist-vars x))))))

  (local (defthm tac-ev-alist-of-add-unused-var
           (implies (not (member-equal v (cmr::term-subst-vars x)))
                    (equal (tac-ev-alist x (cons (cons v val) env))
                           (tac-ev-alist x env)))
           :hints(("Goal" :in-theory (enable tac-ev-alist)
                   :induct (len x)
                   :expand ((cmr::term-subst-vars x))))))

  (local (defthm tac-rule-conjoin-ctx-results-of-add-unused-var
           (implies (not (member-equal v (cmr::termlist-vars x)))
                    (equal (tac-rule-conjoin-ctx-results x elem (cons (cons v val) env))
                           (tac-rule-conjoin-ctx-results x elem env)))
           :hints(("Goal" :in-theory (enable tac-rule-conjoin-ctx-results)
                   :induct (len x)
                   :expand ((cmr::termlist-vars x))))))

  (local (defthm tac-eval-positive-rule-result-branch-of-add-unused-var
           (implies (not (member-equal v (tac-positive-rule-result-branch-vars x)))
                    (equal (tac-eval-positive-rule-result-branch x elem (cons (cons v val) env))
                           (tac-eval-positive-rule-result-branch x elem env)))
           :hints(("Goal" :in-theory (enable tac-eval-positive-rule-result-branch
                                             tac-positive-rule-result-branch-vars)))))

  (local (defthm tac-eval-positive-rule-result-branchlist-of-add-unused-var
           (implies (not (member-equal v (tac-positive-rule-result-branchlist-vars x)))
                    (equal (tac-eval-positive-rule-results x elem (cons (cons v val) env))
                           (tac-eval-positive-rule-results x elem env)))
           :hints(("Goal" :in-theory (enable tac-eval-positive-rule-results
                                             tac-positive-rule-result-branchlist-vars)))))
  
  (defret <fn>-correct
    :pre-bind ((args (list 'tac-w x)))
    (implies (and rewrittenp
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (tac-ev-theoremp (cmr::rewrite-term rule))
                  (tac-rewrite-hyps-ok rule)
                  (tac-typed-env-p env ctx)
                  (equal (tac-term-type x ctx) :set)
                  (tac-pred-rewrite-rhs-vars-subset rule)
                  (event-p elem))
             (iff (tac-eval-positive-rule-results results elem env)
                  (in elem (tac-ev x env))))
    :hints (("goal" :use ((:instance tac-parse-positive-rule-result-correct
                           (x (b* (((mv & rhs subst) (tac-rewrite-pred-apply-rule
                                                      rule 'pred-in-set (list 'tac-w x))))
                                (cmr::term-subst-strict rhs subst)))
                           (env (cons (Cons 'tac-w elem) env)))
                          (:instance TAC-REWRITE-PRED-APPLY-RULE-CORRECT
                           (fn 'pred-in-set) (args (list 'tac-w x))
                           (env (cons (cons 'tac-w elem) env))
                           (ctx (cons (cons 'tac-w :event) ctx))))
             :expand ((tac-typed-val-p elem :event))
             :do-not-induct t))
    :otf-flg t)

  (local
   (defthm tac-positive-rule-result-branch-typed-of-add-unused-var
     (implies (not (member-equal v (tac-positive-rule-result-branch-vars x)))
              (equal (tac-positive-rule-result-branch-typed x type (cons (cons v vtype) ctx))
                     (tac-positive-rule-result-branch-typed x type ctx)))
     :hints(("Goal" :in-theory (enable tac-positive-rule-result-branch-typed
                                       tac-positive-rule-result-branch-vars)))))

  (local
   (defthm tac-positive-rule-result-branchlist-typed-of-add-unused-var
     (implies (not (member-equal v (tac-positive-rule-result-branchlist-vars x)))
              (equal (tac-positive-rule-result-branchlist-typed x type (cons (cons v vtype) ctx))
                     (tac-positive-rule-result-branchlist-typed x type ctx)))
     :hints(("Goal" :in-theory (enable tac-positive-rule-result-branchlist-typed
                                       tac-positive-rule-result-branchlist-vars)))))

  (defret <fn>-preserves-type
    :pre-bind ((args (list 'tac-w x)))
    (implies (and rewrittenp
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (tac-pred-rewrite-rhs-typed rule)
                  (equal (tac-term-type x ctx) :set)
                  (tac-pred-rewrite-rhs-vars-subset rule))
             (tac-positive-rule-result-branchlist-typed results :set ctx))
    :hints (("goal" :use ((:instance tac-parse-positive-rule-result-typed
                           (x (b* (((mv & rhs subst) (tac-rewrite-pred-apply-rule
                                                      rule 'pred-in-set (list 'tac-w x))))
                                (cmr::term-subst-strict rhs subst)))
                           (ctx (cons (Cons 'tac-w :event) ctx)))
                          (:instance TAC-REWRITE-PRED-APPLY-RULE-preserves-type
                           (fn 'pred-in-set) (args (list 'tac-w x))
                           (ctx (cons (cons 'tac-w :event) ctx))))
             :in-theory (disable tac-parse-positive-rule-result-typed
                                 tac-rewrite-pred-apply-rule-preserves-type)
             :do-not-induct t))
    :otf-flg t))

(define tac-try-pred-rewrites ((rules cmr::rewritelist-p)
                               (args pseudo-term-listp))
  :returns (mv rewrittenp (results tac-positive-rule-result-branchlist-p))
  (if (atom rules)
      (mv nil nil)
    (b* (((mv ok results) (tac-try-pred-rewrite (car rules) args))
         ((when ok) (mv ok results)))
      (tac-try-pred-rewrites (cdr rules) args)))
  ///
  (defret <fn>-correct
    :pre-bind ((args (list 'tac-w x)))
    (implies (and rewrittenp
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (tac-ev-theorem-rewritesp rules)
                  (tac-rewrites-hyps-ok rules)
                  (tac-typed-env-p env ctx)
                  (equal (tac-term-type x ctx) :set)
                  (tac-pred-rewrites-rhs-vars-subset rules)
                  (event-p elem))
             (iff (tac-eval-positive-rule-results results elem env)
                  (in elem (tac-ev x env))))
    :hints(("Goal" :in-theory (enable tac-ev-theorem-rewritesp
                                      tac-rewrites-hyps-ok
                                      tac-pred-rewrites-rhs-vars-subset)
            :induct (len rules)
            :expand ((:free (args) <call>)))))

  (defret <fn>-preserves-type
    :pre-bind ((args (list 'tac-w x)))
    (implies (and rewrittenp
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (tac-pred-rewrites-rhs-typed rules)
                  (equal (tac-term-type x ctx) :set)
                  (tac-pred-rewrites-rhs-vars-subset rules))
             (tac-positive-rule-result-branchlist-typed results :set ctx))
    :hints(("Goal" :in-theory (enable tac-pred-rewrites-rhs-typed
                                      tac-pred-rewrites-rhs-vars-subset)
            :induct (len rules)
            :expand ((:free (args) <call>))))))





(define tac-try-pred-rewrites-on-pred-in-set ((x pseudo-termp)
                                              (rules cmr::rewritelist-p))
  :returns (mv rewrittenp (results tac-positive-rule-result-branchlist-p))
  (tac-try-pred-rewrites rules (list 'tac-w x))
  ///
  (defret <fn>-correct
    (implies (and rewrittenp
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (tac-ev-theorem-rewritesp rules)
                  (tac-rewrites-hyps-ok rules)
                  (tac-typed-env-p env ctx)
                  (equal (tac-term-type x ctx) :set)
                  (tac-pred-rewrites-rhs-vars-subset rules)
                  (event-p elem))
             (iff (tac-eval-positive-rule-results results elem env)
                  (in elem (tac-ev x env))))
    :hints(("Goal" :in-theory (enable tac-ev-theorem-rewritesp
                                      tac-rewrites-hyps-ok
                                      tac-pred-rewrites-rhs-vars-subset)
            :induct (len rules)
            :expand ((:free (args) <call>)))))

  (defret <fn>-preserves-type
    (implies (and rewrittenp
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (tac-pred-rewrites-rhs-typed rules)
                  (equal (tac-term-type x ctx) :set)
                  (tac-pred-rewrites-rhs-vars-subset rules))
             (tac-positive-rule-result-branchlist-typed results :set ctx))
    :hints(("Goal" :in-theory (enable tac-pred-rewrites-rhs-typed
                                      tac-pred-rewrites-rhs-vars-subset)
            :induct (len rules)
            :expand ((:free (args) <call>))))))


(local (defthm equal-pseudo-fnsym-fix-forward
         (implies (equal (pseudo-fnsym-fix x) y)
                  (pseudo-fnsym-equiv x y))
         :rule-classes :forward-chaining))

(define tac-context-fn-p ((x pseudo-fnsym-p))
  (and (member-eq (pseudo-fnsym-fix x) '(setimage setpreimage setintersect
                                                  relidentity relcompose relinverse relprod relintersect))
       t)
  ///
  (defthm tac-function-return-type-when-tac-context-fn-p
    (implies (tac-context-fn-p x)
             (tac-function-return-type x))))

(defines tac-positive-apply-rule-in-context
  (define tac-positive-apply-rule-in-context ((x pseudo-termp)
                                              (assums pseudo-term-listp)
                                              (ruleset cmr::rewritelist-p))
    ;; Positive rules replace the term in its context, perhaps splitting into
    ;; two cases (with the same context) [e.g., union or star rules] or perhaps
    ;; adding a new assumption [e.g., intersection or product rules].  We
    ;; generalize this slightly and allow both added assumptions and a list
    ;; of contextual cases.
    :returns (mv successp
                 (results tac-positive-rule-result-branchlist-p))
    :measure (pseudo-term-count x)
    :verify-guards nil
    (b* (((unless (pseudo-term-case x :fncall))
          (mv nil nil))
         ((pseudo-term-fncall x))
         (rettype (tac-function-return-type x.fn))
         ((unless (member-eq rettype '(:set :rel)))
          (mv nil nil))
         ((mv rewrittenp result)
          (pseudo-term-case x
            :fncall
            (tac-try-basic-rewrites (tac-rewrites) x.fn x.args)
            :otherwise (mv nil nil)))
         ((when rewrittenp)
          (mv t (list (tac-positive-rule-result-branch nil (list result)))))
         ((mv rewrittenp result)
          (if (eq rettype :set)
              ;; note: important that x not contain variable tac-w
              (tac-try-pred-rewrites-on-pred-in-set x ruleset)
            (mv nil nil)))
         ((when rewrittenp) (mv t result))
         ((unless (tac-context-fn-p x.fn))
          (mv nil nil))
         ((mv successp results-args)
          (tac-positive-apply-rule-in-context-args
           (tac-function-argument-types x.fn) x.args assums ruleset))
         ((when successp)
          (mv t (apply-fn-to-result-branches x.fn results-args))))
      (mv nil nil)))

  (define tac-positive-apply-rule-in-context-args ((types tac-typelist-p)
                                                   (x pseudo-term-listp)
                                                   (assums pseudo-term-listp)
                                                   (ruleset cmr::rewritelist-p))
    :measure (pseudo-term-list-count x)
    :returns (mv successp
                 (results tac-positive-rule-result-branch-argslist-p))
    (b* (((when (or (atom types)
                    (atom x)))
          (mv nil nil))
         ((mv successp results) (tac-positive-apply-rule-in-context (car x) assums ruleset))
         ((when successp)
          (mv t (tac-positive-rule-result-branchlist-append-args results (cdr x))))
         ((mv successp results) (tac-positive-apply-rule-in-context-args (cdr types) (cdr x) assums ruleset))
         ((when successp)
          (mv t (tac-positive-rule-result-branch-argslist-cons-arg (car x) results))))
      (mv nil nil)))
  ///
  (verify-guards tac-positive-apply-rule-in-context)
  ;; (local (defun-sk preserves-type-list-cond (x results ctx)
  ;;          (forall types
  ;;                  (implies (and (tac-typelist-p types)
  ;;                                (not (member-equal nil types))
  ;;                                (acl2::prefixp types (tac-termlist-types x ctx)))
  ;;                           (tac-positive-rule-result-branch-argslist-typed
  ;;                            results types ctx)))
  ;;          :rewrite :direct))
  ;; (local (in-theory (disable preserves-type-list-cond)))
  
  (std::defret-mutual <fn>-preserves-type-lemma
    (defret <fn>-preserves-type-lemma
      (implies (and (tac-pred-rewrites-rhs-typed ruleset)
                    (tac-pred-rewrites-rhs-vars-subset ruleset)
                    (tac-term-type x ctx)
                    (not (member-equal 'tac-w (cmr::term-vars x)))
                    successp)
               (tac-positive-rule-result-branchlist-typed results (tac-term-type x ctx) ctx))
      :hints ('(:expand (<call>
                         (cmr::term-vars x))
                :in-theory (enable tac-positive-rule-result-branchlist-typed
                                   TAC-POSITIVE-RULE-RESULT-BRANCH-TYPED
                                   tac-termlist-types)))
      :fn tac-positive-apply-rule-in-context)
    (defret <fn>-preserves-type
      (implies (and (tac-pred-rewrites-rhs-typed ruleset)
                    (tac-pred-rewrites-rhs-vars-subset ruleset)
                    (tac-typelist-p types)
                    (not (member-equal nil types))
                    (acl2::prefixp types (tac-termlist-types x ctx))
                    (not (member-equal 'tac-w (cmr::termlist-vars x)))
                    successp)
               (tac-positive-rule-result-branch-argslist-typed
                results types ctx))
      :hints ('(:expand (<call>
                         (:free (a b c) (acl2::prefixp a (cons b c)))
                         (cmr::termlist-vars x))
                :in-theory (enable tac-positive-rule-result-branch-argslist-typed
                                   tac-termlist-types
                                   acl2::prefixp))
              ;; (and stable-under-simplificationp
              ;;      `(:expand (,(car (last clause))
              ;;                 (:free (a b c) (acl2::prefixp a (cons b c))))))
              )
      :fn tac-positive-apply-rule-in-context-args))


  (defret <fn>-preserves-type
    (implies (and (tac-pred-rewrites-rhs-typed ruleset)
                  (tac-pred-rewrites-rhs-vars-subset ruleset)
                  (equal type (tac-term-type x ctx))
                  type
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  successp)
             (tac-positive-rule-result-branchlist-typed results type ctx))
    :fn tac-positive-apply-rule-in-context)


  (defun-sk in-iff-tac-eval-positive-rule-results (x results env)
    (forall elem
            (iff (tac-eval-positive-rule-results results elem env)
                 (in elem (tac-ev x env))))
    :rewrite :direct)

  (defun elems-in-list (elems sets)
    (if (atom elems)
        t
      (And (in (car elems) (car sets))
           (elems-in-list (cdr elems) (cdr sets)))))
  
  (defun-sk elems-in-list-iff-tac-eval-positive-rule-result-args (x results env)
    (forall elems
            (iff (tac-eval-positive-rule-result-args results elems env)
                 (elems-in-list elems (tac-ev x env))))
    :rewrite :direct)
  
  (std::defret-mutual <fn>-eval-lemma
    (defret <fn>-eval-correct
      (implies (and (member-equal (tac-term-type x ctx) '(:set :rel))
                    (tac-typed-env-p env ctx)
                    (tac-ev-theorem-rewritesp ruleset)
                    (tac-rewrites-hyps-ok ruleset)
                    (tac-pred-rewrites-rhs-typed ruleset)
                    (tac-pred-rewrites-rhs-vars-subset rules)
                    (not (member-equal 'tac-w (cmr::term-vars x)))
                    successp)
               (and (member-equal (tac-term-type x ctx) '(:set :rel))
                    (in-iff-tac-eval-positive-rule-results x results env)))
      :hints ((and stable-under-simplificationp
                   (eq (caar (last clause)) 'in-iff-tac-eval-positive-rule-results)
                   `(:expand (,(car (last clause)))))
              (and stable-under-simplificationp
                   '(:expand (<call>))))
      :fn tac-positive-apply-rule-in-context)

    (defret <fn>-eval-correct
      (implies (and (tac-typed-env-p env ctx)
                    (tac-ev-theorem-rewritesp ruleset)
                    (tac-rewrites-hyps-ok ruleset)
                    (tac-pred-rewrites-rhs-typed ruleset)
                    (tac-pred-rewrites-rhs-vars-subset rules)
                    (tac-typelist-p types)
                    (not (member-equal nil types))
                    (acl2::prefixp types (tac-termlist-types x ctx))
                    (not (member-equal 'tac-w (cmr::termlist-vars x)))
                    successp)
               (elems-in-list-iff-tac-eval-positive-rule-result-args x results env))
      :hints ((and stable-under-simplificationp
                   (eq (caar (last clause)) 'elems-in-list-iff-tac-eval-positive-rule-result-args)
                   `(:expand (,(car (last clause)))))
              (and stable-under-simplificationp
                   '(:expand (<call>))))
      :fn tac-positive-apply-rule-in-context-args)))
         
                           

  

(define tac-positive-rule-result-disjoin-cases ((x pseudo-term-listp) env)
  :verify-guards nil
  (if (atom x)
      nil
    (or (pred-in-set (cdr (assoc-eq 'tac-w env))
                     (tac-ev (car x) env))
        (tac-positive-rule-result-disjoin-cases (cdr x) env))))





(define parse-conjunction ((x pseudo-termp))
  :returns (conj pseudo-term-listp)
  :measure (acl2-count (pseudo-term-fix x))
  (b* ((x (pseudo-term-fix x)))
    (case-match x
      (('if a b ''nil) (append (parse-conjunction a) (parse-conjunction b)))
      (& (list x))))
  ///
  (defret tac-ev-cube-of-<fn>
    (iff (tac-ev-cube conj a)
         (tac-ev x a))
    :hints(("Goal" :in-theory (enable tac-ev-cube)
            :induct <call>
            :expand (<call>))
           (and stable-under-simplificationp
                '(:use ((:instance TAC-EV-OF-PSEUDO-TERM-FIX-X (x x) (a a)))
                  :in-theory (disable tac-ev-of-pseudo-term-fix-x
                                      tac-ev-pseudo-term-equiv-congruence-on-x))))))


(define tac-ev-dnf ((x acl2::pseudo-term-list-listp) (env alistp))
  :verify-guards nil
  (if (atom x)
      nil
    (or (tac-ev-cube (car x) env)
        (tac-ev-dnf (cdr x) env)))
  ///
  (defthm tac-ev-dnf-of-append
    (equal (tac-ev-dnf (append x y) env)
           (or (tac-ev-dnf x env)
               (tac-ev-dnf y env)))))

(define parse-disjunction-of-conjunctions ((x pseudo-termp))
  :returns (disj acl2::pseudo-term-list-listp)
  :measure (acl2-count (pseudo-term-fix x))
  (b* ((x (pseudo-term-fix x)))
    (case-match x
      (('if a a b) (append (parse-disjunction-of-conjunctions a)
                           (parse-disjunction-of-conjunctions b)))
      (& (list (parse-conjunction x)))))
  ///
  (defret tac-ev-dnf-of-<fn>
    (iff (tac-ev-dnf disj a)
         (tac-ev x a))
    :hints(("Goal" :in-theory (enable tac-ev-dnf)
            :induct <call>
            :expand (<call>))
           (and stable-under-simplificationp
                '(:use ((:instance TAC-EV-OF-PSEUDO-TERM-FIX-X (x x) (a a)))
                  :in-theory (disable tac-ev-of-pseudo-term-fix-x
                                      tac-ev-pseudo-term-equiv-congruence-on-x))))))






;; Suppose we have an assumption (cube of literals which we want to disprove)
;; in this relational language that has some star operators in positive (set
;; non-emptiness) literals. The outermost star operators in these positive
;; literals may be replaced by fixed repetition operators r{n_i} such that the
;; repetition counts n_i are minimal, i.e. if they are all replaced by lesser
;; or equal values (with at least one lesser) then the assumption is
;; unsatisfiable.  (The same can't be done with inner star operators because
;; they may need different numbers of repetitions in different repetition of
;; the outer operator.)



(define tac-cube-p ((x pseudo-term-listp) (ctx type-ctx-p))
  (if (atom x)
      t
    (and (pred-term-p (car x) ctx)
         (tac-cube-p (cdr x) ctx))))





(encapsulate nil
  (defun-sk tac-ev*-cube-satisfiable (x)
    (exists (ctx env)
            (and (tac-cube-p x ctx)
                 (tac-typed-env-p env ctx) 
                 (tac-ev*-cube x env))))

  (in-theory (disable tac-ev*-cube-satisfiable)))












(define relstar-unrolled ((n natp) (x relation-p))
  :returns (star relation-p)
  (relstar-bounded (max 0 (- (relstar-bound x) (lnfix n))) x)
  ///
  (defret event-rel-p-of-<fn>
    (implies (event-rel-p x)
             (event-rel-p star)))

  (defretd relstar-in-terms-of-unrolled
    (implies (event-rel-p x)
             (equal (relstar x)
                    (relstar-unrolled 0 x)))
    :hints(("Goal" :in-theory (e/d (relstar-in-terms-of-bounded)
                                   (relstar)))))

  (defretd in-relstar-unrolled
    (iff (in pair (relstar-unrolled n x))
         (or (in pair (relidentity (universe)))
             (and (< (nfix n) (relstar-bound x))
                  (in pair (compose x (relstar-unrolled (1+ (nfix n)) x))))))
    :hints(("Goal" :expand ((relstar-bounded (relstar-bound x) x)
                            (relstar-bounded (+ (- n) (relstar-bound x)) x)
                            (relstar-bounded 0 x)))))

  (defthmd relstar-unrolled-redef
    (equal (relstar-unrolled n x)
           (if (< (nfix n) (relstar-bound x))
               (union (relidentity (universe))
                      (compose x (relstar-unrolled (1+ (nfix n)) x)))
             (relidentity (universe))))
    :hints (("goal" :in-theory (e/d (set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-relstar-unrolled)
                                    (relstar-unrolled)))
            (SET::PICK-A-POINT-SUBSET-HINT ID acl2::CLAUSE
                                           WORLD STABLE-UNDER-SIMPLIFICATIONP))
    :rule-classes ((:definition :controller-alist ((relstar-unrolled t nil)))))

  (defthmd relstar-unrolled-of-gte-bound
    (implies (<= (relstar-bound x) (nfix n))
             (equal (relstar-unrolled n x)
                    (id-relation (universe))))
    :hints(("Goal" :in-theory (enable relstar-bounded)))))
                         









(thm
 (implies (pred-nonempty
           (relimage (singleton e)
                     (relintersect
                      (relplus
                       (relunion (relcompose (relidentity r)
                                             (relcompose poloc
                                                         (relcompose
                                                          (relidentity r)
                                                          (relcompose caext
                                                                      (relidentity w)))))
                                 (relunion (relcompose (relidentity w)
                                                       (relcompose rfext
                                                                   (relcompose (relidentity r))))
                                           (relcompose (relidentity (setunion r w))
                                                       (relcompose caext
                                                                   (relidentity w))))))
                      (relidentity (universe)))))
          (not (not-pred-nonempty
                (relimage (singleton e)
                          (relintersect
                           (relplus
                            (relunion (relcompose (relidentity w)
                                                  (relcompose rfext
                                                              (relcompose
                                                               (relidentity r)
                                                               (relcompose poloc
                                                                           (relidentity r)))))
                                      (relunion (relcompose (relidentity w)
                                                            (relcompose rfext
                                                                        (relcompose (relidentity r))))
                                                (relcompose (relidentity (setunion r w))
                                                            (relcompose caext
                                                                        (relidentity w))))))
                           (relidentity (universe))))))))


(tac-rewrite 1000
             '(setimage (singleton e)
                        (relintersect
                         (relplus
                          (relunion (relcompose (relidentity r)
                                                (relcompose poloc
                                                            (relcompose
                                                             (relidentity r)
                                                             (relcompose caext
                                                                         (relidentity w)))))
                                    (relunion (relcompose (relidentity w)
                                                          (relcompose rfext
                                                                      (relidentity r)))
                                              (relcompose (relidentity (setunion r w))
                                                          (relcompose caext
                                                                      (relidentity w))))))
                         (relidentity (universe))))
             '((r . r) (poloc . poloc) (caext . caext) (rfext . rfext) (w . w) (e . e)))
                                                          






(encapsulate
  (((tac-cyclic-pred *) => *)
   ((tac-cyclic-pairs *) => *)
   ((tac-cyclic-rels) => *)
   ((tac-cyclic-unroll) => *)
   ((tac-cyclic-step *) => *))

  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)
  (local (defun tac-cyclic-pred (x) t))
  (local (defun tac-cyclic-rel () nil))
  (local (defun tac-cyclic-src (x) nil))
  (local (defun tac-cyclic-dst (x) t))
  (local (defun tac-cyclic-unroll () 0))
  (local (defun tac-cyclic-step (x) x))

  (defthm tac-cyclic-pred-of-step
    (implies (tac-cyclic-pred x)
             (tac-cyclic-pred (tac-cyclic-step x))))

  (defthm relation-p-of-tac-cyclic-rel
    (relation-p (tac-cyclic-rel)))

  (defthm event-rel-p-of-tac-cyclic-rel
    (event-rel-p (tac-cyclic-rel)))

  (defthm posp-of-tac-cyclic-unroll
    (natp (tac-cyclic-unroll))
    :rule-classes :type-prescription)

  (local (defthm relstar-bounded-of-nil
           (equal (relstar-bounded n nil)
                  (id-relation (universe)))
           :hints(("Goal" :in-theory (enable relstar-bounded)))))

  (local (defthm relstar-unrolled-of-nil
           (equal (relstar-unrolled n nil)
                  (id-relation (universe)))
           :hints(("Goal" :in-theory (enable relstar-unrolled)))))

  (defthm tac-cyclic-pred-implies-nontrivial-edge
    (implies (tac-cyclic-pred x)
             (not (equal (tac-cyclic-src x)
                         (tac-cyclic-dst x)))))
  
  (defthmd tac-cyclic-step-preserves-in-relstar
    (implies (and (tac-cyclic-pred x)
                  (in (edge (tac-cyclic-src x)
                            (tac-cyclic-dst x))
                      (relstar-unrolled n (tac-cyclic-rel)))
                  (natp n))
             (in (edge (tac-cyclic-src (tac-cyclic-step x))
                       (tac-cyclic-dst (tac-cyclic-step x)))
                 (relstar-unrolled (+ 1 (tac-cyclic-unroll) n) (tac-cyclic-rel))))))


(encapsulate nil
  (local (defun ind (n x rel)
           (declare (xargs :measure (nfix (- (relstar-bound rel) (nfix n)))))
           (if (zp (- (relstar-bound rel) (nfix n)))
               x
             (ind (+ 1 (tac-cyclic-unroll)
                     (nfix n))
                  (tac-cyclic-step x) rel))))

  
  (defthm tac-cyclic-step-implies-not-in-relstar
    (implies (tac-cyclic-pred x)
             (not (in (edge (tac-cyclic-src x)
                            (tac-cyclic-dst x))
                      (relstar-unrolled n (tac-cyclic-rel)))))
    :hints (("Goal" :induct (ind n x (tac-cyclic-rel))
             :in-theory (enable relstar-unrolled-of-gte-bound))
            '(:use ((:instance tac-cyclic-step-preserves-in-relstar
                     (n (nfix n))))))))
                
    

