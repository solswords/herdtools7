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

(define pred-nonempty ((s setp))
  :enabled t
  (not (emptyp s)))

(define pred-equal (e1 e2)
  :enabled t
  (equal e1 e2))

(define pred-in-set (e (s setp))
  :enabled t
  (in e s))

(define pred-in-rel (e1 e2 (r relation-p))
  :enabled t
  (in (edge e1 e2) (relation-fix r)))

(acl2::def-ruleset! tac-functions
  '(emptyset singleton setunion setintersect setimage setpreimage relidentity
             relunion relintersect relcompose relstar relinverse relprod
             pred-false pred-nonempty pred-equal pred-in-set pred-in-rel))

(defevaluator tac-ev tac-ev-lst
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
   (relinverse r)
   (relprod s1 s2)
   (pred-false)
   (pred-nonempty s)
   (pred-equal e1 e2)
   (pred-in-set e s)
   (pred-in-rel e1 e2 r)
   
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

(defenum tac-type-p (:event :set :rel))

(fty::defmap type-ctx :key-type pseudo-var :val-type tac-type-p :true-listp t)

(define tac-typed-val-p (val (type tac-type-p))
  (case (tac-type-fix type)
    (:event (event-p val))
    (:set (and (setp val) (event-set-p val)))
    (t    (and (relation-p val) (event-rel-p val)))))

(define tac-typed-env-p ((env alistp) (ctx type-ctx-p))
  (if (atom ctx)
      t
    (and (or (not (mbt (and (consp (car ctx))
                            (pseudo-var-p (caar ctx)))))
             (tac-typed-val-p (cdr (assoc-eq (caar ctx) env)) (tac-type-fix (cdar ctx))))
         (tac-typed-env-p env (cdr ctx))))
  ///
  (defthm tac-typed-env-p-implies-lookup
    (implies (and (tac-typed-env-p env ctx)
                  (assoc-equal v (type-ctx-fix ctx))
                  (pseudo-var-p v))
             (tac-typed-val-p (cdr (assoc-eq v env))
                              (cdr (assoc-equal v (type-ctx-fix ctx)))))
    :hints(("Goal" :in-theory (enable type-ctx-fix))))

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

  (local (in-theory (enable type-ctx-fix))))

(define event-term-p ((x pseudo-termp) (ctx type-ctx-p))
  (pseudo-term-case x
    :var (eq (cdr (assoc-eq x.name (type-ctx-fix ctx))) :event)
    :const (event-p x.val)
    :otherwise nil)
  ///
  (defthm event-p-of-eval-when-event-term-p
    (implies (and (event-term-p x ctx)
                  (tac-typed-env-p env ctx))
             (event-p (tac-ev x env)))))


(include-book "tools/easy-simplify" :dir :system)

(defines set/rel-term-p
  (define set-term-p ((x pseudo-termp) (ctx type-ctx-p))
    :measure (pseudo-term-count x)
    :returns (ok)
    (pseudo-term-case x
      :var (eq (cdr (assoc-eq x.name (type-ctx-fix ctx))) :set)
      :const (and (setp x.val) (event-set-p x.val))
      :lambda nil
      :fncall (case x.fn
                (emptyset t)
                (universe t)
                (singleton (and (consp x.args)
                                (event-term-p (first x.args) ctx)))
                (setunion (and (consp x.args) (consp (cdr x.args))
                               (set-term-p (first x.args) ctx)
                               (set-term-p (second x.args) ctx)))
                (setintersect (and (consp x.args) (consp (cdr x.args))
                                   (set-term-p (first x.args) ctx)
                                   (set-term-p (second x.args) ctx)))
                (setimage (and (consp x.args) (consp (cdr x.args))
                               (set-term-p (first x.args) ctx)
                               (rel-term-p (second x.args) ctx)))
                (setpreimage (and (consp x.args) (consp (cdr x.args))
                                  (rel-term-p (first x.args) ctx)
                                  (set-term-p (second x.args) ctx)))
                (t nil))))
  (define rel-term-p ((x pseudo-termp) (ctx type-ctx-p))
    :measure (pseudo-term-count x)
    :returns (ok)
    (pseudo-term-case x
      :var (eq (cdr (assoc-eq x.name (type-ctx-fix ctx))) :rel)
      :const (and (relation-p x.val) (event-rel-p x.val))
      :lambda nil
      :fncall (case x.fn
                (relidentity (and (consp x.args)
                                  (set-term-p (first x.args) ctx)))
                (relunion (and (consp x.args) (consp (cdr x.args))
                               (rel-term-p (first x.args) ctx)
                               (rel-term-p (second x.args) ctx)))
                (relintersect (and (consp x.args) (consp (cdr x.args))
                                   (rel-term-p (first x.args) ctx)
                                   (rel-term-p (second x.args) ctx)))
                (relcompose (and (consp x.args) (consp (cdr x.args))
                                 (rel-term-p (first x.args) ctx)
                                 (rel-term-p (second x.args) ctx)))
                (relstar (and (consp x.args)
                              (rel-term-p (first x.args) ctx)))
                (relinverse (and (consp x.args)
                                 (rel-term-p (first x.args) ctx)))
                (relprod (and (consp x.args) (consp (cdr x.args))
                              (set-term-p (first x.args) ctx)
                              (set-term-p (second x.args) ctx)))
                (t nil))))
  ///
  (std::defret-mutual type-when-<fn>
    (defret event-set-p-when-<fn>
      (implies (and ok
                    (tac-typed-env-p env ctx))
               (let ((ev (tac-ev x env)))
                 (and (setp ev)
                      (event-set-p ev))))
      :fn set-term-p)
    (defret event-rel-p-when-<fn>
      (implies (and ok
                    (tac-typed-env-p env ctx))
               (let ((ev (tac-ev x env)))
                 (and (relation-p ev)
                      (event-rel-p ev))))
      :fn rel-term-p))

  (fty::deffixequiv-mutual set/rel-term-p)

  (acl2::defopen set-term-p-when-var
    (set-term-p x ctx)
    :hyp (acl2::pseudo-term-case x :var)
    :hint (:expand ((set-term-p x ctx))))

  (acl2::defopen set-term-p-when-const
    (set-term-p x ctx)
    :hyp (acl2::pseudo-term-case x :const)
    :hint (:expand ((set-term-p x ctx))))

  (acl2::defopen set-term-p-when-lambda
    (set-term-p x ctx)
    :hyp (acl2::pseudo-term-case x :lambda)
    :hint (:expand ((set-term-p x ctx))))

  (acl2::defopen set-term-p-when-emptyset
    (set-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'emptyset))
    :hint (:expand ((set-term-p x ctx))))

  (acl2::defopen set-term-p-when-universe
    (set-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'universe))
    :hint (:expand ((set-term-p x ctx))))

  (acl2::defopen set-term-p-when-singleton
    (set-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'singleton))
    :hint (:expand ((set-term-p x ctx))))

  (acl2::defopen set-term-p-when-setunion
    (set-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'setunion))
    :hint (:expand ((set-term-p x ctx))))

  (acl2::defopen set-term-p-when-setintersect
    (set-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'setintersect))
    :hint (:expand ((set-term-p x ctx))))

  (acl2::defopen set-term-p-when-setimage
    (set-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'setimage))
    :hint (:expand ((set-term-p x ctx))))

  (acl2::defopen set-term-p-when-setpreimage
    (set-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'setpreimage))
    :hint (:expand ((set-term-p x ctx))))

  (acl2::defopen set-term-p-when-bad-fncall
    (set-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (not (member-equal (acl2::pseudo-term-fncall->fn x)
                                 '(emptyset universe singleton setunion setintersect setimage setpreimage))))
    :hint (:expand ((set-term-p x ctx))
           :in-theory (enable member-equal)))

  (acl2::defopen rel-term-p-when-var
    (rel-term-p x ctx)
    :hyp (acl2::pseudo-term-case x :var)
    :hint (:expand ((rel-term-p x ctx))))

  (acl2::defopen rel-term-p-when-const
    (rel-term-p x ctx)
    :hyp (acl2::pseudo-term-case x :const)
    :hint (:expand ((rel-term-p x ctx))))

  (acl2::defopen rel-term-p-when-lambda
    (rel-term-p x ctx)
    :hyp (acl2::pseudo-term-case x :lambda)
    :hint (:expand ((rel-term-p x ctx))))

  (acl2::defopen rel-term-p-when-relidentity
    (rel-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relidentity))
    :hint (:expand ((rel-term-p x ctx))))

  (acl2::defopen rel-term-p-when-relunion
    (rel-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relunion))
    :hint (:expand ((rel-term-p x ctx))))

  (acl2::defopen rel-term-p-when-relintersect
    (rel-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relintersect))
    :hint (:expand ((rel-term-p x ctx))))

  (acl2::defopen rel-term-p-when-relcompose
    (rel-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relcompose))
    :hint (:expand ((rel-term-p x ctx))))

  (acl2::defopen rel-term-p-when-relstar
    (rel-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relstar))
    :hint (:expand ((rel-term-p x ctx))))

  (acl2::defopen rel-term-p-when-relinverse
    (rel-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relinverse))
    :hint (:expand ((rel-term-p x ctx))))

  (acl2::defopen rel-term-p-when-relprod
    (rel-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (equal (acl2::pseudo-term-fncall->fn x) 'relprod))
    :hint (:expand ((rel-term-p x ctx))))

  (acl2::defopen rel-term-p-when-bad-fncall
    (rel-term-p x ctx)
    :hyp (and (acl2::pseudo-term-case x :fncall)
              (not (member-equal (acl2::pseudo-term-fncall->fn x)
                                 '(relidentity relunion relintersect relcompose relstar relinverse relprod))))
    :hint (:expand ((rel-term-p x ctx))
           :in-theory (enable member-equal))))

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

(defthm in-image-of-singleton
  (iff (in x (image (insert y nil) z))
       (in (edge y x) (relation-fix z)))
  :hints(("Goal" :in-theory (enable in-of-image-rw
                                    in-of-image-suff))))

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

(defthm in-universe-when-evt-p
  (implies (event-p x)
           (in x (universe)))
  :hints(("Goal" :in-theory (enable event-p))))

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

(defthm exists-path-of-id-relation
  (implies (not (equal src dst))
           (not (exists-path src dst (id-relation x))))
  :hints(("Goal" :in-theory (enable exists-path))))

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

(def-tac-rewrite relstar-of-univrel
  (equal (relstar (relprod (universe) (universe)))
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

(encapsulate nil
  (local (define tac-collect-rewrites-aux ((names symbol-listp)
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
               (mv nil (append rules1 rules2))))))

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
              (implies unify-ok
                       (and (implies (set-term-p x ctx)
                                     (set-term-p (cmr::term-subst-strict rule.rhs subst) ctx))
                            (implies (rel-term-p x ctx)
                                     (rel-term-p (cmr::term-subst-strict rule.rhs subst) ctx))))))
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
                              event-term-p
                              (tac-rewrites))
                             (tac-rewrite-rhs-preserved-necc))))))


(define tac-ev-cube ((x pseudo-term-listp) (env alistp))
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
                            (or (set-term-p x ctx)
                                (rel-term-p x ctx))
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
                  (or (rel-term-p (pseudo-term-fncall fn args) ctx)
                      (set-term-p (pseudo-term-fncall fn args) ctx)))
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
                  (tac-rewrite-rhs-preserved rule))
             (and (implies (rel-term-p (pseudo-term-fncall fn args) ctx)
                           (rel-term-p (cmr::term-subst-strict rhs subst) ctx))
                  (implies (set-term-p (pseudo-term-fncall fn args) ctx)
                           (set-term-p (cmr::term-subst-strict rhs subst) ctx))))
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
      (and (implies (rel-term-p (cmr::term-subst-strict (car x) subst) ctx)
                    (rel-term-p (car y) ctx))
           (implies (set-term-p (cmr::term-subst-strict (car x) subst) ctx)
                    (set-term-p (car y) ctx))
           (implies (event-term-p (cmr::term-subst-strict (car x) subst) ctx)
                    (event-term-p (car y) ctx))
           (termlists-types-preserved (cdr x) (cdr y) subst ctx))))

  (defthm rel-term-p-when-termlists-types-preserved
    (implies (and (rel-term-p (cmr::term-subst-strict x subst) ctx)
                  (termlists-types-preserved (pseudo-term-call->args x) rw-args subst ctx)
                  (equal (len rw-args) (len (pseudo-term-call->args x)))
                  (pseudo-term-case x :fncall))
             (rel-term-p (pseudo-term-fncall
                          (pseudo-term-fncall->fn x) rw-args)
                         ctx))
    :hints(("Goal" 
            :expand ((cmr::term-subst-strict x subst)
                     (cmr::termlist-subst-strict nil subst)
                     (cmr::termlist-subst-strict (pseudo-term-call->args x) subst)
                     (cmr::termlist-subst-strict (cdr (pseudo-term-call->args x)) subst)
                     (termlists-types-preserved (pseudo-term-call->args x) rw-args subst ctx)
                     (termlists-types-preserved (cdr (pseudo-term-call->args x)) (cdr rw-args) subst ctx)
                     (:free (fn args) (rel-term-p (pseudo-term-fncall fn args) ctx))))))

  (defthm set-term-p-when-termlists-types-preserved
    (implies (and (set-term-p (cmr::term-subst-strict x subst) ctx)
                  (termlists-types-preserved (pseudo-term-call->args x) rw-args subst ctx)
                  (equal (len rw-args) (len (pseudo-term-call->args x)))
                  (pseudo-term-case x :fncall))
             (set-term-p (pseudo-term-fncall
                          (pseudo-term-fncall->fn x) rw-args)
                         ctx))
    :hints(("Goal" 
            :expand ((cmr::term-subst-strict x subst)
                     (cmr::termlist-subst-strict nil subst)
                     (cmr::termlist-subst-strict (pseudo-term-call->args x) subst)
                     (cmr::termlist-subst-strict (cdr (pseudo-term-call->args x)) subst)
                     (termlists-types-preserved (pseudo-term-call->args x) rw-args subst ctx)
                     (termlists-types-preserved (cdr (pseudo-term-call->args x)) (cdr rw-args) subst ctx)
                     (:free (fn args) (set-term-p (pseudo-term-fncall fn args) ctx))))))

  (local (defthm event-term-p-of-lambda
           (not (event-term-p (pseudo-term-lambda formals body args) ctx))
           :hints(("Goal" :in-theory (enable event-term-p)))))

  (local (defthm event-term-p-of-fncall
           (not (event-term-p (pseudo-term-fncall fn args) ctx))
           :hints(("Goal" :in-theory (enable event-term-p)))))

  (std::defret-mutual tac-rewrite-types-preserved
    (defret tac-rewrite-types-preserved
      (and (implies (rel-term-p (cmr::term-subst-strict x subst) ctx)
                    (rel-term-p new-x ctx))
           (implies (set-term-p (cmr::term-subst-strict x subst) ctx)
                    (set-term-p new-x ctx))
           (implies (event-term-p (cmr::term-subst-strict x subst) ctx)
                    (event-term-p new-x ctx)))
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
      (and (implies (rel-term-p (pseudo-term-fncall fn args) ctx)
                    (rel-term-p new-x ctx))
           (implies (set-term-p (pseudo-term-fncall fn args) ctx)
                    (set-term-p new-x ctx)))
      :hints ('(:expand (<call>)))
      :fn tac-rewrite-fncall)

    (defret tac-rewrite-apply-rules-types-preserved
      (implies (tac-rewrites-rhs-preserved rules)
               (and (implies (rel-term-p (pseudo-term-fncall fn args) ctx)
                             (rel-term-p new-x ctx))
                    (implies (set-term-p (pseudo-term-fncall fn args) ctx)
                             (set-term-p new-x ctx))))
      :hints ('(:expand (<call>
                         (tac-rewrites-rhs-preserved rules))))
      :fn tac-rewrite-apply-rules))

  (defun tac-rewrite-list-evals-preserved (x new-x subst env ctx)
    (if (atom x)
        t
      (and (implies (or (not (pseudo-term-case (car x) :fncall))
                        (rel-term-p (cmr::term-subst-strict (car x) subst) ctx)
                        (set-term-p (cmr::term-subst-strict (car x) subst) ctx))
                    (equal (tac-ev (car new-x) env)
                           (tac-ev (car x) (tac-ev-alist subst env))))
           (tac-rewrite-list-evals-preserved (cdr x) (cdr new-x) subst env ctx))))

  (defthm eval-preserved-of-rel-term-when-arg-evals-preserved
    (implies (and (tac-rewrite-list-evals-preserved
                   args rw-args subst env ctx)
                  (equal (len args) (len rw-args))
                  (rel-term-p (pseudo-term-fncall fn
                                                  (cmr::termlist-subst-strict args subst))
                              ctx)
                  (pseudo-fnsym-p fn))
             (equal (tac-ev (cons fn rw-args) env)
                    (tac-ev (cons fn args) (tac-ev-alist subst env))))
    :hints (("goal" :expand ((:free (args)
                              (rel-term-p (pseudo-term-fncall fn args)
                                          ctx))
                             (cmr::termlist-subst-strict args subst)
                             (cmr::termlist-subst-strict (cdr args) subst)
                             (tac-rewrite-list-evals-preserved
                              args rw-args subst env ctx)
                             (tac-rewrite-list-evals-preserved
                              (cdr args) (cdr rw-args) subst env ctx))
             :do-not-induct t)))

  (local (defthm event-term-p-when-fncall
           (implies (pseudo-term-case x :fncall)
                    (not (event-term-p x ctx)))
           :hints(("Goal" :in-theory (enable event-term-p)))))

  (local (defthm fncall-of-term-subst-strict
           (implies (pseudo-term-case x :fncall)
                    (pseudo-term-case (cmr::term-subst-strict x subst) :fncall))
           :hints(("Goal" :expand ((cmr::term-subst-strict x subst))))))

  (defthm eval-preserved-of-set-term-when-arg-evals-preserved
    (implies (and (tac-rewrite-list-evals-preserved
                   args rw-args subst env ctx)
                  (equal (len args) (len rw-args))
                  (set-term-p (pseudo-term-fncall fn
                                                  (cmr::termlist-subst-strict args subst))
                              ctx)
                  (pseudo-fnsym-p fn))
             (equal (tac-ev (cons fn rw-args) env)
                    (tac-ev (cons fn args) (tac-ev-alist subst env))))
    :hints (("goal" :expand ((:free (args)
                              (set-term-p (pseudo-term-fncall fn args)
                                          ctx))
                             (cmr::termlist-subst-strict args subst)
                             (cmr::termlist-subst-strict (cdr args) subst)
                             (tac-rewrite-list-evals-preserved
                              args rw-args subst env ctx)
                             (tac-rewrite-list-evals-preserved
                              (cdr args) (cdr rw-args) subst env ctx))
             :do-not-induct t)))
  
  (std::defret-mutual tac-rewrite-correct
    (defret tac-rewrite-correct
      (implies (and (or (not (pseudo-term-case x :fncall))
                        (rel-term-p (cmr::term-subst-strict x subst) ctx)
                        (set-term-p (cmr::term-subst-strict x subst) ctx))
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
      (implies (and (or (rel-term-p (pseudo-term-fncall fn args) ctx)
                        (set-term-p (pseudo-term-fncall fn args) ctx))
                    (tac-typed-env-p env ctx))
               (equal (tac-ev new-x env)
                      (tac-ev (pseudo-term-fncall fn args) env)))
      :hints ('(:expand (<call>)))
      :fn tac-rewrite-fncall)

    (defret tac-rewrite-apply-rules-correct
      (implies (and (or (rel-term-p (pseudo-term-fncall fn args) ctx)
                        (set-term-p (pseudo-term-fncall fn args) ctx))
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

;; XL 
(defthm pred-nonempty-setimage-singleton-prod
  (iff (pred-nonempty (setimage (singleton e1)
                                (relprod (singleton e2) s)))
       (and (pred-equal e1 e2)
            (pred-nonempty s)))
  :hints(("Goal" :in-theory (e/d (in-of-cartesian)))
         (and stable-under-simplificationp
              '(:use ((:instance emptyp-when-in
                       (e (head s))
                       (x (image (insert e1 nil)
                                 (cartesian (insert e1 nil) s)))))
                :in-theory (e/d (in-of-cartesian)
                                (emptyp-when-in)))))
  :otf-flg t)

;; XR
(defthm pred-nonempty-setpreimage-singleton-prod
  (iff (pred-nonempty (setpreimage (relprod s (singleton e2))
                                   (singleton e1)))
       (and (pred-equal e1 e2)
            (pred-nonempty s)))
  :hints(("Goal" :in-theory (e/d (in-of-cartesian)))
         (and stable-under-simplificationp
              '(:use ((:instance emptyp-when-in
                       (e (head s))
                       (x (preimage (insert e1 nil)
                                    (cartesian s (insert e1 nil))))))
                :in-theory (e/d (in-of-cartesian)
                                (emptyp-when-in)))))
  :otf-flg t)

;; U2L
(defthm pred-nonempty-setimage-singleton-union
  (iff (pred-nonempty (setimage (singleton e) (relunion r1 r2)))
       (or (pred-nonempty (setimage (singleton e) r1))
           (pred-nonempty (setimage (singleton e) r2))))
  :hints ((and stable-under-simplificationp
               '(:use ((:instance emptyp-when-in
                        (e (head (setimage (singleton e) (relunion r1 r2))))
                        (x (setimage (singleton e) r1)))
                       (:instance emptyp-when-in
                        (e (head (setimage (singleton e) (relunion r1 r2))))
                        (x (setimage (singleton e) r2)))
                       (:instance emptyp-when-in
                        (e (head (setimage (singleton e) r1)))
                        (x (setimage (singleton e) (relunion r1 r2))))
                       (:instance emptyp-when-in
                        (e (head (setimage (singleton e) r2)))
                        (x (setimage (singleton e) (relunion r1 r2)))))
                 :in-theory (e/d (in-of-image-suff)
                                 (emptyp-when-in
                                  set::never-in-empty))))))

;; U2R
(defthm pred-nonempty-setpreimage-singleton-union
  (iff (pred-nonempty (setpreimage (relunion r1 r2) (singleton e)))
       (or (pred-nonempty (setpreimage r1 (singleton e)))
           (pred-nonempty (setpreimage r2 (singleton e)))))
  :hints ((and stable-under-simplificationp
               '(:use ((:instance emptyp-when-in
                        (e (head (setpreimage (relunion r1 r2) (singleton e))))
                        (x (setpreimage r1 (singleton e))))
                       (:instance emptyp-when-in
                        (e (head (setpreimage (relunion r1 r2) (singleton e))))
                        (x (setpreimage r2 (singleton e))))
                       (:instance emptyp-when-in
                        (e (head (setpreimage r1 (singleton e))))
                        (x (setpreimage (relunion r1 r2) (singleton e))))
                       (:instance emptyp-when-in
                        (e (head (setpreimage r2 (singleton e))))
                        (x (setpreimage (relunion r1 r2) (singleton e)))))
                 :in-theory (e/d ()
                                 (emptyp-when-in
                                  set::never-in-empty))))))


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
(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (not (consp x)))))

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
(defthm pred-nonempty-setimage-singleton-star
  (implies (and (event-p e)
                (event-p w))
           (iff (in w (setimage (singleton e) (relstar r)))
                (or (in w (singleton e))
                    (in w (setimage (setimage (singleton e) r)
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

(defthmd preimage-of-compose-inverse
  (equal (preimage (preimage x y) z)
         (preimage x (compose z y))))

;; *R
(defthm pred-nonempty-setpreimage-singleton-star
  (implies (and (event-p e)
                (event-p w))
           (iff (in w (setpreimage (relstar r) (singleton e)))
                (or (in w (singleton e))
                    (in w (setpreimage (relstar r)
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


;; implemented:
;; ~2XL/R -- relcompose-singleton-prod-1 relcompose-singleton-prod-2
;; ~X2L/R -- relcompose-singleton-prod-3 relcompose-singleton-prod-4
;; ~x-1L/R -- relinverse-of-relprod
;; ~\capXL/R -- relintersect-relprod-singleton-1 relintersect-relprod-singleton-2
;; ~X\capL/R -- relintersect-relprod-singleton-3 relintersect-relprod-singleton-4
