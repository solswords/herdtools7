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
(include-book "centaur/meta/subst-vars" :dir :system)
(local (include-book "std/lists/sets" :dir :System))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable pseudo-termp
                           pseudo-term-listp)))

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

;; (def-tac-rewrite relintersect-relprod-singleton-bogus
;;   (equal (relintersect (relprod z (singleton y)) x)
;;          (cartesian (setintersect z (setpreimage x (singleton y))) (singleton y))))



(include-book "centaur/meta/parse-rewrite" :dir :system)
(include-book "centaur/meta/unify-strict" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "std/util/defconsts" :dir :system)

(fty::defalist tac-rewritelist :key-type symbolp :val-type cmr::rewrite :true-listp t)

(define pair-name-with-rules ((name symbolp) (rules cmr::rewritelist-p))
  :returns (rewrites tac-rewritelist-p)
  (if (atom rules)
      nil
    (cons (cons (mbe :logic (acl2::symbol-fix name) :exec name)
                (cmr::rewrite-fix (car rules)))
          (pair-name-with-rules name (cdr rules)))))

(define tac-collect-rewrites-aux ((names symbol-listp)
                                  (wrld plist-worldp))
  :returns (mv err (rules tac-rewritelist-p))
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
      (mv nil (append (pair-name-with-rules (car names) rules1) rules2)))))

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
    :returns (rewrites tac-rewritelist-p)
    *tac-rewrites*
    ///
    (in-theory (disable (tac-rewrites)))))

(defsection tac-rewrite-rhs-preserved
  (defun-sk tac-rewrite-rhs-preserved (rule)
    (forall (ctx)
            (b* (((cmr::rewrite rule)))
              (implies (tac-term-type rule.lhs ctx)
                       (equal (tac-term-type rule.rhs ctx)
                              (tac-term-type rule.lhs ctx)))))
    :rewrite :direct)

  (in-theory (disable tac-rewrite-rhs-preserved)))


(local (defthm prefixp-of-cons
         (equal (acl2::prefixp (cons a b) c)
                (And (consp c)
                     (equal (car c) a)
                     (acl2::prefixp b (cdr c))))
         :hints(("Goal" :in-theory (enable acl2::prefixp)))))

(define tac-rewrites-rhs-preserved (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-rewrite-rhs-preserved (cdar rules)))
         (tac-rewrites-rhs-preserved (cdr rules))))
  ///
  (local (defthm car-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (car x) a))))
  (local (defthm cdr-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (cdr x) b))))

  ;; (local (defthm tac-term-type-of-tac-subst-ctx
  ;;          (equal (Tac-term-type x (tac-subst-ctx subst ctx))
  ;;                 (tac-term-type (cmr::term-subst-strict x subst) ctx))))
  ;; (local (in-theory (disable tac-term-type-of-term-subst-strict)))
  
  (defthm tac-rewrites-rhs-preserved-of-tac-rewrites
    (tac-rewrites-rhs-preserved (tac-rewrites))
    :hints (("goal" :expand ((:free (x) (tac-rewrite-rhs-preserved x))
                             (:free (a b) (tac-rewrites-rhs-preserved (cons a b))))
             :in-theory (e/d (;; cmr::term-subst-strict
                              ;; cmr::termlist-subst-strict
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
    (forall (ctx env)
            (b* (((cmr::rewrite rule)))
              (implies (and (tac-term-type rule.lhs ctx)
                            (tac-typed-env-p env ctx))
                       (tac-ev-cube rule.hyps env))))
    :rewrite :direct)

  (in-theory (disable tac-rewrite-hyps-ok)))

(define tac-rewrites-hyps-ok (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-rewrite-hyps-ok (cdar rules)))
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
             :in-theory (e/d (cmr::equal-of-pseudo-term-fncall
                              tac-ev-cube
                              (tac-rewrites))
                             (tac-rewrite-hyps-ok-necc))))))




(include-book "std/basic/two-nats-measure" :Dir :system)

(acl2::def-ev-theoremp tac-ev)


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

(define tac-ev-theorem-rewritesp (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-ev-theoremp* (cmr::rewrite-term (cdar rules))))
         (tac-ev-theorem-rewritesp (cdr rules))))
  ///
  (defthm tac-ev-theorem-rewritesp-of-tac-rewrites
    (tac-ev-theorem-rewritesp (tac-rewrites))
    :hints(("Goal" :in-theory (enable (tac-rewrites)
                                      tac-ev-theoremp*-expand)
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

  (local (defthm tac-rewrite-hyps-ok-necc-special
           (b* (((cmr::rewrite rule))
                (subst-env (tac-ev-alist subst env))
                (subst-ctx (tac-subst-ctx subst ctx)))
             (implies (and (tac-rewrite-hyps-ok rule)
                           (tac-typed-env-p env ctx)
                           ;; unify-ok
                           (tac-term-type rule.lhs subst-ctx))
                      (tac-ev-cube rule.hyps subst-env)))
           :hints (("goal" :use ((:instance tac-rewrite-hyps-ok-necc
                                  (env (tac-ev-alist subst env))
                                  (ctx (tac-subst-ctx subst ctx))))
                    :in-theory (disable tac-rewrite-hyps-ok-necc)))))

  (local (defthm tac-term-type-of-tac-subst-ctx
           (equal (Tac-term-type x (tac-subst-ctx subst ctx))
                  (tac-term-type (cmr::term-subst-strict x subst) ctx))))
  (local (in-theory (disable tac-term-type-of-term-subst-strict)))
  
  (defret <fn>-correct
    (implies (and ok
                  (tac-ev-theoremp (cmr::rewrite-term rule))
                  (tac-rewrite-hyps-ok rule)
                  (tac-typed-env-p env ctx)
                  (tac-term-type (pseudo-term-fncall fn args) ctx))
             (equal (tac-ev rhs (tac-ev-alist subst env))
                    (tac-ev (pseudo-term-fncall fn args) env)))
    :hints(("Goal" :in-theory (e/d (cmr::rewrite-term)
                                   (;; tac-rewrite-hyps-ok-necc
                                    ))
            :expand ((CMR::TERM-UNIFY-STRICT (CMR::REWRITE->LHS RULE)
                                             (pseudo-term-fncall fn args) NIL)
                     (:free (subst) (cmr::term-subst-strict (cmr::rewrite->lhs rule) subst)))
            :use ((:instance tac-ev-falsify
                   (a (tac-ev-alist (mv-nth 1 (cmr::termlist-unify-strict
                                               (pseudo-term-call->args (cmr::rewrite->lhs rule))
                                               args nil))
                                    env))
                   (x (cmr::rewrite-term rule)))
                  ;; (:instance tac-rewrite-hyps-ok-necc
                  ;;  (x (pseudo-term-fncall fn args)))
                  ))))

  (local (defthm tac-rewrite-rhs-preserved-necc-special
           (b* (((cmr::rewrite rule))
                (type (tac-term-type (cmr::term-subst-strict rule.lhs subst) ctx)))
             (implies (and (tac-rewrite-rhs-preserved rule)
                           type)
                      (equal (tac-term-type (cmr::term-subst-strict rule.rhs subst) ctx)
                             type)))
           :hints (("goal" :use ((:instance tac-rewrite-rhs-preserved-necc
                                  (ctx (tac-subst-ctx subst ctx))))
                    :in-theory (disable tac-rewrite-rhs-preserved-necc)))))
                          
  
  (defret <fn>-preserves-type
    (implies (and ok
                  (tac-rewrite-rhs-preserved rule)
                  (equal type (tac-term-type (pseudo-term-fncall fn args) ctx))
                  type)
             (equal (tac-term-type (cmr::term-subst-strict rhs subst) ctx)
                    type))
    :hints (("goal" 
            :expand ((CMR::TERM-UNIFY-STRICT (CMR::REWRITE->LHS RULE)
                                             (pseudo-term-fncall fn args) NIL)
                     (:free (subst) (cmr::term-subst-strict (cmr::rewrite->lhs rule) subst))))))

  (defret vars-of-<fn>
    (implies (not (member v (cmr::termlist-vars args)))
             (not (member v (cmr::term-subst-vars subst))))))

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
                                   (rules tac-rewritelist-p)
                                   (fn pseudo-fnsym-p)
                                   (args pseudo-term-listp))
    :measure (acl2::nat-list-measure (list clk 0 0 0 (len rules)))
    :returns (new-x pseudo-termp)
    (if (atom rules)
        (pseudo-term-fncall fn args)
      (b* (((unless (mbt (consp (car rules))))
            (tac-rewrite-apply-rules clk (cdr rules) fn args))
           ((mv ok rhs subst) (tac-rewrite-apply-rule (cdar rules) fn args))
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


  (local (defthm tac-term-type-of-tac-subst-ctx
           (equal (Tac-term-type x (tac-subst-ctx subst ctx))
                  (tac-term-type (cmr::term-subst-strict x subst) ctx))))
  (local (in-theory (disable tac-term-type-of-term-subst-strict)))
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
      :fn tac-rewrite-apply-rules))
  (local (defthm tac-rewrite-apply-rules-of-0
           (equal (tac-rewrite-apply-rules 0 rules fn args)
                  (pseudo-term-fncall fn args))
           :hints (("goal" :induct (len rules)
                    :expand ((tac-rewrite-apply-rules 0 rules fn args))))))
  (local (in-theory (enable tac-rewritelist-fix)))
  (fty::deffixequiv-mutual tac-rewrite))




;; Positive normalization rules that already exist
;; idL/R -- setimage/preimage-of-relidentity, setintersect-of-universe
;; \bot2L/R -- setimage/preimage-of-relidentity, setintersect-of-empty
;; \top2L/R -- setimage/preimage-of-singleton-universe
;; .2,2L/R -- setimage/preimage-of-relcompose
;; .-1L/R -- setimage/preimage-of-inverse
;; \cap2L/R -- setimage/preimage-of-intersect


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
       nil))


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
    :returns (rewrites tac-rewritelist-p)
    *tac-positive-normalize-rules*
    ///
    (in-theory (disable (tac-positive-normalize-rules)))))


(acl2::def-ruleset! tac-negative-normalize-rules nil)

(defmacro def-tac-negative-normalize (name &rest args)
  `(progn (defthm ,name . ,args)
          (acl2::add-to-ruleset tac-negative-normalize-rules ,name)))

;; Categories of negative rules:
;; -- Direction-agnostic normalization rules (use an "l" context instead of "~p"):
;;    idL/idR, \bot2L/\bot2R, \top2L/R, .2,2L/R, .-1L/R, \cap2L/R
;; -- Otherwise straightforward normalization rules (one ~p assumption, one ~p conclusion, no free vars):
;;    ~2XL/R, ~X2L/R, ~X-1L/R, ~\capXL/R, ~X\capL/R
;; -- Decomposition rules: (one ~p assumption, multiple new ~p conclusions, no free vars):
;;    ~\cup2L/R, ~\cup1L/R
;; -- Non-loop case splitting rules: ~XL/R, ~eL/R, ~1XL/R, ~X1L/R
;; -- Looping rules: ~*L/R, ~+L/R
;; -- Top-level only rules (no l or ~p context):  ~\cap1L/R, ~1.2L/R, ~2.1L/R, ~\cap_e, ~\emptyset, ~=
;; -- Instantiation rules (have the same ~p context term in pre and post):
;;    ~aL/R, ~A, ~T1, ~=L (arguably)

;; The first 4 categories can be taken care of using the same rewriter as for positive rules.
;; Top-level rules are straightforward.
;; Looping rules need to be applied with the rest but we'll need to detect repetitions.

;; The problematic ones are the instantiation rules. These
;; (a) need to be able to determine what to introduce for their new variables and
;; (b) need to not loop and just recreate the same new conjunct over and over.

;; It also happens that they are the only contextual rules that deal with
;; additional assumptions.

;; Simplest (?) possibility seems to be to create all the possible new
;; conjuncts at once at the point of rewriting, where it's simple to do so
;; without repetition/looping. Then we need some way of marking that we
;; shouldn't apply that rule again (in the particular context) until there might be new
;; conjuncts to generate.

;; Approaches --
;; 1. Detect these sorts of rewrite rules that need to bind a free variable and will loop,
;;    and treat them specially in the existing rule application framework.
;;   Pros: don't need a new form of rewrite rule, may not need new well formedness props
;;   Cons: complicated?
;; 2. Keep the same form of rewrite rules but apply them in a separate kind of rule application
;; 3. Use a new form of rewrite rule that is more explicit about expansion to
;; multiple disjuncts (or conjuncts when looking at the negations)

;; I think 1 is maybe best?

;; If the rule unifies with the LHS:
;; - check whether this is one of these rules -- will loop and/or needs
;;   assignment of free variables

;; - determine the list of free variable assignment candidates that will
;;   satisfy the hyps

;; - produce the rhs term corresponding to applying the rule for the whole list
;;   of candidates.

;; See special-instantiation-rule functions below...




;; ~aL -- looping/free variable instantiation rule
(def-tac-negative-normalize in-singleton-image-when-pair
  (implies (and (pred-in-rel e1 e2 a)
                (relation-p a))
           (iff (pred-in-set w (setimage (singleton e1) a))
                (or (pred-in-set w (setimage (singleton e1) a))
                    (pred-in-set w (singleton e2))))))

;; ~aR -- looping/free variable instantiation rule
(def-tac-negative-normalize in-singleton-preimage-when-pair
  (implies (and (pred-in-rel e2 e1 a)
                (relation-p a))
           (iff (pred-in-set w (setpreimage a (singleton e1)))
                (or (pred-in-set w (setpreimage a (singleton e1)))
                    (pred-in-set w (singleton e2))))))


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
(def-tac-negative-normalize in-singleton-star-image
  (implies (event-p w)
           (iff (pred-in-set w (setimage (singleton e) (relstar r)))
                (or (pred-in-set w (singleton e))
                    (pred-in-set w (setimage (setimage (singleton e) r) (relstar r))))))
  :hints(("Goal" :in-theory (e/d (reflexive-transitive-closure
                                  image-of-compose-inverse
                                  in-of-compose-suff
                                  in-of-compose-suff2
                                  in-of-compose-rw)
                                 (image-of-compose))
          :use ((:instance in-of-transitive-closure-split
                 (pair (edge e w)))))))

;; ~+L
(def-tac-negative-normalize in-singleton-plus-image
  (implies (event-p w)
           (iff (pred-in-set w (setimage (singleton e) (relplus r)))
                (or (pred-in-set w (setimage (singleton e) r))
                     (pred-in-set w (setimage (setimage (singleton e) r) (relplus r))))))
  :hints(("Goal" :in-theory (e/d (reflexive-transitive-closure
                                  image-of-compose-inverse
                                  in-of-compose-suff
                                  in-of-compose-suff2
                                  in-of-compose-rw)
                                 (image-of-compose))
          :use ((:instance in-of-transitive-closure-split
                 (pair (edge e w)))))))

;; ~*R
(def-tac-negative-normalize in-singleton-star-preimage
  (implies (event-p w)
           (iff (pred-in-set w (setpreimage (relstar r) (singleton e)))
                (or (pred-in-set w (singleton e))
                    (pred-in-set w (setpreimage (relstar r) (setpreimage r (singleton e)))))))
  :hints(("Goal" :in-theory (e/d (reflexive-transitive-closure
                                  preimage-of-compose-inverse
                                  in-of-compose-suff
                                  in-of-compose-suff2
                                  in-of-compose-rw)
                                 (preimage-of-compose))
          :use ((:instance in-of-transitive-closure-split2
                 (pair (edge w e)))))))


;; ~+R
(def-tac-negative-normalize in-singleton-plus-preimage
  (implies (event-p w)
           (iff (pred-in-set w (setpreimage (relplus r) (singleton e)))
                (or (pred-in-set w (setpreimage r (singleton e)))
                    (pred-in-set w (setpreimage (relplus r) (setpreimage r (singleton e)))))))
  :hints(("Goal" :in-theory (e/d (reflexive-transitive-closure
                                  preimage-of-compose-inverse
                                  in-of-compose-suff
                                  in-of-compose-suff2
                                  in-of-compose-rw)
                                 (preimage-of-compose))
          :use ((:instance in-of-transitive-closure-split2
                 (pair (edge w e)))))))

;; ~U2L
(def-tac-negative-normalize in-singleton-union-image
  (iff (pred-in-set w (setimage (singleton e) (relunion r1 r2)))
       (or (pred-in-set w (setimage (singleton e) r1))
           (pred-in-set w (setimage (singleton e) r2)))))

;; ~U2R
(def-tac-negative-normalize in-singleton-union-preimage
  (iff (pred-in-set w (setpreimage (relunion r1 r2) (singleton e)))
       (or (pred-in-set w (setpreimage r1 (singleton e)))
           (pred-in-set w (setpreimage r2 (singleton e))))))

;; ~=L -- looping/free variable instantiation rule
(def-tac-negative-normalize in-singleton-1
  (implies (pred-equal e1 e2)
           (iff (pred-in-set w (singleton e1))
                (or (pred-in-set w (singleton e1))
                    (pred-in-set w (singleton e2))))))

;; ~=R (?)  -- looping/free variable instantiation rule
(def-tac-negative-normalize in-singleton-2
  (implies (pred-equal e2 e1)
           (iff (pred-in-set w (singleton e1))
                (or (pred-in-set w (singleton e1))
                    (pred-in-set w (singleton e2))))))

;; (def-tac-negative-normalize in-singleton-2-bogys
;;   (implies (and (event-p e1)
;;                 (pred-equal e2 e1))
;;            (iff (pred-in-set w (singleton e1))
;;                 (or (pred-in-set w (singleton e1))
;;                     (pred-in-set w (singleton e2))))))

;; ~XL
(def-tac-negative-normalize in-singleton-image-prod
  (iff (pred-in-set w (setimage (singleton e) (relprod s1 s2)))
       (and (pred-nonempty (setintersect (singleton e) s1))
            (pred-in-set w s2)))
  :hints(("Goal" :in-theory (enable in-of-cartesian))))
  
;; ~XR
(def-tac-negative-normalize in-singleton-preimage-prod
  (iff (pred-in-set w (setpreimage (relprod s1 s2) (singleton e)))
       (and (pred-nonempty (setintersect (singleton e) s2))
            (pred-in-set w s1)))
  :hints(("Goal" :in-theory (enable in-of-cartesian))))



;; ~A -- looping/free variable instantiation rule
(def-tac-negative-normalize in-base-set
  (implies (and (pred-in-set e a)
                (base-set-p a))
           (iff (pred-in-set w a)
                (or (pred-in-set w a)
                    (pred-in-set w (singleton e))))))
           
;; ~U1
(def-tac-negative-normalize in-setunion
  (iff (pred-in-set w (setunion s1 s2))
       (or (pred-in-set w s1)
           (pred-in-set w s2))))


;; ~T1  -- looping/free variable instantiation rule
(def-tac-negative-normalize in-universe
  (implies (and (mentioned-event-p e)
                (event-p e))
           (iff (pred-in-set w (universe))
                (or (pred-in-set w (universe))
                    (pred-in-set w (singleton e))))))
;; ~eL
(def-tac-negative-normalize in-singleton-intersect-1
  (iff (pred-in-set w (setintersect (singleton e) s))
       (and (pred-in-set w (singleton e))
            (pred-nonempty (setintersect (singleton e) s)))))

;; ~eR
(def-tac-negative-normalize in-singleton-intersect-2
  (iff (pred-in-set w (setintersect s (singleton e)))
       (and (pred-in-set w (singleton e))
            (pred-nonempty (setintersect s (singleton e))))))



;; (defthm singleton-intersect-image
;;   (equal (intersect (insert e nil) (image s r))
;;          (intersect (preimage (insert e nil) r) s))
;;   :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
;;                                      pick-a-point-subset-strategy))))


;; ~.1,2L
(def-tac-negative-normalize nonempty-singleton-intersect-image-1
  (implies (not-singleton-set-p s)
           (iff (pred-nonempty (setintersect (singleton e) (setimage s r)))
                (pred-nonempty (setintersect (setpreimage r (singleton e)) s))))
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
           (iff (pred-nonempty (setintersect (setimage s r) (singleton e)))
                (pred-nonempty (setintersect s (setpreimage r (singleton e))))))
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
           (iff (pred-nonempty (setintersect (singleton e) (setpreimage r s)))
                (pred-nonempty (setintersect (setimage (singleton e) r) s))))
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
           (iff (pred-nonempty (setintersect (setpreimage r s) (singleton e)))
                (pred-nonempty (setintersect s (setimage (singleton e) r)))))
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
  (iff (pred-nonempty (setintersect (singleton e) (setintersect s1 s2)))
       (and (pred-nonempty (setintersect (singleton e) s1))
            (pred-nonempty (setintersect (singleton e) s2)))))
;; ~\cap1R
(def-tac-negative-normalize nonempty-singleton-intersect-intersect-2
  (iff (pred-nonempty (setintersect (setintersect s1 s2) (singleton e)))
       (and (pred-nonempty (setintersect s1 (singleton e)))
            (pred-nonempty (setintersect s2 (singleton e))))))

;; ~\cap_e
(def-tac-negative-normalize nonempty-singleton-intersect-singleton
  (iff (pred-nonempty (setintersect (singleton e1) (singleton e2)))
       (pred-equal e1 e2)))

;; ~1XL
(def-tac-negative-normalize in-image-product-singleton-1
  (iff (pred-in-set w (setimage s1 (relprod (singleton e) s2)))
       (and (pred-in-set w s2)
            (pred-nonempty (setintersect s1 (singleton e)))))
  :hints(("Goal" :in-theory (enable in-of-image-rw
                                    in-of-cartesian))))
;; ~1XR
(def-tac-negative-normalize in-image-product-singleton-2
  (iff (pred-in-set w (setpreimage (relprod s2 (singleton e)) s1))
       (and (pred-in-set w s2)
            (pred-nonempty (setintersect s1 (singleton e)))))
  :hints(("Goal" :in-theory (enable in-of-preimage-rw
                                    in-of-cartesian))))
;; ~X1L
(def-tac-negative-normalize in-image-product-singleton-3
  (iff (pred-in-set w (setpreimage (relprod (singleton e) s1) s2))
       (and (pred-in-set w (singleton e))
            (pred-nonempty (setintersect s1 s2))))
  :hints(("Goal" :in-theory (e/d (in-of-preimage-rw
                                  in-of-cartesian)
                                 (emptyp-when-in
                                  set::never-in-empty))
          :use ((:instance emptyp-when-in
                 (e (preimage-witness w s2 (cartesian (insert e nil) s1)))
                 (x (intersect s1 s2)))))))

;; ~X1R
(def-tac-negative-normalize in-image-product-singleton-4
  (iff (pred-in-set w (setimage s2 (relprod s1 (singleton e))))
       (and (pred-in-set w (singleton e))
            (pred-nonempty (setintersect s1 s2))))
  :hints(("Goal" :in-theory (e/d (in-of-image-rw
                                  in-of-cartesian)
                                 (emptyp-when-in
                                  set::never-in-empty))
          :use ((:instance emptyp-when-in
                 (e (image-witness w s2 (cartesian s1 (insert e nil))))
                 (x (intersect s1 s2)))))))
;; ~0
(def-tac-negative-normalize pred-nonempty-of-singleton
  (iff (pred-nonempty (singleton e))
       t))

;; ~=
(def-tac-negative-normalize pred-equal-same
  (iff (pred-equal e e)
       t))

(encapsulate nil

  (acl2::defconsts *tac-negative-normalize-rules*
    (b* (((mv err rewrites)
          (tac-collect-rewrites-aux
           (acl2::get-ruleset 'tac-negative-normalize-rules (w state))
           (w state))))
      (if err
          (er hard? '*tac-negative-normalize-rules* "~@0" err)
        rewrites)))

  (define tac-negative-normalize-rules ()
    :returns (rewrites tac-rewritelist-p)
    *tac-negative-normalize-rules*
    ///
    (in-theory (disable (tac-negative-normalize-rules)))))


(local
 (defthm symbol-listp-when-pseudo-var-list-p
   (implies (cmr::pseudo-var-list-p x)
            (symbol-listp x))))



(define is-special-instantiation-rule ((x cmr::rewrite-p))
  (b* (((cmr::rewrite x)))
    (pseudo-term-case x.rhs
      :fncall (and (eq x.rhs.fn 'if)
                   (equal (first x.rhs.args) (second x.rhs.args)) ;; or
                   (equal (first x.rhs.args) x.lhs))
      :otherwise nil)))

(define special-instantiation-rule-free-vars ((x cmr::rewrite-p))
  :guard (is-special-instantiation-rule x)
  :guard-hints (("Goal" :in-theory (enable is-special-instantiation-rule)))
  :returns (vars cmr::pseudo-var-list-p)
  :prepwork ((local (defthm pseudo-var-list-p-of-set-diff
                      (implies (cmr::pseudo-var-list-p x)
                               (cmr::pseudo-var-list-p (set-difference-equal x y))))))
  (b* (((cmr::rewrite x))
       ((pseudo-term-fncall x.rhs)))
    (set-difference-eq (cmr::term-vars (third x.rhs.args)) (cmr::term-vars x.lhs))))

(define special-instantiation-rule-binding-hyp ((x cmr::rewrite-p))
  :guard (is-special-instantiation-rule x)
  :guard-hints (("Goal" :in-theory (enable is-special-instantiation-rule)))
  :returns (hyp pseudo-termp)
  :prepwork ((local (defthm pseudo-var-list-p-of-set-diff
                      (implies (cmr::pseudo-var-list-p x)
                               (cmr::pseudo-var-list-p (set-difference-equal x y))))))
  (b* (((cmr::rewrite x))
       (free-vars (special-instantiation-rule-free-vars x)))
    (and (consp x.hyps)
         (intersectp-eq (cmr::term-vars (car x.hyps)) free-vars)
         (car x.hyps))))

(defthm tac-ev-theorem-rewritesp-of-tac-positive-normalize-rules
  (tac-ev-theorem-rewritesp (tac-positive-normalize-rules))
  :hints(("Goal" :in-theory (acl2::e/d* ((tac-positive-normalize-rules)
                                         tac-ev-theoremp*-expand)
                                        ((:ruleset tac-negative-normalize-rules)
                                         tac-functions
                                         (emptyset)
                                         (pred-false))
                                        ((:ruleset tac-positive-normalize-rules)))
          :expand ((:Free (a b) (tac-ev-theorem-rewritesp (cons a b)))))))

(defsection tac-ev-theorem-rewritesp-of-tac-negative-normalize-rules
  (local (define tac-ev-theorem-rewrite-p ((name symbolp)
                                           (rule cmr::rewrite-p))
           :verify-guards nil
           (declare (ignore name))
           (tac-ev-theoremp* (cmr::rewrite-term rule))))

  (local (in-theory (disable (tac-ev-theorem-rewrite-p))))
  (local (defthm tac-ev-theorem-rewritesp-in-terms-of-rewrite-p
           (equal (tac-ev-theorem-rewritesp (cons a b))
                  (and (or (not (consp a))
                           (tac-ev-theorem-rewrite-p (car a) (cdr a)))
                       (tac-ev-theorem-rewritesp b)))
           :hints (("goal" :expand ((tac-ev-theorem-rewritesp (cons a b)))
                    :in-theory (e/d (tac-ev-theorem-rewrite-p))))))

  (local (defun instance-subst (vars term)
           (if (atom vars)
               nil
             (cons (list (car vars)
                         `(cdr (assoc-equal ',(car vars)
                                            (tac-ev-falsify ',term))))
                   (instance-subst (cdr vars) term)))))

  (defthm tac-ev-theorem-rewritesp-of-tac-negative-normalize-rules
    (tac-ev-theorem-rewritesp (tac-negative-normalize-rules))
    :hints(("Goal" :in-theory (acl2::e/d* ((tac-negative-normalize-rules)
                                           tac-ev-theoremp*-expand)
                                          ((:ruleset tac-negative-normalize-rules)
                                           (:ruleset tac-positive-normalize-rules)
                                           (:ruleset tac-rewrites)
                                           tac-functions
                                           (emptyset)
                                           (pred-false))))
           (and stable-under-simplificationp
                (let ((lit (car (last clause))))
                  (case-match lit
                    (('tac-ev-theorem-rewrite-p ('quote name) ('quote rule))
                     (let ((rule-term (cmr::rewrite-term rule)))
                       `(:use ((:instance ,name
                                . ,(instance-subst (cmr::term-vars rule-term) rule-term)))
                         :expand (,lit))))))))))


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



(defthm setimage-of-setunion-1
  (equal (setimage (setunion s1 s2) r)
         (setunion (setimage s1 r)
                   (setimage s2 r))))

(defthm setimage-of-relunion-2
  (equal (setimage s (relunion r1 r2))
         (setunion (setimage s r1)
                   (setimage s r2))))

(defthm setpreimage-of-setunion-2
  (equal (setpreimage r (setunion s1 s2))
         (setunion (setpreimage r s1)
                   (setpreimage r s2))))

(defthm setpreimage-of-relunion-1
  (equal (setpreimage (relunion r1 r2) s)
         (setunion (setpreimage r1 s)
                   (setpreimage r2 s)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-preimage-rw))))

(defthm relidentity-of-setunion
  (equal (relidentity (setunion s1 s2))
         (relunion (relidentity s1)
                   (relidentity s2))))

(defthm relcompose-of-relunion-1
  (equal (relcompose (relunion r1 r2) r3)
         (relunion (relcompose r1 r3)
                   (relcompose r2 r3))))

(defthm relcompose-of-relunion-2
  (equal (relcompose r1 (relunion r2 r3))
         (relunion (relcompose r1 r2)
                   (relcompose r1 r3))))

(defthm relinverse-of-relunion
  (equal (relinverse (relunion r1 r2))
         (relunion (relinverse r1)
                   (relinverse r2))))

(defthm setintersect-of-setunion-1
  (equal (setintersect (setunion s1 s2) s3)
         (setunion (setintersect s1 s3)
                   (setintersect s2 s3)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy))))

(defthm setintersect-of-setunion-2
  (equal (setintersect s1 (setunion s2 s3))
         (setunion (setintersect s1 s2)
                   (setintersect s1 s3)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy))))

(defthm relintersect-of-relunion-1
  (equal (relintersect (relunion s1 s2) s3)
         (relunion (relintersect s1 s3)
                   (relintersect s2 s3)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy))))

(defthm relintersect-of-relunion-2
  (equal (relintersect s1 (relunion s2 s3))
         (relunion (relintersect s1 s2)
                   (relintersect s1 s3)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy))))



;; implemented:
;; ~2XL/R -- relcompose-singleton-prod-1 relcompose-singleton-prod-2
;; ~X2L/R -- relcompose-singleton-prod-3 relcompose-singleton-prod-4
;; ~x-1L/R -- relinverse-of-relprod
;; ~\capXL/R -- relintersect-relprod-singleton-1 relintersect-relprod-singleton-2
;; ~X\capL/R -- relintersect-relprod-singleton-3 relintersect-relprod-singleton-4


;; (fty::deflist pseudo-term-list-list :elt-type pseudo-term-listp
;;   :pred acl2::pseudo-term-list-listp
;;   :true-listp t)

(defprod tac-ruleres-branch
  ((assums pseudo-term-listp)
   (ctx-result pseudo-termp)))

;; all disjoined
(deflist tac-ruleres-branchlist :elt-type tac-ruleres-branch :true-listp t)

;; list of disjoined branches for arguments
(deflist tac-ruleres-branchlistlist :elt-type tac-ruleres-branchlist :true-listp t)

(defprod tac-ruleres-branch-args
  ((assums pseudo-term-listp)
   (ctx-result-args pseudo-term-listp)))

(deflist tac-ruleres-branch-argslist :elt-type tac-ruleres-branch-args :true-listp t)


;; ------------- Types of tac-ruleres objects


(define tac-ruleres-branch-typed ((x tac-ruleres-branch-p)
                                               (type tac-type-p)
                                               (ctx type-ctx-p))
  (b* (((tac-ruleres-branch x)))
    (and (subsetp (tac-termlist-types x.assums ctx) '(:pred))
         (let ((type (tac-type-fix type)))
           (or (not type)
               (equal (tac-term-type x.ctx-result ctx) type)))))
  ///
  (defthm tac-ruleres-branch-typed-when-nil
    (implies (tac-ruleres-branch-typed x type ctx)
             (tac-ruleres-branch-typed x nil ctx))))

(define tac-ruleres-branchlist-typed ((x tac-ruleres-branchlist-p)
                                                   (type tac-type-p)
                                                   (ctx type-ctx-p))
  (if (atom x)
      t
    (and (tac-ruleres-branch-typed (car x) type ctx)
         (tac-ruleres-branchlist-typed (cdr x) type ctx)))
  ///
  (defthm tac-ruleres-branchlist-typed-of-append
    (iff (tac-ruleres-branchlist-typed (append x y) type ctx)
         (and (tac-ruleres-branchlist-typed x type ctx)
              (tac-ruleres-branchlist-typed y type ctx))))
  
  (defthm tac-ruleres-branchlist-typed-when-nil
    (implies (tac-ruleres-branchlist-typed x type ctx)
             (tac-ruleres-branchlist-typed x nil ctx))))

(define tac-ruleres-branchlistlist-typed ((x tac-ruleres-branchlistlist-p)
                                                       (types tac-typelist-p)
                                                       (ctx type-ctx-p))
  (if (atom types)
      t
    (and (consp x)
         (tac-ruleres-branchlist-typed (car x) (car types) ctx)
         (tac-ruleres-branchlistlist-typed (cdr x) (cdr types) ctx))))

;; (deflist tac-typelistlist :elt-type tac-typelist :true-listp t)

;; (define tac-termlistlist-types ((x acl2::pseudo-term-list-listp)
;;                                 (ctx type-ctx-p))
;;   :returns (types tac-typelistlist-p)
;;   (if (atom x)
;;       nil
;;     (cons (tac-termlist-types (car x) ctx)
;;           (tac-termlistlist-types (cdr x) ctx))))

;; (define prefixp-of-all (x y)
;;   (if (atom y)
;;       t
;;     (and (acl2::prefixp x (car y))
;;          (prefixp-of-all x (cdr y))))
;;   ///
;;   (defthm prefixp-of-all-of-nil
;;     (prefixp-of-all nil y)
;;     :hints(("Goal" :in-theory (enable acl2::prefixp)))))

(define tac-ruleres-branch-args-typed ((x tac-ruleres-branch-args-p)
                                                    (types tac-typelist-p)
                                                    (ctx type-ctx-p))
  (b* (((tac-ruleres-branch-args x)))
    (and (subsetp (tac-termlist-types x.assums ctx) '(:pred))
         (acl2::prefixp (tac-typelist-fix types) (tac-termlist-types x.ctx-result-args ctx))))
  ///
  (defthm tac-ruleres-branch-args-typed-of-nil
    (implies (tac-ruleres-branch-args-typed x types ctx)
             (tac-ruleres-branch-args-typed x nil ctx))
    :hints(("Goal" :in-theory (enable acl2::prefixp)))))

(define tac-ruleres-branch-argslist-typed ((x tac-ruleres-branch-argslist-p)
                                                        (types tac-typelist-p)
                                                        (ctx type-ctx-p))
  (if (atom x)
      t
    (and (tac-ruleres-branch-args-typed (car x) types ctx)
         (tac-ruleres-branch-argslist-typed (cdr x) types ctx)))
  ///
  (defthm tac-ruleres-branch-argslist-typed-of-nil
    (implies (tac-ruleres-branch-argslist-typed x types ctx)
             (tac-ruleres-branch-argslist-typed x nil ctx)))

  (defthm tac-ruleres-branch-argslist-typed-of-append
    (implies (and (tac-ruleres-branch-argslist-typed x types ctx)
                  (tac-ruleres-branch-argslist-typed y types ctx))
             (tac-ruleres-branch-argslist-typed (append x y) types ctx))))

;; ------------- Evaluation of of tac-ruleres objects

(define tac-eval-ruleres-branch ((x tac-ruleres-branch-p)
                                              env)
  :verify-guards nil
  (b* (((tac-ruleres-branch x)))
    (and (tac-ev-cube x.assums env)
         (tac-ev x.ctx-result env)))
  ///
  (defthm relation-p-of-tac-eval-ruleres-branch-by-type
    (implies (and (tac-ruleres-branch-typed x :rel ctx)
                  (tac-typed-env-p env ctx))
             (relation-p (tac-eval-ruleres-branch x env)))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-typed))))

  (defthm tac-typed-val-p-of-tac-eval-ruleres-branch-by-type
    (implies (and (tac-ruleres-branch-typed x type ctx)
                  (member-equal type '(:set :rel))
                  (tac-typed-env-p env ctx))
             (tac-typed-val-p (tac-eval-ruleres-branch x env) type))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-typed
                                      tac-typed-val-p)))))

(include-book "kestrel/fty/set" :dir :system)

(fty::deflist setlist :elt-type setp :true-listp t)
(fty::deflist rellist :elt-type relation :true-listp t)

(define tac-eval-ruleres-branchlist ((x tac-ruleres-branchlist-p)
                                                  env)
  :verify-guards nil
  :returns (vals true-listp :rule-classes :type-prescription)
  (if (atom x)
      nil
    (cons (tac-eval-ruleres-branch (car x) env)
          (tac-eval-ruleres-branchlist (cdr x) env)))
  ///
  (defthm tac-eval-ruleres-branchlist-of-append
    (equal (tac-eval-ruleres-branchlist (append x y) env)
           (append (tac-eval-ruleres-branchlist x env)
                   (tac-eval-ruleres-branchlist y env))))
  

  (defthm tac-1typed-vallist-p-of-tac-eval-ruleres-branch-by-type
    (implies (and (tac-typed-env-p env ctx)
                  (tac-ruleres-branchlist-typed x type ctx)
                  (member-equal type '(:set :rel)))
             (tac-1typed-vallist-p (tac-eval-ruleres-branchlist x env) type))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-typed
                                      tac-1typed-vallist-p)))))

(define tac-typed-multiarglist-p ((x true-list-listp) (types tac-typelist-p))
  :measure (len types)
  (if (atom types)
      t
    (and (tac-1typed-vallist-p (car x) (car types))
         (tac-typed-multiarglist-p (cdr x) (cdr types)))))

(define tac-eval-ruleres-branchlistlist ((x tac-ruleres-branchlistlist-p)
                                                      env)
  :verify-guards nil
  :returns (vals true-list-listp)
  (if (atom x)
      nil
    (cons (tac-eval-ruleres-branchlist (car x) env)
          (tac-eval-ruleres-branchlistlist (cdr x) env)))
  ///
  (defthm tac-eval-ruleres-branchlistli-of-append
    (equal (tac-eval-ruleres-branchlistlist (append x y) env)
           (append (tac-eval-ruleres-branchlistlist x env)
                   (tac-eval-ruleres-branchlistlist y env))))

  (defthm tac-typed-multiarglist-p-of-tac-eval-ruleres-branchlistlist
    (implies (and (tac-typed-env-p env ctx)
                  (tac-ruleres-branchlistlist-typed x types ctx)
                  (subsetp-equal types '(:set :rel)))
             (tac-typed-multiarglist-p (tac-eval-ruleres-branchlistlist x env) types))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlistlist-typed
                                      tac-typed-multiarglist-p
                                      subsetp-equal))))

  (defret len-of-<fn>
    (equal (len vals) (len x))))



(local (include-book "std/lists/repeat" :dir :system))

(define tac-eval-ruleres-branch-args ((x tac-ruleres-branch-args-p)
                                                   env)
  :verify-guards nil
  (b* (((tac-ruleres-branch-args x)))
    (if (tac-ev-cube x.assums env)
        (tac-ev-lst x.ctx-result-args env)
      (make-list (len x.ctx-result-args) :initial-element nil)))
  ///
  (local (include-book "std/lists/repeat" :dir :system))
  (local (defthm tac-typed-vallist-p-repeat-nil
           (implies (and (subsetp-equal types '(:set :rel)))
                    (tac-typed-vallist-p (acl2::repeat n nil) types))
           :hints(("Goal" :in-theory (enable tac-typed-vallist-p
                                             acl2::repeat)
                   :induct (nthcdr n types)))))

  (local (defthmd prefixp-implies-len
           (implies (acl2::prefixp x y)
                    (<= (len x) (len y)))
           :hints(("Goal" :in-theory (enable acl2::prefixp)))))

  (local (defun cdr-cdr-ind (x y)
           (if (atom x)
               y
             (cdr-cdr-ind (cdr x) (cdr y)))))

  ;; (local (defthm equal-tac-type-fix-forward
  ;;          (implies (equal (tac-type-fix x) y)
  ;;                   (tac-type-equiv x y))
  ;;          :rule-classes :forward-chaining))

  (defthm len-of-tac-termlist-types
    (equal (len (tac-termlist-types x ctx))
           (len x))
    :hints(("Goal" :in-theory (enable tac-termlist-types))))
  
  (defthm tac-typed-vallist-p-when-prefixp-types
    (implies (and (acl2::prefixp (tac-typelist-fix types) (tac-termlist-types x ctx))
                  (tac-typed-env-p env ctx))
             (tac-typed-vallist-p (tac-ev-lst x env) types))
    :hints(("Goal" :induct (cdr-cdr-ind types x)
            :in-theory (enable acl2::prefixp tac-termlist-types tac-typed-vallist-p
                               tac-typelist-fix))
           (and stable-under-simplificationp
                '(:use ((:instance tac-typed-val-p-when-term-type
                         (x (car x))))
                  :in-theory (disable tac-typed-val-p-when-term-type)))))

  
  (defthm tac-typed-vallist-p-of-tac-eval-ruleres-branch-args
    (implies (and (tac-ruleres-branch-args-typed x types ctx)
                  (tac-typed-env-p env ctx)
                  (subsetp-equal types '(:set :rel)))
             (tac-typed-vallist-p (tac-eval-ruleres-branch-args x env) types))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-args-typed)
            :use ((:instance prefixp-implies-len
                   (x (tac-typelist-fix types))
                   (y (tac-termlist-types (tac-ruleres-branch-args->ctx-result-args x) ctx))))))))

(define tac-eval-ruleres-branch-argslist ((x tac-ruleres-branch-argslist-p)
                                                       env)
  :verify-guards nil
  (if (atom x)
      nil
    (cons (tac-eval-ruleres-branch-args (car x) env)
          (tac-eval-ruleres-branch-argslist (cdr x) env)))
  ///
  (defthm tac-eval-ruleres-branch-argslist-of-append
    (equal (tac-eval-ruleres-branch-argslist (append x y) env)
           (append (tac-eval-ruleres-branch-argslist x env)
                   (tac-eval-ruleres-branch-argslist y env)))))



;; ------------ Variables of tac-ruleres objects
(local (Defthm union-of-pseudo-var-list
         (implies (and (cmr::pseudo-var-list-p x)
                       (cmr::pseudo-var-list-p y))
                  (cmr::pseudo-var-list-p (union-equal x y)))))

(local (defthm symbol-listp-when-pseudo-var-list-p
         (implies (cmr::pseudo-var-list-p x)
                  (symbol-listp x))))

(cmr::defthm-term-vars-flag
  (defthm tac-ev-of-cons-non-var
    (implies (not (member-equal v (cmr::term-vars x)))
             (equal (tac-ev x (cons (cons v val) env))
                    (tac-ev x env)))
    :hints ('(:expand ((cmr::term-vars x))
              :in-theory (enable tac-ev-when-pseudo-term-call)))
    :flag cmr::term-vars)
  (defthm tac-ev-lst-of-cons-non-var
    (implies (not (member-equal v (cmr::termlist-vars x)))
             (equal (tac-ev-lst x (cons (cons v val) env))
                    (tac-ev-lst x env)))
    :hints ('(:expand ((cmr::termlist-vars x))))
    :flag cmr::termlist-vars))

(defthm eval-cons-non-var-of-cube
  (implies (not (member-equal v (cmr::termlist-vars cube)))
           (equal (tac-ev-cube cube (cons (cons v val) env))
                  (tac-ev-cube cube env)))
  :hints(("Goal" :in-theory (enable tac-ev-cube cmr::termlist-vars))))

(define tac-ruleres-branch-vars ((x tac-ruleres-branch-p))
  :returns (vars cmr::pseudo-var-list-p)
  (b* (((tac-ruleres-branch x)))
    (union-eq (cmr::termlist-vars x.assums)
              (cmr::term-vars x.ctx-result)))
  ///
  (defret eval-cons-non-var-of-<fn>
    (implies (not (member-equal v vars))
             (equal (tac-eval-ruleres-branch x (cons (cons v val) env))
                    (tac-eval-ruleres-branch x env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch))))

  (defthm tac-ruleres-branch-typed-of-add-unused-var
    (implies (not (member-equal v (tac-ruleres-branch-vars x)))
             (equal (tac-ruleres-branch-typed x type (cons (cons v vtype) ctx))
                    (tac-ruleres-branch-typed x type ctx)))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-typed
                                      tac-ruleres-branch-vars)))))


(define tac-ruleres-branchlist-vars ((x tac-ruleres-branchlist-p))
  :returns (vars cmr::pseudo-var-list-p)
  (if (atom x)
      nil
    (union-eq (tac-ruleres-branch-vars (car x))
              (tac-ruleres-branchlist-vars (cdr x))))
  ///
  (defret eval-cons-non-var-of-<fn>
    (implies (not (member-equal v vars))
             (equal (tac-eval-ruleres-branchlist x (cons (cons v val) env))
                    (tac-eval-ruleres-branchlist x env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branchlist))))

  (defthm tac-ruleres-branchlist-typed-of-add-unused-var
    (implies (not (member-equal v (tac-ruleres-branchlist-vars x)))
             (equal (tac-ruleres-branchlist-typed x type (cons (cons v vtype) ctx))
                    (tac-ruleres-branchlist-typed x type ctx)))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-typed
                                      tac-ruleres-branchlist-vars)))))

(define tac-ruleres-branchlistlist-vars ((x tac-ruleres-branchlistlist-p))
  :returns (vars cmr::pseudo-var-list-p)
  (if (atom x)
      nil
    (union-eq (tac-ruleres-branchlist-vars (car x))
              (tac-ruleres-branchlistlist-vars (cdr x)))))


(define tac-ruleres-branch-args-vars ((x tac-ruleres-branch-args-p))
  :returns (vars cmr::pseudo-var-list-p)
  (b* (((tac-ruleres-branch-args x)))
    (union-eq (cmr::termlist-vars x.assums)
              (cmr::termlist-vars x.ctx-result-args))))

(define tac-ruleres-branch-argslist-vars ((x tac-ruleres-branch-argslist-p))
  :returns (vars cmr::pseudo-var-list-p)
  (if (atom x)
      nil
    (union-eq (tac-ruleres-branch-args-vars (car x))
              (tac-ruleres-branch-argslist-vars (cdr x)))))


;; Interlude for reasoning about removing a variable from a substitution
(local (include-book "std/alists/hons-remove-assoc" :dir :system))

(defsection hons-remove-assoc-lemmas
  
  
  (local (defthm assoc-equal-is-hons-assoc-equal
           (implies k
                    (equal (assoc-equal k x)
                           (hons-assoc-equal k x)))))


  
  (cmr::defthm-term-vars-flag
    (defthm term-subst-strict-of-remove-non-term-var
      (implies (not (member-equal v (cmr::term-vars x)))
               (equal (cmr::term-subst-strict x (acl2::hons-remove-assoc v subst))
                      (cmr::term-subst-strict x subst)))
      :hints ('(:expand ((cmr::term-vars x)
                         (:free (Subst) (cmr::term-subst-strict x subst)))))
      :flag cmr::term-vars)
    (defthm termlist-subst-strict-of-remove-non-term-var
      (implies (not (member-equal v (cmr::termlist-vars x)))
               (equal (cmr::termlist-subst-strict x (acl2::hons-remove-assoc v subst))
                      (cmr::termlist-subst-strict x subst)))
      :hints ('(:expand ((cmr::termlist-vars x)
                         (:free (Subst) (cmr::termlist-subst-strict x subst)))))
      :flag cmr::termlist-vars))

  #!cmr (flag::make-flag term-unify-strict :local t)
  (local (in-theory (disable cmr::term-unify-strict-reversible-iff-rw
                             cmr::termlist-unify-strict-reversible-iff-rw)))

  (local (defthm hons-remove-assoc-of-pseudo-term-subst-fix
           (equal (cmr::pseudo-term-subst-fix (acl2::hons-remove-assoc v alist))
                  (acl2::hons-remove-assoc v (cmr::pseudo-term-subst-fix alist)))
           :hints(("Goal" :in-theory (enable acl2::hons-remove-assoc
                                             cmr::pseudo-term-subst-fix)))))
  #!cmr
  (cmr::defthm-flag-term-unify-strict
    (defthm term-unify-strict-of-hons-remove-assoc
      (b* (((mv ok subst) (term-unify-strict pat x alist))
           ((mv ok1 subst1) (term-unify-strict pat x (acl2::hons-remove-assoc v alist))))
        (implies (and (not (member-equal v (term-vars pat)))
                      ok)
                 (and ok1
                      (equal (acl2::hons-remove-assoc v subst)
                             subst1))))
      :hints ('(:expand ((:free (alist) (term-unify-strict pat x alist))
                         (term-vars pat))))
      :flag term-unify-strict)
    (defthm termlist-unify-strict-of-hons-remove-assoc
      (b* (((mv ok subst) (termlist-unify-strict pat x alist))
           ((mv ok1 subst1) (termlist-unify-strict pat x (acl2::hons-remove-assoc v alist))))
        (implies (and (not (member-equal v (termlist-vars pat)))
                      ok)
                 (and ok1
                      (equal (acl2::hons-remove-assoc v subst)
                             subst1))))
      :hints ('(:expand ((:free (alist) (termlist-unify-strict pat x alist))
                         (termlist-vars pat))))
      :flag termlist-unify-strict)))


;; ------------- Substitution into tac-ruleres objects

(define tac-subst-ruleres-branch ((x tac-ruleres-branch-p)
                                  (subst cmr::pseudo-term-subst-p))
  :returns (new-x tac-ruleres-branch-p)
  (b* (((tac-ruleres-branch x)))
    (tac-ruleres-branch
     (cmr::termlist-subst-strict x.assums subst)
     (cmr::term-subst-strict x.ctx-result subst)))
  ///
  (defret eval-of-<fn>
    (equal (tac-eval-ruleres-branch new-x env)
           (tac-eval-ruleres-branch x (tac-ev-alist subst env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch))))

  (defret tac-ruleres-branch-typed-of-<fn>
    (implies (tac-ruleres-branch-typed x type (tac-subst-ctx subst ctx))
             (tac-ruleres-branch-typed new-x type ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-typed))))

  (defret vars-of-<fn>
    (implies (not (member-equal v (cmr::term-subst-vars subst)))
             (not (member-equal v (tac-ruleres-branch-vars new-x))))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-vars))))

  (defret <fn>-of-remove-unused
    (implies (not (member-equal v (tac-ruleres-branch-vars x)))
             (equal (tac-subst-ruleres-branch x (acl2::hons-remove-assoc v subst))
                    new-x))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-vars)))))

(define tac-subst-ruleres-branchlist ((x tac-ruleres-branchlist-p)
                                      (subst cmr::pseudo-term-subst-p))
  :returns (new-x tac-ruleres-branchlist-p)
  (if (atom x)
      nil
    (cons (tac-subst-ruleres-branch (car x) subst)
          (tac-subst-ruleres-branchlist (cdr x) subst)))
  ///
  (defthm tac-subst-ruleres-branchlist-of-append
    (equal (tac-subst-ruleres-branchlist (append x y) env)
           (append (tac-subst-ruleres-branchlist x env)
                   (tac-subst-ruleres-branchlist y env))))

  (defret eval-of-<fn>
    (equal (tac-eval-ruleres-branchlist new-x env)
           (tac-eval-ruleres-branchlist x (tac-ev-alist subst env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branchlist))))
  

  (defret tac-ruleres-branchlist-typed-of-<fn>
    (implies (tac-ruleres-branchlist-typed x type (tac-subst-ctx subst ctx))
             (tac-ruleres-branchlist-typed new-x type ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-typed))))

  (defret len-of-<fn>
    (equal (len new-x) (len x)))

  (defret vars-of-<fn>
    (implies (not (member-equal v (cmr::term-subst-vars subst)))
             (not (member-equal v (tac-ruleres-branchlist-vars new-x))))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-vars))))

  (defret <fn>-of-remove-unused
    (implies (not (member-equal v (tac-ruleres-branchlist-vars x)))
             (equal (tac-subst-ruleres-branchlist x (acl2::hons-remove-assoc v subst))
                    new-x))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-vars)))))

(define tac-subst-ruleres-branchlistlist ((x tac-ruleres-branchlistlist-p)
                                          (subst cmr::pseudo-term-subst-p))
  :returns (new-x tac-ruleres-branchlistlist-p)
  (if (atom x)
      nil
    (cons (tac-subst-ruleres-branchlist (car x) subst)
          (tac-subst-ruleres-branchlistlist (cdr x) subst)))
  ///
  (defthm tac-subst-ruleres-branchlistlist-of-append
    (equal (tac-subst-ruleres-branchlistlist (append x y) env)
           (append (tac-subst-ruleres-branchlistlist x env)
                   (tac-subst-ruleres-branchlistlist y env))))

  (defret eval-of-<fn>
    (equal (tac-eval-ruleres-branchlistlist new-x env)
           (tac-eval-ruleres-branchlistlist x (tac-ev-alist subst env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branchlistlist))))

  (defret tac-ruleres-branchlistlist-typed-of-<fn>
    (implies (tac-ruleres-branchlistlist-typed x types (tac-subst-ctx subst ctx))
             (tac-ruleres-branchlistlist-typed new-x types ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlistlist-typed))))

  (defret len-of-<fn>
    (equal (len new-x) (len x))))

(define tac-subst-ruleres-branch-args ((x tac-ruleres-branch-args-p)
                                       (subst cmr::pseudo-term-subst-p))
  :returns (new-x tac-ruleres-branch-args-p)
  (b* (((tac-ruleres-branch-args x)))
    (tac-ruleres-branch-args
     (cmr::termlist-subst-strict x.assums subst)
     (cmr::termlist-subst-strict x.ctx-result-args subst)))
  ///

  (defret eval-of-<fn>
    (Equal (tac-eval-ruleres-branch-args new-x env)
           (tac-eval-ruleres-branch-args x (tac-ev-alist subst env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch-args))))

  (defret tac-ruleres-branch-args-typed-of-<fn>
    (implies (tac-ruleres-branch-args-typed x types (tac-subst-ctx subst ctx))
             (tac-ruleres-branch-args-typed new-x types ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-args-typed)))))


(define tac-subst-ruleres-branch-argslist ((x tac-ruleres-branch-argslist-p)
                                          (subst cmr::pseudo-term-subst-p))
  :returns (new-x tac-ruleres-branch-argslist-p)
  (if (atom x)
      nil
    (cons (tac-subst-ruleres-branch-args (car x) subst)
          (tac-subst-ruleres-branch-argslist (cdr x) subst)))
  ///
  (defthm tac-subst-ruleres-branch-argslist-of-append
    (equal (tac-subst-ruleres-branch-argslist (append x y) env)
           (append (tac-subst-ruleres-branch-argslist x env)
                   (tac-subst-ruleres-branch-argslist y env))))

  (defret len-of-<fn>
    (equal (len new-x) (len x)))

  (defret eval-of-<fn>
    (equal (tac-eval-ruleres-branch-argslist new-x env)
           (tac-eval-ruleres-branch-argslist x (tac-ev-alist subst env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch-argslist)))))





;; ------------- Parsing of of tac-ruleres objects



(define tac-parse-ruleres-base ((x pseudo-termp))
  :returns (mv ok (ctx-res pseudo-termp))
  (pseudo-term-case x
    :fncall (if (and (eq x.fn 'pred-in-set)
                     (eq (first x.args) 'w))
                (mv t (second x.args))
              (mv nil nil))
    :otherwise (mv nil nil))
  ///
  (defret <fn>-correct
    (implies ok
             (equal (in (cdr (assoc 'w env))
                        (tac-ev ctx-res env))
                    (tac-ev x env))))

  ;; (defret <fn>-typed
  ;;   (implies (and ok
  ;;                 (subsetp (tac-termlist-types (collect-if-branches x) ctx) '(:pred)))
  ;;            (equal (tac-term-type ctx-res ctx) :set))
  ;;   :hints(("Goal" :in-theory (enable collect-if-branches
  ;;                                     tac-termlist-types))))
  )

                
(local (in-theory (disable acl2::pseudo-termp-opener)))

(defthm tac-ev-cube-of-append
  (equal (tac-ev-cube (append x y) a)
         (and (tac-ev-cube x a)
              (tac-ev-cube y a)))
  :hints(("Goal" :in-theory (enable tac-ev-cube))))


(define tac-parse-ruleres-conj ((x pseudo-termp))
  :returns (mv (ok)
               (has-ctx)
               (assums pseudo-term-listp)
               (ctx-result pseudo-termp))
  :measure (pseudo-term-count x)
  :verify-guards nil
  (pseudo-term-case x
    :fncall (if (eq x.fn 'if)
                (b* (((list a b c) x.args))
                  (cond ((equal c ''nil)
                         (b* (((mv ok has-ctx1 assums1 ctx-result1) (tac-parse-ruleres-conj a))
                              ((unless ok) (mv nil nil nil nil))
                              ((mv ok has-ctx2 assums2 ctx-result2) (tac-parse-ruleres-conj b))
                              ((unless ok) (mv nil nil nil nil))
                              ((when (and has-ctx1 has-ctx2)) (mv nil nil nil nil)))
                           (mv t
                               (or has-ctx1 has-ctx2)
                               (append assums1 assums2)
                               (if has-ctx1 ctx-result1 ctx-result2))))
                        (t (mv nil nil nil nil))))
              (b* (((mv ok ctx-res) (tac-parse-ruleres-base x))
                   ((when ok) (mv t t nil ctx-res)))
                (mv t nil (list (pseudo-term-fix x)) nil)))
    :const (if x.val
               (mv t nil nil nil)
             (mv nil nil nil nil))
    :otherwise (mv nil nil nil nil))
  ///
  (verify-guards tac-parse-ruleres-conj)
  (local (in-theory (disable pred-in-set)))
  (defret <fn>-correct
    (implies ok
             (iff (tac-ev x env)
                  (and (tac-ev-cube assums env)
                       (or (not has-ctx)
                           (in (cdr (assoc 'w env))
                               (tac-ev ctx-result env))))))
    :hints(("Goal" :in-theory (enable tac-ev-cube)
            :induct <call>))
    :rule-classes nil)

  (defret <fn>-correct-rw
    (implies ok
             (and (implies has-ctx
                           (iff (in (cdr (assoc 'w env))
                                    (tac-eval-ruleres-branch
                                     (tac-ruleres-branch assums ctx-result)
                                     env))
                                (tac-ev x env)))
                  (implies (not has-ctx)
                           (iff (tac-ev-cube assums env)
                                (tac-ev x env)))))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch)
            :use <fn>-correct)))

  ;; (defret <fn>-typed
  ;;   (implies (subsetp (tac-termlist-types (collect-if-branches x) ctx) '(:pred))
  ;;            (and (subsetp (tac-termlist-types assums ctx) '(:pred))
  ;;                 (implies has-ctx
  ;;                          (equal (tac-term-type ctx-result ctx) :set))))
  ;;   :hints(("Goal" :in-theory (enable tac-termlist-types
  ;;                                     collect-if-branches))))
  )

(local (defcong set::sequiv equal (in a b) 2
         :hints(("Goal" :in-theory (enable in)))))

(define union-list (x)
  :verify-guards nil
  :returns (union setp)
  (if (atom x)
      nil
    (union (car x)
           (union-list (cdr x))))
  ///
  (defthm union-list-of-append
    (equal (union-list (append x y))
           (union (union-list x) (union-list y))))

  (defthm tac-typed-val-p-of-union-list
    (implies (and (tac-1typed-vallist-p x type)
                  (member-equal type '(:set :rel)))
             (tac-typed-val-p (union-list x) type))
    :hints(("Goal" :in-theory (enable tac-typed-val-p
                                      tac-1typed-vallist-p))))

  (fty::deffixcong acl2::list-equiv equal (union-list x) x))

(define tac-parse-ruleres ((x pseudo-termp))
  :returns (mv (ok)
               (results tac-ruleres-branchlist-p))
  :measure (pseudo-term-count x)
  :verify-guards nil
  (cond ((pseudo-term-case x
           :fncall (and (eq x.fn 'if)
                        (equal (first x.args) (second x.args)))
           :otherwise nil)
         (b* (((list a & c) (acl2::pseudo-term-fncall->args x))
              ((mv ok results1) (tac-parse-ruleres a))
              ((unless ok) (mv nil nil))
              ((mv ok results2) (tac-parse-ruleres c))
              ((unless ok) (mv nil nil)))
           (mv t (append results1 results2))))
        ((pseudo-term-case x
           :const (eq x.val nil)
           :otherwise nil)
         (mv t nil))
        (t (b* (((mv ok has-ctx assums ctx-result) (tac-parse-ruleres-conj x))
                ((unless (and ok has-ctx)) (mv nil nil)))
             (mv ok (list (tac-ruleres-branch assums ctx-result))))))
  ///
  (verify-guards tac-parse-ruleres)
  (defret <fn>-correct
    (implies ok
             (iff (in (cdr (assoc 'w env))
                      (union-list
                       (tac-eval-ruleres-branchlist results env)))
                  (tac-ev x env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branchlist
                                      union-list))))
)
  
  ;; (defret <fn>-typed
  ;;   (implies (subsetp (tac-termlist-types (collect-if-branches x) ctx) '(:pred))
  ;;            (tac-ruleres-branchlist-typed results :set ctx))
  ;;   :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-typed
  ;;                                     tac-ruleres-branch-typed
  ;;                                     collect-if-branches))))


;; ----------------- Well-formedness of tac positive/negative normalize rules



;; (define collect-if-branches ((x pseudo-termp))
;;   :returns (branches pseudo-term-listp)
;;   :measure (pseudo-term-count x)
;;   (pseudo-term-case x
;;     :fncall (if (eq x.fn 'if)
;;                 (b* (((list a b c) x.args)
;;                      ((when (equal c ''nil))
;;                       (append (collect-if-branches a)
;;                               (collect-if-branches b)))
;;                      ((when (equal a b))
;;                       (append (collect-if-branches a)
;;                               (collect-if-branches c))))
;;                   (list (pseudo-term-fix x)))
;;               (list (pseudo-term-fix x)))
;;     :const (if (or (eq x.val nil)
;;                    (eq x.val t))
;;                nil
;;              (list (pseudo-term-fix x)))
;;     :otherwise (list (pseudo-term-fix x))))
                     

;; ;; (defun-sk sub-subst-p (x y)
;; ;;   (forall v
;; ;;           (implies (and (pseudo-var-p v)
;; ;;                         (hons-assoc-equal v x))
;; ;;                    (and (hons-assoc-equal v y)
;; ;;                         (pseudo-term-equiv (cdr (hons-assoc-equal v y))
;; ;;                                            (cdr (hons-assoc-equal v x))))))
;; ;;   :rewrite :direct)


;; (define non-if-fncalllist-p ((x pseudo-term-listp))
;;   (if (atom x)
;;       t
;;     (and (pseudo-term-case (car x) :fncall)
;;          (not (eq 'if (pseudo-term-fncall->fn (car x))))
;;          (non-if-fncalllist-p (cdr x))))
;;   ///
;;   (defthm non-if-fncalllist-p-of-append
;;     (iff (non-if-fncalllist-p (append x y))
;;          (and (non-if-fncalllist-p x)
;;               (non-if-fncalllist-p y))))
;;   (local (defthm termlist-subst-strict-of-append
;;            (equal (cmr::termlist-subst-strict (append x y) subst)
;;                   (append (cmr::termlist-subst-strict x subst)
;;                           (cmr::termlist-subst-strict y subst)))
;;            :hints(("Goal" :in-theory (enable append cmr::termlist-subst-strict)))))

;;   (local (defthmd not-equal-quote-nil-by-pseudo-term-kind
;;            (implies (not (equal (pseudo-term-kind x) :quote))
;;                     (not (equal x ''nil)))))
  
;;   (defthm not-const-of-term-subst-strict-when-non-if-fncallist-p-of-collect
;;     (implies (and (non-if-fncalllist-p (collect-if-branches x))
;;                   (not (equal (pseudo-term-fix x) ''nil)))
;;              (not (equal (cmr::term-subst-strict x subst) ''nil)))
;;     :hints(("Goal" :in-theory (enable (:i collect-if-branches)
;;                                       not-equal-quote-nil-by-pseudo-term-kind)
;;             :induct (collect-if-branches x)
;;             :expand ((cmr::term-subst-strict x subst)
;;                      (collect-if-branches x)))))

;;   (local (defthm cdr-of-termlist-subst-strict
;;            (equal (cdr (cmr::termlist-subst-strict x subst))
;;                   (cmr::termlist-subst-strict (cdr x) subst))
;;            :hints(("Goal" :expand ((cmr::termlist-subst-strict x subst)
;;                                    (cmr::termlist-subst-strict nil subst))))))

;;   (local (defthm car-of-termlist-subst-strict
;;            (equal (car (cmr::termlist-subst-strict x subst))
;;                   (cmr::term-subst-strict (car x) subst))
;;            :hints(("Goal" :expand ((cmr::termlist-subst-strict x subst)
;;                                    (cmr::term-subst-strict nil subst))))))

;;   (local (defthm term-subst-strict-of-quote-nil
;;            (equal (cmr::term-subst-strict ''nil subst)
;;                   ''nil)
;;            :hints (("goal" :expand ((cmr::term-subst-strict ''nil subst))))))
            
;;   (defthm collect-if-branches-of-term-subst-strict-when-fncallist-p
;;     (implies (non-if-fncalllist-p (collect-if-branches x))
;;              (equal (collect-if-branches (cmr::term-subst-strict x subst))
;;                     (cmr::termlist-subst-strict (collect-if-branches x) subst)))
;;     :hints(("Goal" :in-theory (enable (:i collect-if-branches))
;;             :induct (collect-if-branches x)
;;             :expand ((cmr::term-subst-strict x subst)
;;                      (cmr::termlist-subst-strict nil subst)
;;                      (:free (a b) (cmr::termlist-subst-strict (cons a b) subst))
;;                      (collect-if-branches x)
;;                      (:free (fn args) (collect-if-branches (pseudo-term-fncall fn args))))))))

;; (define tac-pred-rewrites-branches-are-fncalls ((x tac-rewritelist-p))
;;   (if (atom x)
;;       t
;;     (and (or (not (mbt (consp (car x))))
;;              (non-if-fncalllist-p (collect-if-branches (cmr::rewrite->rhs (cdar x)))))
;;          (tac-pred-rewrites-branches-are-fncalls (cdr x))))
;;   ///
;;   (defthm tac-pred-rewrites-branches-are-fncalls-of-tac-positive-normalize-rules
;;     (tac-pred-rewrites-branches-are-fncalls (tac-positive-normalize-rules))
;;     :hints(("Goal" :in-theory (enable (tac-positive-normalize-rules)))))

;;   (defthm tac-pred-rewrites-branches-are-fncalls-of-tac-negative-normalize-rules
;;     (tac-pred-rewrites-branches-are-fncalls (tac-negative-normalize-rules))
;;     :hints(("Goal" :in-theory (enable (tac-negative-normalize-rules)))))
  
;;   (local (in-theory (enable tac-rewritelist-fix))))

(define is-pred-in-set ((x pseudo-termp))
  (pseudo-term-case x
    :fncall (eq x.fn 'pred-in-set)
    :otherwise nil))

(defsection tac-pred-rewrite-rhs-typed
  (defun-sk tac-pred-rewrite-rhs-typed (rule)
    (forall (ctx)
            (b* (((cmr::rewrite rule))
                 (lhs-type (tac-term-type rule.lhs ctx))
                 ((mv ok rhs-parsed) (tac-parse-ruleres rule.rhs)))
              (implies (and lhs-type
                            (is-pred-in-set rule.lhs)
                            (let* ((binding-hyp (and (is-special-instantiation-rule rule)
                                                     (special-instantiation-rule-binding-hyp rule))))
                              (or (not binding-hyp)
                                  (tac-term-type binding-hyp ctx))))
                       (and ok
                            (tac-ruleres-branchlist-typed rhs-parsed :set ctx))
                       ;; (subsetp (tac-termlist-types (collect-if-branches rule.rhs) ctx)
                       ;;          '(:pred))
                       )))
    :rewrite :direct)

  (in-theory (disable tac-pred-rewrite-rhs-typed)))





(define tac-pred-rewrites-rhs-typed (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-pred-rewrite-rhs-typed (cdar rules)))
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
    :hints (("goal" :expand ((:free (a b) (tac-pred-rewrites-rhs-typed (cons a b)))
                             (:free (x) (tac-pred-rewrite-rhs-typed x))
                             (:free (a b) (tac-pred-rewrites-rhs-typed (cons a b)))
                             (:free (a b ctx) (tac-ruleres-branchlist-typed (cons a b) :set ctx))
                             (:free (a b ctx) (tac-ruleres-branchlist-typed nil :set ctx)))
             :in-theory (e/d (cmr::term-subst-strict
                              tac-ruleres-branch-typed
                              tac-termlist-types
                              cmr::termlist-subst-strict
                              cmr::equal-of-pseudo-term-fncall
                              (tac-positive-normalize-rules))
                             (tac-pred-rewrite-rhs-typed-necc)))))

  (defthm tac-pred-rewrites-rhs-typed-of-tac-negative-normalize-rules
    (tac-pred-rewrites-rhs-typed (tac-negative-normalize-rules))
    :hints (("goal" :expand ((:free (a b) (tac-pred-rewrites-rhs-typed (cons a b)))
                             (:free (x) (tac-pred-rewrite-rhs-typed x))
                             (:free (a b) (tac-pred-rewrites-rhs-typed (cons a b)))
                             (:free (a b ctx) (tac-ruleres-branchlist-typed (cons a b) :set ctx))
                             (:free (a b ctx) (tac-ruleres-branchlist-typed nil :set ctx)))
             :in-theory (e/d (cmr::term-subst-strict
                              tac-ruleres-branch-typed
                              tac-termlist-types
                              cmr::termlist-subst-strict
                              cmr::equal-of-pseudo-term-fncall
                              (tac-negative-normalize-rules))
                             (tac-pred-rewrite-rhs-typed-necc)))))
  )

(defsection tac-pred-rewrite-hyps-ok
  (defun-sk tac-pred-rewrite-hyps-ok (rule)
    (forall (ctx env)
            (b* (((cmr::rewrite rule)))
              (implies (and (tac-typed-env-p env ctx)
                            (tac-term-type rule.lhs ctx))
                       (and (implies (and (is-special-instantiation-rule rule)
                                          (tac-term-type (special-instantiation-rule-binding-hyp rule) ctx)
                                          (tac-ev (special-instantiation-rule-binding-hyp rule) env))
                                     (tac-ev-cube rule.hyps env))
                            (implies (not (is-special-instantiation-rule rule))
                                     (tac-ev-cube rule.hyps env))))))
    :rewrite :direct)

  (in-theory (disable tac-pred-rewrite-hyps-ok)))



(define tac-pred-rewrites-hyps-ok (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-pred-rewrite-hyps-ok (cdar rules)))
         (tac-pred-rewrites-hyps-ok (cdr rules))))
  ///
  (local (defthm car-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (car x) a))))
  (local (defthm cdr-when-equal-cons
           (implies (equal x (cons a b))
                    (equal (cdr x) b))))
  
  (defthm tac-pred-rewrites-hyps-ok-of-tac-positive-normalize-rules
    (tac-pred-rewrites-hyps-ok (tac-positive-normalize-rules))
    :hints (("goal" :expand ((:free (x) (tac-pred-rewrite-hyps-ok x))
                             (:free (a b) (tac-pred-rewrites-hyps-ok (cons a b))))
             :in-theory (e/d (cmr::term-subst-strict
                              cmr::termlist-subst-strict
                              cmr::equal-of-pseudo-term-fncall
                              tac-ev-cube
                              (tac-positive-normalize-rules))
                             (tac-pred-rewrite-hyps-ok-necc)))))

  (defthm tac-pred-rewrites-hyps-ok-of-tac-negative-normalize-rules
    (tac-pred-rewrites-hyps-ok (tac-negative-normalize-rules))
    :hints (("goal" :expand ((:free (x) (tac-pred-rewrite-hyps-ok x))
                             (:free (a b) (tac-pred-rewrites-hyps-ok (cons a b))))
             :in-theory (e/d (cmr::term-subst-strict
                              cmr::termlist-subst-strict
                              cmr::equal-of-pseudo-term-fncall
                              tac-ev-cube
                              (tac-negative-normalize-rules))
                             (tac-pred-rewrite-hyps-ok-necc))))))



(define is-pred-in-set-w ((x pseudo-termp))
  (pseudo-term-case x
    :fncall (and (eq x.fn 'pred-in-set)
                 (consp x.args)
                 (eq (first x.args) 'w))
    :otherwise nil))

(define tac-pred-rewrite-parse-ok ((rule cmr::rewrite-p))
  :guard-hints (("goal" :in-theory (enable is-pred-in-set-w)))
  (b* (((cmr::rewrite rule))
       ((mv ok results) (tac-parse-ruleres rule.rhs)))
    (or (not (is-pred-in-set rule.lhs))
        (and (is-pred-in-set-w rule.lhs)
             (not (member-equal 'w (cmr::term-vars (cadr (pseudo-term-call->args rule.lhs)))))
             (or (not (is-special-instantiation-rule rule))
                 (not (member-equal 'w (cmr::term-vars
                                        (special-instantiation-rule-binding-hyp rule)))))
             ok
             (not (member-equal 'w (tac-ruleres-branchlist-vars results))))))
  ///
  (defthmd tac-pred-rewrite-parse-ok-implies
    (b* (((cmr::rewrite rule))
         ((mv ok results) (tac-parse-ruleres rule.rhs)))
      (implies (and (tac-pred-rewrite-parse-ok rule)
                    (is-pred-in-set rule.lhs))
               (and (equal (pseudo-term-kind rule.lhs) :fncall)
                    (equal (pseudo-term-fncall->fn rule.lhs) 'pred-in-set)
                    (equal (first (pseudo-term-call->args rule.lhs)) 'w)
                    (is-pred-in-set-w rule.lhs)
                    (not (member-equal 'w (cmr::term-vars (cadr (pseudo-term-call->args rule.lhs)))))
                    ok
                    (not (member-equal 'w (tac-ruleres-branchlist-vars results)))
                    (implies (is-special-instantiation-rule rule)
                             (not (member-equal 'w (cmr::term-vars
                                                    (special-instantiation-rule-binding-hyp rule))))))))
    :hints(("Goal" :in-theory (enable is-pred-in-set-w)))))
                    

(define tac-pred-rewrites-parse-ok ((rules tac-rewritelist-p))
  (if (atom rules)
      t
    (and (or (not (mbt (consp (car rules))))
             (tac-pred-rewrite-parse-ok (cdar rules)))
         (tac-pred-rewrites-parse-ok (cdr rules))))
  ///
  (defthm tac-pred-rewriteso-parse-ok-of-positive-normalize
    (tac-pred-rewrites-parse-ok (tac-positive-normalize-rules))
    :hints(("Goal" :in-theory (enable (tac-positive-normalize-rules)))))

  (defthm tac-pred-rewrites-parse-ok-of-negative-normalize
    (tac-pred-rewrites-parse-ok (tac-negative-normalize-rules))
    :hints(("Goal" :in-theory (enable (tac-negative-normalize-rules)))))

  (local (in-theory (enable tac-rewritelist-fix))))





(define collect-is-special-instantiation-rule ((x tac-rewritelist-p))
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (cons (is-special-instantiation-rule (cdar x))
              (collect-is-special-instantiation-rule (cdr x)))
      (collect-is-special-instantiation-rule (cdr x))))
  ///
  (local (in-theory (enable tac-rewritelist-fix))))

(define collect-special-instantiation-rule-hyps ((x tac-rewritelist-p))
  (if (atom x)
      nil
    (if (and (mbt (consp (car x)))
             (is-special-instantiation-rule (cdar x)))
        (cons (special-instantiation-rule-binding-hyp (cdar x))
              (collect-special-instantiation-rule-hyps (cdr x)))
      (collect-special-instantiation-rule-hyps (cdr x))))
  ///
  (local (in-theory (enable tac-rewritelist-fix))))


(local (defthm prefixp-transitive
         (implies (and (acl2::prefixp a b)
                       (acl2::prefixp b c))
                  (acl2::prefixp a c))
         :hints(("Goal" :in-theory (enable acl2::prefixp)))))
(local (defthm prefixp-reflexive
         (acl2::prefixp x x)
         :hints(("Goal" :in-theory (enable acl2::prefixp)))))

(local (defthm equal-pseudo-fnsym-fix-forward
         (implies (equal (pseudo-fnsym-fix x) y)
                  (pseudo-fnsym-equiv x y))
         :rule-classes :forward-chaining))


(define union-multiarglists ((x true-list-listp))
  :verify-guards nil
  :returns (args true-listp)
  (if (atom x)
      nil
    (cons (union-list (car x))
          (union-multiarglists (cdr x))))
  ///
  (defthm tac-typed-vallist-p-of-union-multiarglist
    (implies (and (tac-typed-multiarglist-p x types)
                  (subsetp-equal types '(:set :rel)))
             (tac-typed-vallist-p (union-multiarglists x) types))
    :hints(("Goal" :in-theory (enable tac-typed-vallist-p
                                      tac-typed-multiarglist-p))))
  (local (in-theory (enable acl2::true-list-list-fix))))


(define tac-typed-vallistlist-p ((x true-list-listp)
                                 (types tac-typelist-p))
  (if (atom x)
      t
    (and (tac-typed-vallist-p (car x) types)
         (tac-typed-vallistlist-p (cdr x) types)))
  ///
  (defthm tac-typed-vallistlist-p-of-append
    (implies (and (tac-typed-vallistlist-p x types)
                  (tac-typed-vallistlist-p y types))
             (tac-typed-vallistlist-p (append x y) types))))

(define lists-have-lengths ((n natp) x)
  (if (atom x)
      t
    (and (equal (len (car x)) (lnfix n))
         (lists-have-lengths n (cdr x))))
  ///
  (defthm lists-have-lengths-of-append
    (iff (lists-have-lengths n (append x y))
         (and (lists-have-lengths n x)
              (lists-have-lengths n y)))))

(define cons-to-each (x (y true-list-listp))
  :returns (new-y true-list-listp)
  (if (atom y)
      nil
    (cons (cons x (true-list-fix (car y)))
          (cons-to-each x (cdr y))))
  ///
  (defthm tac-typed-vallistlist-p-of-cons-to-each
    (implies (and (tac-typed-val-p x (car types))
                  (tac-typed-vallistlist-p y (cdr types)))
             (tac-typed-vallistlist-p (cons-to-each x y) types))
    :hints(("Goal" :in-theory (enable tac-typed-vallistlist-p
                                      tac-typed-vallist-p))))

  (defthm cons-to-each-of-append
    (equal (cons-to-each x (append y z))
           (append (cons-to-each x y)
                   (cons-to-each x z))))

  (defret lists-have-lengths-of-<fn>
    (implies (and (posp n)
                  (lists-have-lengths (1- n) y))
             (lists-have-lengths n new-y))
    :hints(("Goal" :in-theory (enable lists-have-lengths)))))

(define cons-product ((x true-listp)
                      (y true-list-listp))
  :returns (prod true-list-listp)
  (if (atom x)
      nil
    (append (cons-to-each (car x) y)
            (cons-product (cdr x) y)))
  ///
  (defthm tac-typed-vallistlist-p-of-cons-product
    (implies (and (tac-1typed-vallist-p x (car types))
                  (tac-typed-vallistlist-p y (cdr types)))
             (tac-typed-vallistlist-p (cons-product x y) types))
    :hints(("Goal" :in-theory (enable tac-typed-vallistlist-p
                                      tac-1typed-vallist-p))))

  (defret lists-have-lengths-of-<fn>
    (implies (and (posp n)
                  (lists-have-lengths (1- n) y))
             (lists-have-lengths n prod))
    :hints(("Goal" :in-theory (enable lists-have-lengths)))))





(define arglist-product ((x true-list-listp))
  :returns (product)
  (if (atom x)
      (list nil)
    (cons-product (car x) (arglist-product (cdr x))))
  ///
  (defthm tac-typed-vallistlist-p-of-arglist
    (implies (and (tac-typed-multiarglist-p x types)
                  (equal (len types) (len x)))
             (tac-typed-vallistlist-p (arglist-product x) types))
    :hints(("Goal" :in-theory (enable tac-typed-multiarglist-p
                                      tac-typed-vallistlist-p
                                      tac-typed-vallist-p))))

  (defret lists-have-lengths-of-<fn>-lemma
    (lists-have-lengths (len x) product))

  (defret lists-have-lengths-of-<fn>
    (implies (equal (len x) (nfix n))
             (lists-have-lengths n product))
    :hints(("Goal" :in-theory (enable lists-have-lengths)))))

(define arglist-unions ((x true-list-listp))
  :verify-guards nil
  (if (atom x)
      nil
    (cons (union-list (car x))
          (arglist-unions (cdr x)))))

(fty::deffixcong pseudo-fnsym-equiv equal (tac-ev-apply fn args) fn
  :hints(("Goal" :in-theory (enable tac-ev-apply pseudo-fnsym-fix))))
(fty::deffixcong acl2::list-equiv equal (tac-ev-apply fn args) args
  :hints(("Goal" :in-theory (enable tac-ev-apply))))

(define tac-ev-apply-to-arglists ((fn pseudo-fnsym-p)
                                  (args true-list-listp))
  :verify-guards nil
  (if (atom args)
      nil
    (cons (tac-ev-apply fn (car args))
          (tac-ev-apply-to-arglists fn (cdr args))))
  ///
  (defthm tac-ev-apply-to-arglists-of-append
    (equal (tac-ev-apply-to-arglists fn (append x y))
           (append (tac-ev-apply-to-arglists fn x)
                   (tac-ev-apply-to-arglists fn y)))))


(define remove-entries-with-nil ((x true-list-listp))
  (if (atom x)
      nil
    (if (member-equal nil (car x))
        (remove-entries-with-nil (cdr x))
      (cons (acl2::true-list-fix (car x))
            (remove-entries-with-nil (cdr x)))))
  ///
  (defthm remove-entries-with-nil-of-append
    (equal (remove-entries-with-nil (append x y))
           (append (remove-entries-with-nil x)
                   (remove-entries-with-nil y))))
  (local (in-theory (enable acl2::true-list-list-fix))))

(define tac-context-fn-p ((x pseudo-fnsym-p))
  (and (member-eq (pseudo-fnsym-fix x) '(setimage setpreimage setintersect
                                                  relidentity relcompose relinverse relprod relintersect))
       t)
  ///
  (defthm tac-function-return-type-when-tac-context-fn-p
    (implies (tac-context-fn-p x)
             (tac-function-return-type x)))

  (defthm tac-ev-apply-nil-when-tac-context-fn-p
    (implies (tac-context-fn-p fn)
             (equal (tac-ev-apply fn nil) nil))
    :hints(("Goal" :in-theory (enable tac-ev-apply
                                      tac-context-fn-p))))

  (local (in-theory (enable set::union-symmetric set::union-commutative)))

  (local (defthm tac-typed-val-p-of-rel
           (implies (tac-typed-val-p x :rel)
                    (relation-p x))
           :hints(("Goal" :in-theory (enable tac-typed-val-p)))))

  (local (defthm intersect-of-union-1
           (equal (intersect (union x y) z)
                  (union (intersect x z)
                         (intersect y z)))
           :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                              pick-a-point-subset-strategy)))))

  (local (defthm intersect-of-union-2
           (equal (intersect x (union y z))
                  (union (intersect x y)
                         (intersect x z)))
           :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                              pick-a-point-subset-strategy)))))

  (local (defthm cartesian-of-union-1
           (equal (cartesian (union x y) z)
                  (union (cartesian x z)
                         (cartesian y z)))
           :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                              pick-a-point-subset-strategy
                                              in-of-cartesian)))))

  (local (defthm cartesian-of-union-2
           (equal (cartesian x (union y z))
                  (union (cartesian x y)
                         (cartesian x z)))
           :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                              pick-a-point-subset-strategy
                                              in-of-cartesian)))))

  (local (defthm preimage-of-union-1
           (implies (relation-p z)
                    (equal (preimage (union x y) z)
                           (union (preimage x z)
                                  (preimage y z))))
           :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                              pick-a-point-subset-strategy
                                              in-of-preimage-rw)))))

  (local (defthm preimage-of-union-2
           (implies (and (relation-p y)
                         (relation-p z))
                    (equal (preimage x (union y z))
                           (union (preimage x y)
                                  (preimage x z))))
           :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                              pick-a-point-subset-strategy
                                              in-of-preimage-rw)))))

  (local (defthm preimage-of-union-1
           (implies (relation-p z)
                    (equal (preimage (union x y) z)
                           (union (preimage x z)
                                  (preimage y z))))
           :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                              pick-a-point-subset-strategy
                                              in-of-preimage-rw)))))

  (local (defthm preimage-of-union-2
           (implies (and (relation-p y)
                         (relation-p z))
                    (equal (preimage x (union y z))
                           (union (preimage x y)
                                  (preimage x z))))
           :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                              pick-a-point-subset-strategy
                                              in-of-preimage-rw)))))

  (local (defund empty-set () nil))
  (local (defthm setp-empty-set
           (setp (empty-set))))
  (local (defthm preimage-of-nil-2
           (equal (preimage x nil) (empty-set))
           :hints (("goal" :in-theory (e/d (set::double-containment-no-backchain-limit
                                              pick-a-point-subset-strategy
                                              in-of-preimage-rw)
                                           ((empty-set) (:t empty-set))))
                   (set::pick-a-point-subset-hint id clause world stable-under-simplificationp)
                   (and stable-under-simplificationp
                        '(:in-theory (enable empty-set))))))

  
  (local (defthm image-of-nil-2
           (equal (image x nil) (empty-set))
           :hints (("goal" :in-theory (e/d (set::double-containment-no-backchain-limit
                                              pick-a-point-subset-strategy
                                              in-of-image-rw)
                                           ((empty-set) (:t empty-set))))
                   (set::pick-a-point-subset-hint id clause world stable-under-simplificationp)
                   (and stable-under-simplificationp
                        '(:in-theory (enable empty-set))))))
  
  (defthm tac-context-fn-apply-when-member-nil
    (implies (and (tac-context-fn-p fn)
                  (member nil (take (len (tac-function-argument-types fn)) args)))
             (equal (tac-ev-apply fn args) nil))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable tac-ev-apply)))))
    
  
  (defthm union-of-tac-ev-apply-to-arglists-of-cons-to-each-union
    (implies (and (tac-context-fn-p fn)
                  (tac-typed-val-p x (car (tac-function-argument-types fn)))
                  (tac-typed-val-p y (car (tac-function-argument-types fn)))
                  (tac-typed-vallistlist-p z (cdr (tac-function-argument-types fn))))
             (equal (union-list (tac-ev-apply-to-arglists fn (cons-to-each (union x y) z)))
                    (union (union-list (tac-ev-apply-to-arglists fn (cons-to-each x z)))
                           (union-list (tac-ev-apply-to-arglists fn (cons-to-each y z))))))
    :hints (("goal" :in-theory (enable union-list cons-to-each
                                       tac-ev-apply-to-arglists
                                       tac-typed-vallistlist-p
                                       tac-ev-apply))))

  (defthm union-of-tac-ev-apply-to-arglists-of-cons-to-each-union-2
    (implies (and (tac-context-fn-p fn)
                  (< 1 (len (tac-function-argument-types fn)))
                  (tac-typed-val-p x (cadr (tac-function-argument-types fn)))
                  (tac-typed-val-p y (cadr (tac-function-argument-types fn)))
                  (tac-typed-vallistlist-p z (cddr (tac-function-argument-types fn))))
             (equal (union-list (tac-ev-apply-to-arglists fn (cons-to-each x1 (cons-to-each (union x y) z))))
                    (union (union-list (tac-ev-apply-to-arglists fn (cons-to-each x1 (cons-to-each x z))))
                           (union-list (tac-ev-apply-to-arglists fn (cons-to-each x1 (cons-to-each y z)))))))
    :hints (("goal"
             :induct (len z)
             :in-theory (enable cons-to-each
                                tac-ev-apply-to-arglists
                                tac-typed-vallistlist-p
                                union-list))
            (and stable-under-simplificationp
                 '(:in-theory (enable tac-ev-apply)))))
  
           
  (defthm union-of-tac-ev-apply-to-arglists-of-cons-to-each-nil
    (implies (and (tac-context-fn-p fn)
                  (tac-typed-vallistlist-p z (cdr (tac-function-argument-types fn))))
             (equal (union-list (tac-ev-apply-to-arglists fn (cons-to-each nil z)))
                    nil))
    :hints (("goal" :in-theory (enable union-list cons-to-each
                                       tac-ev-apply-to-arglists
                                       tac-typed-vallistlist-p
                                       tac-ev-apply))))

  (defthm union-of-tac-ev-apply-to-arglists-of-cons-to-each-nil-2
    (implies (and (tac-context-fn-p fn)
                  (< 1 (len (tac-function-argument-types fn)))
                  (tac-typed-vallistlist-p z (cddr (tac-function-argument-types fn))))
             (equal (union-list (tac-ev-apply-to-arglists fn (cons-to-each x (cons-to-each nil z))))
                    nil))
    :hints (("goal" :in-theory (enable union-list cons-to-each
                                       tac-ev-apply-to-arglists
                                       tac-typed-vallistlist-p
                                       tac-ev-apply)
             :induct (len z))))

  (defthm function-argument-types-when-tac-context-fn-p
    (implies (tac-context-fn-p fn)
             (subsetp-equal (tac-function-argument-types fn) '(:set :rel))))

  (defthm function-argument-types-when-tac-context-fn-p-2
    (implies (tac-context-fn-p fn)
             (member-equal (car (tac-function-argument-types fn)) '(:set :rel))))
  
  (defthm union-of-tac-ev-apply-to-arglists-of-cons-product
    (implies (and (tac-context-fn-p fn)
                  (tac-1typed-vallist-p x (car (tac-function-argument-types fn)))
                  (tac-typed-vallistlist-p y (cdr (tac-function-argument-types fn))))
             (equal (union-list (tac-ev-apply-to-arglists fn (cons-product x y)))
                    (union-list (tac-ev-apply-to-arglists fn (cons-to-each (union-list x) y)))))
    :hints (("goal" :in-theory (e/d (cons-product union-list cons-to-each
                                                  tac-1typed-vallist-p)
                                    (tac-context-fn-p))
             :induct (len x)
             :expand ((tac-ev-apply-to-arglists fn nil)))))

  (defthm union-of-tac-ev-apply-to-arglists-of-cons-product-2
    (implies (and (tac-context-fn-p fn)
                  (< 1 (len (tac-function-argument-types fn)))
                  (tac-1typed-vallist-p x (cadr (tac-function-argument-types fn)))
                  (tac-typed-vallistlist-p y (cddr (tac-function-argument-types fn))))
             (equal (union-list (tac-ev-apply-to-arglists fn (cons-to-each x1 (cons-product x y))))
                    (union-list (tac-ev-apply-to-arglists fn (cons-to-each x1 (cons-to-each (union-list x) y))))))
    :hints (("goal" :in-theory (e/d (cons-product union-list cons-to-each
                                                  tac-1typed-vallist-p)
                                    (tac-context-fn-p))
             :induct (len x)
             :expand ((tac-ev-apply-to-arglists fn nil)))))

  (defthm tac-ev-apply-of-union-lists-when-tac-context-fn-p
    (implies (and (tac-context-fn-p fn)
                  (tac-typed-multiarglist-p x (tac-function-argument-types fn))
                  (equal (len x) (len (tac-function-argument-types fn))))
             (equal (union-list (tac-ev-apply-to-arglists fn (arglist-product x)))
                    (tac-ev-apply fn (union-multiarglists x))))
    :hints (("goal" :expand ((arglist-product x)
                             (arglist-product (cdr x))
                             (arglist-product (cddr x))
                             (union-multiarglists x)
                             (union-multiarglists (cdr x))
                             (union-multiarglists (cddr x))
                             (:free (x a b) (cons-to-each x (cons a b)))
                             (:free (x) (cons-to-each x nil))
                             (:free (a b) (union-list (cons a b)))
                             (:free (fn a b) (tac-ev-apply-to-arglists fn (cons a b)))
                             (:free (fn a b) (tac-ev-apply-to-arglists fn nil))
                             (:free (x a b) (tac-typed-multiarglist-p x (cons a b))))
             :do-not-induct t
             :in-theory (disable (tac-ev-apply-to-arglists)))
            (and stable-under-simplificationp
                 '(:in-theory (enable tac-ev-apply)))))

  (defthm tac-ev-apply-to-arglists-of-remove-entries-with-nil-when-tac-context-fn-p
    (implies (and (tac-context-fn-p fn)
                  (lists-have-lengths (len (tac-function-argument-types fn)) x))
             (equal (union-list (tac-ev-apply-to-arglists fn (remove-entries-with-nil x)))
                    (union-list (tac-ev-apply-to-arglists fn x))))
    :hints(("Goal" :in-theory (enable remove-entries-with-nil
                                      lists-have-lengths
                                      tac-ev-apply-to-arglists)
            :induct (len x))
           (and stable-under-simplificationp
                '(:in-theory (enable tac-ev-apply
                                     union-list)))))

  (local (defthm lists-have-lengths-of-remove-entries-with-nil
           (implies (lists-have-lengths n x)
                    (lists-have-lengths n (remove-entries-with-nil x)))
           :hints(("Goal" :in-theory (enable lists-have-lengths remove-entries-with-nil)))))
  
  (defthm rewrite-tac-ev-apply-to-arglists-under-remove-entries-with-nil
    (implies (and (tac-context-fn-p fn)
                  (lists-have-lengths (len (tac-function-argument-types fn)) x)
                  (equal x1 (remove-entries-with-nil x))
                  (bind-free
                   (case-match x1
                     (('remove-entries-with-nil x2) `((x2 . ,x2) (flag . 't)))
                     (& `((x2 . ,x1) (flag . 'nil))))
                   (x2 flag))
                  ;; (syntaxp ((lambda (mfc state)
                  ;;             (declare (ignore state))
                  ;;             (progn$ (cw "unify subst: ~x0~%" (mfc-unify-subst mfc))
                  ;;                     t))
                  ;;           mfc state))
                  (syntaxp (not (equal x2 x)))
                  (equal x1 (if flag (remove-entries-with-nil x2) x2))
                  (lists-have-lengths (len (tac-function-argument-types fn)) x2))
             (equal (union-list (tac-ev-apply-to-arglists fn x))
                    (union-list (tac-ev-apply-to-arglists fn x2))))
    :hints(("Goal" :in-theory (disable tac-context-fn-p
                                       tac-ev-apply-to-arglists-of-remove-entries-with-nil-when-tac-context-fn-p)
            :use ((:instance tac-ev-apply-to-arglists-of-remove-entries-with-nil-when-tac-context-fn-p (x x))
                  (:instance tac-ev-apply-to-arglists-of-remove-entries-with-nil-when-tac-context-fn-p (x x2)))))
    ))



(define tac-ruleres-branch-argslist-have-lengths ((n natp) (x tac-ruleres-branch-argslist-p))
  (if (atom x)
      t
    (and (equal (lnfix n) (len (tac-ruleres-branch-args->ctx-result-args (car x))))
         (tac-ruleres-branch-argslist-have-lengths n (cdr x))))
  ///
  (defthm tac-ruleres-branch-argslist-have-lengths-of-append
    (implies (and (tac-ruleres-branch-argslist-have-lengths n x)
                  (tac-ruleres-branch-argslist-have-lengths n y))
             (tac-ruleres-branch-argslist-have-lengths n (append x y)))))

(local (in-theory (disable nfix)))

(define tac-ruleres-branch-argslist-no-assums-without-args ((x tac-ruleres-branch-argslist-p))
  (if (atom x)
      t
    (and (b* (((tac-ruleres-branch-args x1) (car x)))
           (implies (not (consp x1.ctx-result-args))
                    (not (consp x1.assums))))
         (tac-ruleres-branch-argslist-no-assums-without-args (cdr x))))
  ///
  (defthm tac-ruleres-branch-argslist-no-assums-without-args-of-append
    (implies (and (tac-ruleres-branch-argslist-no-assums-without-args x)
                  (tac-ruleres-branch-argslist-no-assums-without-args y))
             (tac-ruleres-branch-argslist-no-assums-without-args (append x y)))))

(local (defthm termlist-vars-of-append
         (iff (member v (cmr::termlist-vars (append a b)))
              (or (member v (cmr::termlist-vars a))
                  (member v (cmr::termlist-vars b))))
         :hints(("Goal" :in-theory (enable cmr::termlist-vars)))))
                

(define tac-ruleres-branch-product-with-branch-argslist ((x tac-ruleres-branch-p)
                                                                      (y tac-ruleres-branch-argslist-p))
  :returns (new-y tac-ruleres-branch-argslist-p)
  (if (atom y)
      nil
    (cons (b* (((tac-ruleres-branch x))
               ((tac-ruleres-branch-args y1) (car y)))
            (tac-ruleres-branch-args (append x.assums y1.assums)
                                                  (cons x.ctx-result y1.ctx-result-args)))
          (tac-ruleres-branch-product-with-branch-argslist x (cdr y))))
  ///
  (defret vars-of-<fn>
    (implies (and (not (member v (tac-ruleres-branch-vars x)))
                  (not (member v (tac-ruleres-branch-argslist-vars y))))
             (not (member v (tac-ruleres-branch-argslist-vars new-y))))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-vars
                                      tac-ruleres-branch-argslist-vars
                                      tac-ruleres-branch-args-vars
                                      cmr::termlist-vars))))
  
  (local (defthm remove-entries-with-nil-of-cons-to-each-nil
           (equal (remove-entries-with-nil (cons-to-each nil x)) nil)
           :hints(("Goal" :in-theory (enable remove-entries-with-nil cons-to-each)))))
  (defret lengths-of-<fn>
    (implies (and (tac-ruleres-branch-argslist-have-lengths (1- n) y)
                  (posp n))
             (tac-ruleres-branch-argslist-have-lengths n new-y))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-argslist-have-lengths
                                      nfix))))
     
  (defret eval-of-<fn>
    (implies (tac-ruleres-branch-argslist-no-assums-without-args y)
             (equal (remove-entries-with-nil (tac-eval-ruleres-branch-argslist new-y env))
                    (remove-entries-with-nil
                     (cons-to-each (tac-eval-ruleres-branch x env)
                                   (tac-eval-ruleres-branch-argslist y env)))))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch-argslist
                                      tac-eval-ruleres-branch
                                      tac-eval-ruleres-branch-args
                                      tac-ruleres-branch-argslist-no-assums-without-args
                                      remove-entries-with-nil
                                      tac-ev-cube
                                      cons-to-each))))

  (defret tac-ruleres-branch-argslist-no-assums-without-args-of-<fn>
    (tac-ruleres-branch-argslist-no-assums-without-args new-y)
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-argslist-no-assums-without-args))))

  (defret types-of-<fn>
    (implies (and (tac-ruleres-branch-typed x (car types) Ctx)
                  (tac-ruleres-branch-argslist-typed y (cdr types) ctx)
                  (not (member-equal nil (tac-typelist-fix types))))
             (tac-ruleres-branch-argslist-typed new-y types ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-typed
                                      tac-ruleres-branch-argslist-typed
                                      tac-ruleres-branch-args-typed
                                      tac-termlist-types acl2::prefixp tac-typelist-fix)
            :induct <call>))))

(local (defthm member-tac-ruleres-branch-arslist-vars-of-append
         (iff (member v (tac-ruleres-branch-argslist-vars (append a b)))
              (or (member v (tac-ruleres-branch-argslist-vars a))
                  (member v (tac-ruleres-branch-argslist-vars b))))
         :hints(("Goal" :in-theory (enable tac-ruleres-branch-argslist-vars)))))

(define tac-ruleres-branchlist-product-with-branch-argslist ((x tac-ruleres-branchlist-p)
                                                                          (y tac-ruleres-branch-argslist-p))
  :Returns (new-y tac-ruleres-branch-argslist-p)
  (if (atom x)
      nil
    (append (tac-ruleres-branch-product-with-branch-argslist (car x) y)
            (tac-ruleres-branchlist-product-with-branch-argslist (cdr x) y)))
  ///
  (defret vars-of-<fn>
    (implies (and (not (member v (tac-ruleres-branchlist-vars x)))
                  (not (member v (tac-ruleres-branch-argslist-vars y))))
             (not (member v (tac-ruleres-branch-argslist-vars new-y))))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-vars
                                      tac-ruleres-branch-argslist-vars
                                      tac-ruleres-branch-args-vars))))
  (defret eval-of-<fn>
    (implies (tac-ruleres-branch-argslist-no-assums-without-args y)
             (equal (remove-entries-with-nil
                     (tac-eval-ruleres-branch-argslist new-y env))
                    (remove-entries-with-nil
                     (cons-product (tac-eval-ruleres-branchlist x env)
                                   (tac-eval-ruleres-branch-argslist y env)))))
    :hints(("Goal" :in-theory (enable cons-product
                                      tac-eval-ruleres-branchlist
                                      tac-eval-ruleres-branch-argslist))))

  (defret lengths-of-<fn>
    (implies (and (tac-ruleres-branch-argslist-have-lengths (1- n) y)
                  (posp n))
             (tac-ruleres-branch-argslist-have-lengths n new-y))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-argslist-have-lengths
                                      nfix))))

  (defret tac-ruleres-branch-argslist-no-assums-without-args-of-<fn>
    (tac-ruleres-branch-argslist-no-assums-without-args new-y)
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-argslist-no-assums-without-args))))

  (defret types-of-<fn>
    (implies (and (tac-ruleres-branchlist-typed x (car types) Ctx)
                  (tac-ruleres-branch-argslist-typed y (cdr types) ctx)
                  (not (member-equal nil (tac-typelist-fix types))))
             (tac-ruleres-branch-argslist-typed new-y types ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-typed
                                      tac-ruleres-branch-argslist-typed)
            :induct <call>))))

(defthm remove-entries-with-nil-of-cons-to-each
  (equal (remove-entries-with-nil (cons-to-each x y))
         (and x
              (cons-to-each x (remove-entries-with-nil y))))
  :hints(("Goal" :in-theory (enable cons-to-each remove-entries-with-nil))))

(defthm remove-entries-with-nil-of-cons-product
  (equal (remove-entries-with-nil (cons-product x y))
         (cons-product (remove nil x) (remove-entries-with-nil y)))
  :hints(("Goal" :in-theory (enable cons-product remove-entries-with-nil))))

(local (include-book "std/basic/arith-equivs" :dir :System))

(define tac-ruleres-branchlistlist-to-branch-argslist ((x tac-ruleres-branchlistlist-p))
  :returns (arglist tac-ruleres-branch-argslist-p)
  (if (atom x)
      (list (tac-ruleres-branch-args nil nil))
    (tac-ruleres-branchlist-product-with-branch-argslist
     (car x) (tac-ruleres-branchlistlist-to-branch-argslist (cdr x))))
  ///
  (defret tac-ruleres-branch-argslist-no-assums-without-args-of-<fn>
    (tac-ruleres-branch-argslist-no-assums-without-args arglist))

  (defret eval-of-<fn>
    (equal (remove-entries-with-nil
            (tac-eval-ruleres-branch-argslist arglist env))
           (remove-entries-with-nil
            (arglist-product (tac-eval-ruleres-branchlistlist x env))))
    :hints(("Goal" :in-theory (enable arglist-product
                                      TAC-EVAL-RULERES-BRANCHLISTLIST
                                      tac-eval-ruleres-branchlist
                                      tac-eval-ruleres-branch-argslist)
            :induct <call>)
           (And stable-under-simplificationp
                '(:in-theory (enable remove-entries-with-nil
                                     tac-eval-ruleres-branch-args)))))

  (defret lengths-of-<fn>-lemma
    (tac-ruleres-branch-argslist-have-lengths (len x) arglist))

  (defret lengths-of-<fn>
    (implies (equal (nfix n) (len x))
             (tac-ruleres-branch-argslist-have-lengths n arglist)))

  (defret types-of-<fn>
    (implies (and (tac-ruleres-branchlistlist-typed x types ctx)
                  (equal (len types) (len x))
                  (not (member-equal nil (tac-typelist-fix types))))
             (tac-ruleres-branch-argslist-typed arglist types ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlistlist-typed
                                      tac-ruleres-branch-argslist-typed)
            ;; :expand ((tac-ruleres-branchlistlist-typed x types ctx))
            :induct (tac-ruleres-branchlistlist-typed x types ctx)
            :expand (<call>))
           (and stable-under-simplificationp
                '(:in-theory (enable tac-ruleres-branch-args-typed
                                     tac-termlist-types acl2::prefixp)))))

  (defret vars-of-<fn>
    (implies (not (member v (tac-ruleres-branchlistlist-vars x)))
             (not (member v (tac-ruleres-branch-argslist-vars arglist))))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlistlist-vars
                                      tac-ruleres-branch-argslist-vars
                                      tac-ruleres-branch-args-vars)))))

(defthm lengths-of-tac-eval-ruleres-branch-argslist-when-have-lengths
  (equal (lists-have-lengths n (tac-eval-ruleres-branch-argslist x env))
         (tac-ruleres-branch-argslist-have-lengths n x))
  :hints(("Goal" :in-theory (enable tac-eval-ruleres-branch-argslist
                                    tac-ruleres-branch-argslist-have-lengths
                                    lists-have-lengths
                                    tac-eval-ruleres-branch-args))))

(define apply-fn-to-result-branches ((fn pseudo-fnsym-p)
                                     (results tac-ruleres-branch-argslist-p))
  :returns (apps tac-ruleres-branchlist-p)
  (if (atom results)
      nil
    (cons (b* (((tac-ruleres-branch-args x) (car results)))
            (tac-ruleres-branch x.assums
                                             (pseudo-term-fncall fn x.ctx-result-args)))
          (apply-fn-to-result-branches fn (cdr results))))
  ///
  (defthm len-args-when-tac-context-fn-p
    (implies (tac-context-fn-p fn)
             (< 0 (len (tac-function-argument-types fn))))
    :hints(("Goal" :in-theory (enable tac-context-fn-p)))
    :rule-classes (:linear :type-prescription))
  
  (defret eval-of-<fn>
    (implies (and (tac-context-fn-p fn)
                  (tac-ruleres-branch-argslist-have-lengths
                   (len (tac-function-argument-types fn)) results))
             (equal (tac-eval-ruleres-branchlist apps env)
                    (tac-ev-apply-to-arglists fn (tac-eval-ruleres-branch-argslist results env))))
    :hints(("Goal" :in-theory (enable tac-ev-apply-to-arglists
                                      tac-ruleres-branch-argslist-have-lengths
                                      tac-ruleres-branch-argslist-no-assums-without-args
                                      tac-ev-cube
                                      tac-eval-ruleres-branch
                                      tac-eval-ruleres-branch-args
                                      tac-eval-ruleres-branch-argslist
                                      tac-eval-ruleres-branchlist)
            :expand ((:free (args) (tac-ev (cons (pseudo-fnsym-fix fn) args) env))))))
  
  (defret types-of-apply-fn-to-result-branches
    (implies (and (equal rettype (tac-function-return-type fn))
                  rettype
                  (tac-ruleres-branch-argslist-typed
                   results (tac-function-argument-types fn) ctx))
             (tac-ruleres-branchlist-typed apps rettype ctx))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-typed
                                      tac-ruleres-branch-typed
                                      TAC-RULERES-BRANCH-ARGS-TYPED
                                      TAC-RULERES-BRANCH-ARGSLIST-TYPED)
            :induct <call>)
           (And stable-under-simplificationp
                '(:expand ((:free (args) (tac-term-type (pseudo-term-fncall fn args) ctx)))))))

  (defret vars-of-<fn>
    (implies (not (member v (tac-ruleres-branch-argslist-vars results)))
             (not (member v (tac-ruleres-branchlist-vars apps))))
    :hints(("Goal" :in-theory (enable tac-ruleres-branch-argslist-vars
                                      tac-ruleres-branch-args-vars
                                      tac-ruleres-branchlist-vars
                                      tac-ruleres-branch-vars
                                      cmr::term-vars)))))

(define tac-try-basic-rewrites ((rules tac-rewritelist-p)
                                (fn pseudo-fnsym-p)
                                (args pseudo-term-listp))
  :returns (mv rewrittenp (result pseudo-termp))
  (if (atom rules)
      (mv nil nil)
    (b* (((unless (mbt (consp (car rules))))
          (tac-try-basic-rewrites (cdr rules) fn args))
         ((mv ok rhs subst) (tac-rewrite-apply-rule (cdar rules) fn args))
         ((when ok) (mv t (cmr::term-subst-strict rhs subst))))
      (tac-try-basic-rewrites (cdr rules) fn args)))
  ///
  (defret <fn>-preserves-vars
    (implies (not (member v (cmr::termlist-vars args)))
             (not (member v (cmr::term-vars result)))))
  
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

  (local (in-theory (disable tac-term-type-of-term-subst-strict)))
  
  (defret <fn>-preserves-type
    (implies (and rewrittenp
                  (tac-rewrites-rhs-preserved rules)
                  (equal type (tac-term-type (pseudo-term-fncall fn args) ctx))
                  type)
             (equal (tac-term-type result ctx) type))
    :hints(("Goal" :in-theory (enable tac-rewrites-rhs-preserved))))

  (local (in-theory (enable tac-rewritelist-fix))))




(fty::deflist pseudo-term-substlist :elt-type cmr::pseudo-term-subst :true-listp t)

(include-book "std/alists/alist-equiv" :dir :system)

(local (defthm assoc-equal-is-hons-assoc-equal
         (implies k
                  (equal (assoc-equal k x)
                         (hons-assoc-equal k x)))))

(defsection tac-ev-when-preserves-vars
  
  

  (local (defthm member-alist-keys
           (iff (member-equal v (acl2::alist-keys x))
                (hons-assoc-equal v x))
           :hints(("Goal" :in-theory (enable acl2::alist-keys)))))
  
  (cmr::defthm-term-vars-flag
    (defthm tac-ev-when-sub-alistp
      (implies (and (acl2::sub-alistp sub super)
                    (subsetp-equal (cmr::term-vars x)
                                   (acl2::alist-keys sub)))
               (equal (tac-ev x super)
                      (tac-ev x sub)))
      :hints ('(:expand ((cmr::term-vars x))
                :in-theory (enable tac-ev-of-fncall-args
                                   tac-ev-when-pseudo-term-call
                                   acl2::sub-alistp-hons-assoc-equal)))
      :flag cmr::term-vars)

    (defthm tac-ev-lst-when-sub-alistp
      (implies (and (acl2::sub-alistp sub super)
                    (subsetp-equal (cmr::termlist-vars x)
                                   (acl2::alist-keys sub)))
               (equal (tac-ev-lst x super)
                      (tac-ev-lst x sub)))
      :hints ('(:expand ((cmr::termlist-vars x))))
      :flag cmr::termlist-vars))

  (cmr::defthm-term-vars-flag
    (defthm term-subst-strict-when-sub-alistp
      (implies (and (acl2::sub-alistp (cmr::pseudo-term-subst-fix sub)
                                      (cmr::pseudo-term-subst-fix super))
                    (subsetp-equal (cmr::term-vars x)
                                   (acl2::alist-keys
                                    (cmr::pseudo-term-subst-fix sub))))
               (equal (cmr::term-subst-strict x super)
                      (cmr::term-subst-strict x sub)))
      :hints ('(:expand ((cmr::term-vars x)
                         (:free (s) (cmr::term-subst-strict x s)))
                :in-theory (enable acl2::sub-alistp-hons-assoc-equal)))
      :flag cmr::term-vars)

    (defthm termlist-subst-strict-when-sub-alistp
      (implies (and (acl2::sub-alistp (cmr::pseudo-term-subst-fix sub)
                                      (cmr::pseudo-term-subst-fix super))
                    (subsetp-equal (cmr::termlist-vars x)
                                   (acl2::alist-keys
                                    (cmr::pseudo-term-subst-fix sub))))
               (equal (cmr::termlist-subst-strict x super)
                      (cmr::termlist-subst-strict x sub)))
      :hints ('(:expand ((cmr::termlist-vars x)
                         (:free (s) (cmr::termlist-subst-strict x s)))))
      :flag cmr::termlist-vars))

  (local (defthm lookup-under-iff-when-sub-alistp
           (implies (and (acl2::sub-alistp (cmr::pseudo-term-subst-fix sub)
                                           (cmr::pseudo-term-subst-fix super))
                         (hons-assoc-equal var sub)
                         (pseudo-var-p var))
                    (hons-assoc-equal var super))
           :hints (("goal" :use ((:instance acl2::sub-alistp-hons-assoc-equal
                                  (x var) (a (cmr::pseudo-term-subst-fix sub))
                                  (b (cmr::pseudo-term-subst-fix super))))))))
  
  (local (defthm cdr-lookup-under-pseudo-term-equiv-when-sub-alistp
           (implies (and (acl2::sub-alistp (cmr::pseudo-term-subst-fix sub)
                                           (cmr::pseudo-term-subst-fix super))
                         (hons-assoc-equal var sub)
                         (pseudo-var-p var))
                    (pseudo-term-equiv (cdr (hons-assoc-equal var super))
                                       (cdr (hons-assoc-equal var sub))))
           :hints (("goal" :use ((:instance acl2::sub-alistp-hons-assoc-equal
                                  (x var) (a (cmr::pseudo-term-subst-fix sub))
                                  (b (cmr::pseudo-term-subst-fix super))))))))

  (defthm sub-alistp-of-tac-ev-alist
    (implies (acl2::sub-alistp (cmr::pseudo-term-subst-fix sub)
                               (cmr::pseudo-term-subst-fix super))
             (acl2::sub-alistp (tac-ev-alist sub a) (tac-ev-alist super a)))
    :hints(("goal" :in-theory (enable acl2::sub-alistp-iff-witness
                                      acl2::sub-alistp-hons-assoc-equal)
            :restrict ((acl2::sub-alistp-iff-witness
                        ((acl2::a (tac-ev-alist sub a))))))))

  (defthm sub-alistp-of-tac-ev-alist-no-fix
    (implies (and (acl2::sub-alistp (cmr::pseudo-term-subst-fix sub) super)
                  (cmr::pseudo-term-subst-p super))
             (acl2::sub-alistp (tac-ev-alist sub a) (tac-ev-alist super a)))
    :hints(("goal" :use ((:instance sub-alistp-of-tac-ev-alist))
            :in-theory (disable sub-alistp-of-tac-ev-alist))))

  (in-theory (disable tac-ev-when-sub-alistp
                      tac-ev-lst-when-sub-alistp)))


(define tac-rewrite-pred-find-subst ((assums pseudo-term-listp)
                                     (hyp pseudo-termp)
                                     (unify-subst cmr::pseudo-term-subst-p)
                                     (used-unify-substs pseudo-term-substlist-p))
  ;; The hyp has some free variables and also potentially some variables bound
  ;; in unify-subst.  Find an assumption that unifies with hyp with the
  ;; starting unify-subst, and that isn't already used in used-unify-substs.
  :returns (new-subst cmr::pseudo-term-subst-p)
  (b* (((When (atom assums)) nil)
       ((mv ok subst) (cmr::term-unify-strict hyp (car assums) unify-subst))
       ((when (and ok
                   (not (member-equal subst (pseudo-term-substlist-fix used-unify-substs)))))
        subst))
    (tac-rewrite-pred-find-subst (cdr assums) hyp unify-subst used-unify-substs))
  ///
  (defret <fn>-preserves-bound-vars
    (implies (and new-subst
                  (hons-assoc-equal var unify-subst)
                  (pseudo-var-p var))
             (and (equal (hons-assoc-equal var new-subst)
                         (hons-assoc-equal var (cmr::pseudo-term-subst-fix unify-subst)))
                  (hons-assoc-equal var new-subst))))

  (defret sub-alistp-of-<fn>
    (implies new-subst
             (acl2::sub-alistp (cmr::pseudo-term-subst-fix unify-subst) new-subst))
    :hints(("Goal" :in-theory (enable acl2::sub-alistp-iff-witness))))

  (defret <fn>-correct
    (implies new-subst
             (member-equal (cmr::term-subst-strict hyp new-subst)
                           (pseudo-term-list-fix assums))))

  (local (defthm equal-of-pseudo-term-fix
           (implies (equal x (pseudo-term-fix y))
                    (acl2::pseudo-term-equiv x y))
           :rule-classes :forward-chaining))
  
  (local (defthm tac-term-type-of-tac-subst-ctx
           (equal (Tac-term-type x (tac-subst-ctx subst ctx))
                  (tac-term-type (cmr::term-subst-strict x subst) ctx))))
  (local (in-theory (disable tac-term-type-of-term-subst-strict)))
  
  (defret <fn>-type
    (implies (and new-subst
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred)))
             (equal (tac-term-type hyp (tac-subst-ctx new-subst ctx)) :pred))
    :hints(("Goal" :induct t
            :expand ((tac-termlist-types assums ctx)))))

  (defret <fn>-type-subst
    (implies (and new-subst
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred)))
             (equal (tac-term-type (cmr::term-subst-strict hyp new-subst) ctx) :pred))
    :hints (("goal" :use <fn>-type
             :in-theory (disable <fn> <fn>-type))))

  (defret tac-ev-of-tac-rewrite-pred-find-subst
    (implies (and (subsetp-equal (cmr::term-vars x)
                                 (acl2::alist-keys (cmr::pseudo-term-subst-fix unify-subst)))
                  new-subst)
             (equal (tac-ev x (tac-ev-alist new-subst env))
                    (tac-ev x (tac-ev-alist unify-subst env))))
    :hints(("Goal" :in-theory (e/d ()
                                   (<fn>))
            :use ((:instance tac-ev-when-sub-alistp
                   (x x)
                   (sub (tac-ev-alist unify-subst env))
                   (super (tac-ev-alist
                           (tac-rewrite-pred-find-subst
                            assums hyp unify-subst used-unify-substs)
                           env)))))))

  (defret tac-ev-lst-of-tac-rewrite-pred-find-subst
    (implies (and (subsetp-equal (cmr::termlist-vars x)
                                 (acl2::alist-keys (cmr::pseudo-term-subst-fix unify-subst)))
                  new-subst)
             (equal (tac-ev-lst x (tac-ev-alist new-subst env))
                    (tac-ev-lst x (tac-ev-alist unify-subst env))))
    :hints(("Goal" :in-theory (e/d ()
                                   (<fn>))
            :use ((:instance tac-ev-lst-when-sub-alistp
                   (x x)
                   (sub (tac-ev-alist unify-subst env))
                   (super (tac-ev-alist
                           (tac-rewrite-pred-find-subst
                            assums hyp unify-subst used-unify-substs)
                           env)))))))

  (defret termlist-subst-strict-of-tac-rewrite-pred-find-subst
    (implies (and (subsetp-equal (cmr::termlist-vars x)
                                 (acl2::alist-keys (cmr::pseudo-term-subst-fix unify-subst)))
                  new-subst)
             (equal (cmr::termlist-subst-strict x new-subst)
                    (cmr::termlist-subst-strict x unify-subst)))
    :hints(("Goal" :in-theory (e/d ()
                                   (<fn>))
            :use ((:instance termlist-subst-strict-when-sub-alistp
                   (x x)
                   (sub unify-subst)
                   (super (tac-rewrite-pred-find-subst
                           assums hyp unify-subst used-unify-substs)))))))
  

  (defret vars-of-<fn>
    (implies (and (not (member v (cmr::term-subst-vars unify-subst)))
                  (not (member v (cmr::termlist-vars assums))))
             (not (member v (cmr::term-subst-vars new-subst))))
    :hints (("goal" :induct <call>
             :expand ((cmr::termlist-vars assums)))))

  (defret tac-w-not-present-of-<fn>
    (implies (and (not (member 'tac-w (cmr::term-subst-vars
                                       (acl2::hons-remove-assoc 'w unify-subst))))
                  (not (member 'tac-w (cmr::termlist-vars assums)))
                  (not (member 'w (cmr::term-vars hyp))))
             (not (member 'tac-w (cmr::term-subst-vars
                                  (acl2::hons-remove-assoc 'w new-subst)))))
    :hints (("goal" :induct <call>
             :expand ((cmr::termlist-vars assums))))))



(define tac-rewrite-pred-subst ((rule cmr::rewrite-p)
                                (fn pseudo-fnsym-p)
                                (args pseudo-term-listp)
                                (assums pseudo-term-listp)
                                (used-unify-substs pseudo-term-substlist-p))
  :returns (mv ok (subst cmr::pseudo-term-subst-p))
  (b* (((cmr::rewrite rule))
       ((unless (pseudo-term-case rule.lhs
                  :fncall (eq rule.lhs.fn (pseudo-fnsym-fix fn))
                  :otherwise nil))
        (mv nil nil))
       ((mv ok subst1) (cmr::termlist-unify-strict (pseudo-term-call->args rule.lhs)
                                                   args nil))
       ((unless ok) (mv nil nil))
       ((unless (is-special-instantiation-rule rule))
        (mv t subst1))
       (hyp (special-instantiation-rule-binding-hyp rule))
       (new-subst (tac-rewrite-pred-find-subst assums hyp subst1 used-unify-substs))
       ((unless new-subst)
        (mv nil nil)))
    (mv t new-subst))
  ///
  (defret <fn>-lhs-subst
    (implies ok
             (equal (cmr::term-subst-strict
                     (cmr::rewrite->lhs rule) subst)
                    (pseudo-term-fncall fn args)))
    :hints (("goal" :expand ((:free (subst)
                              (cmr::term-subst-strict (cmr::rewrite->lhs rule) subst))))))

  (defret <fn>-lhs-eval
    (implies ok
             (equal (tac-ev (cmr::rewrite->lhs rule)
                            (tac-ev-alist subst env))
                    (tac-ev (pseudo-term-fncall fn args) env)))
    :hints (("goal" :use ((:instance tac-ev-of-term-subst-strict
                           (a (mv-nth 1 (tac-rewrite-pred-subst rule fn args assums used-unify-substs)))
                           (x (cmr::rewrite->lhs rule))))
             :in-theory (disable tac-ev-of-term-subst-strict
                                 <fn>))))

  (defret <fn>-hyp-member
    (implies (and (is-special-instantiation-rule rule)
                  ok)
             (member-equal (cmr::term-subst-strict
                            (special-instantiation-rule-binding-hyp rule) subst)
                           (pseudo-term-list-fix assums))))

  (local (defthm tac-ev-when-member-cube
           (implies (and (tac-ev-cube assums env)
                         (member-equal hyp (pseudo-term-list-fix assums)))
                    (tac-ev hyp env))
           :hints(("Goal" :in-theory (enable tac-ev-cube pseudo-term-list-fix)))))
  
  (defret <fn>-hyp-satisfied
    (implies (and (is-special-instantiation-rule rule)
                  (tac-ev-cube assums env)
                  ok)
             (tac-ev (special-instantiation-rule-binding-hyp rule)
                     (tac-ev-alist subst env)))
    :hints (("goal" :use ((:instance tac-ev-of-term-subst-strict
                           (a (mv-nth 1 (tac-rewrite-pred-subst rule fn args assums used-unify-substs)))
                           (x (special-instantiation-rule-binding-hyp rule))))
             :in-theory (disable tac-ev-of-term-subst-strict
                                 <fn>))))

  (local (defthm tac-term-type-of-term-subst-strict-inverse
           (equal (tac-term-type x (tac-subst-ctx y z))
                  (tac-term-type (cmr::term-subst-strict x y) z))))
  (local (in-theory (disable tac-term-type-of-term-subst-strict)))

  (local (defthm tac-term-type-when-member-and-subsetp-singleton
           (implies (and (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                         (member-equal hyp (pseudo-term-list-fix assums)))
                    (equal (tac-term-type hyp ctx) :pred))
           :hints(("Goal" 
                   :induct (len assums)
                   :expand ((pseudo-term-list-fix assums)
                            (tac-termlist-types assums ctx))))))
  
  (defret <fn>-typed
    (implies (and ok
                  (equal (tac-termlist-types args ctx)
                         (tac-function-argument-types fn)))
             (and (equal (tac-term-type (cmr::rewrite->lhs rule)
                                        (tac-subst-ctx subst ctx))
                         (tac-function-return-type fn))
                  (implies (and (is-special-instantiation-rule rule)
                                (subsetp-equal (tac-termlist-types assums ctx) '(:pred)))
                           (equal (tac-term-type (special-instantiation-rule-binding-hyp rule)
                                                 (tac-subst-ctx subst ctx))
                                  :pred))))
    :hints(("Goal" :in-theory (e/d ()
                                   (<fn>))
            :expand ((tac-term-type (pseudo-term-fncall fn args) ctx)))))

  (defret <fn>-implies-is-pred-in-set
    :pre-bind ((fn 'pred-in-set))
    (implies ok
             (is-pred-in-set (cmr::rewrite->lhs rule)))
    :hints(("Goal" :in-theory (enable is-pred-in-set)))
    :rule-classes :forward-chaining)

  (defret <fn>-binds-w-when-tac-pred-rewrite-parse-ok
    :pre-bind ((fn 'pred-in-set))
    (implies (And (tac-pred-rewrite-parse-ok rule)
                  ok)
             (hons-assoc-equal 'w subst))
    :hints(("Goal" :in-theory (enable tac-pred-rewrite-parse-ok
                                      is-pred-in-set
                                      is-pred-in-set-w)
            :expand ((CMR::TERMLIST-VARS (PSEUDO-TERM-CALL->ARGS (CMR::REWRITE->LHS RULE)))))))

  (defret <fn>-lookup-of-w-when-tac-pred-rewrite-parse-ok
    :pre-bind ((fn 'pred-in-set)
               (args (list 'tac-w x)))
    (implies (And (tac-pred-rewrite-parse-ok rule)
                  ok)
             (equal (cdr (hons-assoc-equal 'w subst))
                    'tac-w))
    :hints(("Goal" :in-theory (enable tac-pred-rewrite-parse-ok
                                      is-pred-in-set
                                      is-pred-in-set-w)
            :expand ((CMR::TERMLIST-VARS (PSEUDO-TERM-CALL->ARGS (CMR::REWRITE->LHS RULE)))
                     (:free (subst) (cmr::term-subst-strict 'w subst))
                     (:free (subst)
                      (cmr::termlist-subst-strict
                       (PSEUDO-TERM-CALL->ARGS (CMR::REWRITE->LHS RULE))
                       subst))))))
  (local (defthm hons-remove-assoc-when-not-present
           (implies (and (not (hons-assoc-equal v x))
                         (cmr::pseudo-term-subst-p x))
                    (equal (acl2::hons-remove-assoc v x) x))
           :hints(("Goal" :in-theory (enable acl2::hons-remove-assoc)))))
                    

  (defret tac-w-not-present-of-<fn>
    :pre-bind ((fn 'pred-in-set)
               (args (list 'tac-w x)))
    (implies (and (tac-pred-rewrite-parse-ok rule)
                  (not (member 'tac-w (cmr::term-vars x)))
                  (not (member 'tac-w (cmr::termlist-vars assums))))
             (not (member 'tac-w (cmr::term-subst-vars
                                  (acl2::hons-remove-assoc 'w subst)))))
    :hints (("goal" :in-theory (enable tac-pred-rewrite-parse-ok
                                       IS-PRED-IN-SET-W
                                       is-pred-in-set)
             :expand ((:free (args a b subst)
                       (cmr::termlist-unify-strict args (cons a b) subst))
                      (:free (args subst)
                       (cmr::termlist-unify-strict args nil subst))))))

  (defret vars-of-<fn>
    (implies (and (not (member v (cmr::termlist-vars args)))
                  (not (member v (cmr::termlist-vars assums))))
             (not (member v (cmr::term-subst-vars subst))))))
               
    


(defthm-tac-term-type-flag
  (defthm tac-term-type-of-cons-non-var
    (implies (not (member-equal v (cmr::term-vars x)))
             (equal (tac-term-type x (cons (cons v type) ctx))
                    (tac-term-type x ctx)))
    :hints ('(:expand ((cmr::term-vars x)
                       (:free (ctx) (tac-term-type x ctx)))))
    :flag tac-term-type)
  (defthm tac-termlist-types-of-cons-non-var
    (implies (not (member-equal v (cmr::termlist-vars x)))
             (equal (tac-termlist-types x (cons (cons v type) ctx))
                    (tac-termlist-types x ctx)))
    :hints ('(:expand ((cmr::termlist-vars x)
                       (:free (ctx) (tac-termlist-types x ctx)))))
    :flag tac-termlist-types))



(define tac-rewrite-pred-apply-rule ((rule cmr::rewrite-p)
                                     (x pseudo-termp)
                                     (assums pseudo-term-listp)
                                     (used-unify-substs pseudo-term-substlist-p))
  :returns (mv ok
               (result tac-ruleres-branchlist-p)
               (subst cmr::pseudo-term-subst-p))
  (b* (((cmr::rewrite rule))
       ((unless (and (or (eq rule.equiv 'equal)
                         (eq rule.equiv 'iff))))
        (mv nil nil nil))
       ((mv ok subst) (tac-rewrite-pred-subst rule 'pred-in-set (list 'tac-w x)
                                              assums used-unify-substs))
       ((unless ok) (mv nil nil nil))
       ((mv ok res-pattern) (tac-parse-ruleres rule.rhs))
       ((unless ok) (mv nil nil nil))
       (res (tac-subst-ruleres-branchlist res-pattern subst)))
    (mv t res subst))
  ///
  (local (in-theory (enable tac-ev-of-fncall-args)))
  
  (local (defthm hons-assoc-equal-when-cdr-hons-assoc-equal
           (implies (cdr (hons-assoc-equal k x))
                    (hons-assoc-equal k x))
           :rule-classes :forward-chaining))
  
  (defret <fn>-correct-lemma
    (implies (and ok
                  (tac-ev-theoremp* (cmr::rewrite-term rule))
                  (tac-pred-rewrite-hyps-ok rule)
                  (tac-typed-env-p env ctx)
                  (tac-ev-cube assums env)
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  ;; (equal (tac-termlist-types args ctx)
                  ;;        (tac-function-argument-types fn))
                  ;; (equal (tac-function-return-type fn) :pred)
                  (equal (tac-term-type x ctx) :set)
                  (equal (cdr (hons-assoc-equal 'tac-w ctx)) :event)
                  (tac-pred-rewrite-parse-ok rule))
             (iff (in (cdr (assoc 'tac-w env))
                      (union-list
                       (tac-eval-ruleres-branchlist result env)))
                  (in (cdr (assoc 'tac-w env))
                      (tac-ev x env))))
    :hints (("goal" :use ((:instance tac-parse-ruleres-correct
                           (x (cmr::rewrite->rhs rule))
                           (env
                            (tac-ev-alist
                             (mv-nth 1 (tac-rewrite-pred-subst rule 'pred-in-set (list 'tac-w x)
                                                               assums used-unify-substs))
                             env)))
                          (:instance tac-ev-theoremp*-implies
                           (x (cmr::rewrite-term rule))
                           (a (tac-ev-alist
                               (mv-nth 1 (tac-rewrite-pred-subst rule 'pred-in-set (list 'tac-w x)
                                                                 assums used-unify-substs))
                               env)))
                          (:instance tac-pred-rewrite-hyps-ok-necc
                           (env (tac-ev-alist
                                   (mv-nth 1 (tac-rewrite-pred-subst rule 'pred-in-set (list 'tac-w x)
                                                                     assums used-unify-substs))
                                   env))
                           (ctx (tac-subst-ctx
                                 (mv-nth 1 (tac-rewrite-pred-subst rule 'pred-in-set (list 'tac-w x)
                                                                   assums used-unify-substs))
                                 ctx)))
                          )
             :expand ((:free (a b) (tac-termlist-types (cons a b) ctx))
                      (tac-termlist-types nil ctx))
             :in-theory (enable cmr::rewrite-term))))

  (local (DEFTHM TAC-PRED-REWRITE-RHS-TYPED-NECC-force
           (IMPLIES
            (TAC-PRED-REWRITE-RHS-TYPED RULE)
            (B* (((CMR::REWRITE RULE))
                 (LHS-TYPE (TAC-TERM-TYPE RULE.LHS CTX))
                 ((MV OK RHS-PARSED)
                  (TAC-PARSE-RULERES RULE.RHS)))
              (IMPLIES
               (AND
                LHS-TYPE (IS-PRED-IN-SET RULE.LHS)
                (case-split (LET*
                             ((BINDING-HYP
                               (AND (IS-SPECIAL-INSTANTIATION-RULE RULE)
                                    (SPECIAL-INSTANTIATION-RULE-BINDING-HYP RULE))))
                             (OR (NOT BINDING-HYP)
                                 (TAC-TERM-TYPE BINDING-HYP CTX)))))
               (AND OK
                    (TAC-RULERES-BRANCHLIST-TYPED RHS-PARSED
                                                  :SET CTX)))))))
  
  (defret <fn>-type-lemma
    (implies (and ok
                  (tac-pred-rewrite-rhs-typed rule)
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  (equal (tac-term-type x ctx) :set)
                  (equal (cdr (hons-assoc-equal 'tac-w ctx)) :event))
             (tac-ruleres-branchlist-typed result :set ctx))
    :hints (("goal" 
             :expand ((:free (a b) (tac-termlist-types (cons a b) ctx))
                      (tac-termlist-types nil ctx)))))

  (local (defthm member-term-subst-vars-of-hons-remove-assoc
           (implies (not (member v (cmr::term-subst-vars x)))
                    (not (member v (cmr::term-subst-vars (acl2::hons-remove-assoc v1 x)))))
           :hints(("Goal" :in-theory (enable cmr::term-subst-vars
                                             acl2::hons-remove-assoc)))))
  
  (defret <fn>-does-not-introduce-vars
    (implies (and ok
                  (tac-pred-rewrite-parse-ok rule)
                  (not (member-equal v (cmr::term-vars x)))
                  (not (member-equal v (cmr::termlist-vars assums))))
             (not (member-equal v (tac-ruleres-branchlist-vars result))))
    :hints(("Goal" :in-theory (e/d (tac-pred-rewrite-parse-ok-implies)
                                   (;; tac-subst-ruleres-branchlist-of-remove-unused
                                    vars-of-tac-subst-ruleres-branchlist))
            :cases ((equal v 'tac-w))
            :expand ((:free (a b) (cmr::termlist-vars (cons a b))))
            :use ((:instance vars-of-tac-subst-ruleres-branchlist
                   (x (mv-nth 1 (tac-parse-ruleres (cmr::rewrite->rhs rule))))
                   (subst (acl2::hons-remove-assoc
                           'w
                           (mv-nth 1 (tac-rewrite-pred-subst
                                      rule 'pred-in-set (list 'tac-w x)
                                      assums used-unify-substs)))))))))
    
                  
  
  (defret <fn>-type
    (implies (and ok
                  (tac-pred-rewrite-rhs-typed rule)
                  (tac-pred-rewrite-parse-ok rule)
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  (equal (tac-term-type x ctx) :set)
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums))))
             (tac-ruleres-branchlist-typed result :set ctx))
    :hints (("goal" :use ((:instance <fn>-type-lemma
                           (ctx (cons (cons 'tac-w :event) ctx))))
             :in-theory (disable <fn> <fn>-type-lemma))))
                  

  
  (local (defthm tac-typed-env-p-aux-of-cons
           (implies (and (tac-typed-env-p-aux vars env ctx)
                         (or (not (pseudo-var-p v))
                             (tac-typed-val-p val type)))
                    (tac-typed-env-p-aux vars (cons (cons v val) env)
                                         (cons (cons v type) ctx)))
           :hints(("Goal" 
                   :induct (len vars)
                   :expand ((:free (env ctx)
                             (tac-typed-env-p-aux vars env ctx)))))))

  (local (defthm tac-typed-env-p-of-cons
           (implies (tac-typed-env-p env ctx)
                    (iff (tac-typed-env-p (cons (cons v val) env)
                                          (cons (cons v type) ctx))
                         (or (not (pseudo-var-p v))
                             (tac-typed-val-p val type))))
           :hints(("Goal" :in-theory (enable tac-typed-env-p
                                             acl2::alist-keys
                                             tac-typed-env-p-aux)))))

  (local (defthm non-event-in-typed-val
           (implies (and (tac-typed-val-p x :set)
                         (not (tac-typed-val-p e :event)))
                    (not (in e x)))
           :hints(("Goal" :in-theory (enable tac-typed-val-p)))))
  
  (defret <fn>-correct
    (implies (and ok
                  (tac-ev-theoremp* (cmr::rewrite-term rule))
                  (tac-pred-rewrite-hyps-ok rule)
                  (tac-typed-env-p env ctx)
                  (tac-ev-cube assums env)
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  ;; (equal (tac-termlist-types args ctx)
                  ;;        (tac-function-argument-types fn))
                  ;; (equal (tac-function-return-type fn) :pred)
                  (equal (tac-term-type x ctx) :set)
                  (tac-pred-rewrite-parse-ok rule)
                  (tac-pred-rewrite-rhs-typed rule)
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums))))
             (equal (union-list
                     (tac-eval-ruleres-branchlist result env))
                    (tac-ev x env)))
    :hints (("goal" :in-theory (e/d (set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy)
                                    (<fn> <fn>-correct-lemma)))
            (set::pick-a-point-subset-hint id clause world stable-under-simplificationp)
            (and stable-under-simplificationp
                 '(:use ((:instance <fn>-correct-lemma
                          (env (cons (cons 'tac-w set::arbitrary-element) env))
                          (ctx (cons (cons 'tac-w :event) ctx)))))))))

(fty::defmap rule-used-substs :key-type symbolp :val-type pseudo-term-substlist-p :true-listp t)

(define tac-rewrite-pred-try-rules ((rules tac-rewritelist-p)
                                    (x pseudo-termp)
                                    (assums pseudo-term-listp)
                                    (rule-used-substs rule-used-substs-p))
  :returns (mv ok
               (result tac-ruleres-branchlist-p)
               (new-rule-used-substs rule-used-substs-p)
               (rule-used-substs-updatedp))
  (b* (((when (atom rules)) (mv nil nil nil nil))
       ((unless (mbt (consp (car rules))))
        (tac-rewrite-pred-try-rules (cdr rules) x assums rule-used-substs))
       ((cons name rule) (car rules))
       (name (mbe :logic (acl2::symbol-fix name) :exec name))
       (rule-used-substs (rule-used-substs-fix rule-used-substs))
       (used-substs (cdr (hons-assoc-equal name rule-used-substs)))
       ((mv ok result subst) (tac-rewrite-pred-apply-rule rule x assums used-substs))
       ((unless ok) (tac-rewrite-pred-try-rules (cdr rules) x assums rule-used-substs)))
    (if (is-special-instantiation-rule rule)
        (mv t result (cons (cons name (cons subst used-substs)) rule-used-substs) t)
      (mv t result nil nil)))
  ///

  (defret <fn>-does-not-introduce-vars
    (implies (and ok
                  (tac-pred-rewrites-parse-ok rules)
                  (not (member-equal v (cmr::term-vars x)))
                  (not (member-equal v (cmr::termlist-vars assums))))
             (not (member-equal v (tac-ruleres-branchlist-vars result))))
    :hints(("Goal" :in-theory (enable tac-pred-rewrites-parse-ok))))
    
                  
  
  (defret <fn>-type
    (implies (and ok
                  (tac-pred-rewrites-rhs-typed rules)
                  (tac-pred-rewrites-parse-ok rules)
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  (equal (tac-term-type x ctx) :set)
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums))))
             (tac-ruleres-branchlist-typed result :set ctx))
    :hints (("goal" :in-theory (enable tac-pred-rewrites-rhs-typed
                                       tac-pred-rewrites-parse-ok))))
                  

  
  (defret <fn>-correct
    (implies (and ok
                  (tac-ev-theorem-rewritesp rules)
                  (tac-pred-rewrites-hyps-ok rules)
                  (tac-typed-env-p env ctx)
                  (tac-ev-cube assums env)
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  ;; (equal (tac-termlist-types args ctx)
                  ;;        (tac-function-argument-types fn))
                  ;; (equal (tac-function-return-type fn) :pred)
                  (equal (tac-term-type x ctx) :set)
                  (tac-pred-rewrites-parse-ok rules)
                  (tac-pred-rewrites-rhs-typed rules)
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums))))
             (equal (union-list
                     (tac-eval-ruleres-branchlist result env))
                    (tac-ev x env)))
    :hints (("goal" :in-theory (enable tac-ev-theorem-rewritesp
                                       tac-pred-rewrites-hyps-ok
                                       tac-pred-rewrites-parse-ok
                                       tac-pred-rewrites-rhs-typed))))

  (local (in-theory (enable tac-rewritelist-fix))))



(define args-to-tac-ruleres-branchlistlist ((x pseudo-term-listp))
  :returns (branch-args tac-ruleres-branchlistlist-p)
  (if (atom x)
      nil
    (cons (list (tac-ruleres-branch nil (car x)))
          (args-to-tac-ruleres-branchlistlist (cdr x))))
  ///
  (local (defun cdr2 (x y)
           (if (atom x)
               y
             (cdr2 (cdr x) (cdr y)))))
  (defret <fn>-typed
    (implies (acl2::prefixp types (tac-termlist-types x ctx))
             (tac-ruleres-branchlistlist-typed
              branch-args types ctx))
    :hints(("Goal" :in-theory (enable tac-termlist-types
                                      acl2::prefixp
                                      tac-ruleres-branchlistlist-typed
                                      tac-ruleres-branchlist-typed
                                      tac-ruleres-branch-typed)
            :induct (cdr2 x types))))

  (defret len-of-<fn>
    (equal (len branch-args) (len x)))

  (defret eval-of-<fn>
    (implies (and (tac-typed-env-p env ctx)
                  (subsetp (tac-termlist-types x ctx) '(:set :rel)))
             (equal (union-multiarglists
                     (tac-eval-ruleres-branchlistlist
                      branch-args env))
                    (tac-ev-lst x env)))
    :hints(("Goal" :in-theory (enable tac-eval-ruleres-branchlistlist
                                      tac-eval-ruleres-branchlist
                                      tac-eval-ruleres-branch
                                      union-multiarglists
                                      tac-termlist-types
                                      tac-ev-cube
                                      union-list))))

  (defret vars-of-<fn>
    (implies (not (member v (cmr::termlist-vars x)))
             (not (member v (tac-ruleres-branchlistlist-vars branch-args))))
    :hints(("Goal" :in-theory (enable tac-ruleres-branchlistlist-vars
                                      tac-ruleres-branchlist-vars
                                      tac-ruleres-branch-vars
                                      cmr::termlist-vars)))))

(deftypes used-subst-database
  (defprod term-used-subst-database
    ((rule-substs rule-used-substs-p)
     (arg-substs arg-used-subst-database))
    :layout :tree ;; so that nil is valid
    :measure (acl2::two-nats-measure (acl2-count x) 1))
  (fty::defmap arg-used-subst-database :key-type natp :val-type term-used-subst-database
    :true-listp t
    :valp-of-nil t
    :measure (acl2::two-nats-measure (acl2-count x) 0)))



(defines tac-apply-rule-in-context
  (define tac-apply-rule-in-context ((x pseudo-termp)
                                     (assums pseudo-term-listp)
                                     (ruleset tac-rewritelist-p)
                                     (subst-database term-used-subst-database-p))
    ;; Positive rules replace the term in its context, perhaps splitting into
    ;; two cases (with the same context) [e.g., union or star rules] or perhaps
    ;; adding a new assumption [e.g., intersection or product rules].  We
    ;; generalize this slightly and allow both added assumptions and a list
    ;; of contextual cases.
    :returns (mv successp
                 (results tac-ruleres-branchlist-p)
                 (new-subst-database term-used-subst-database-p)
                 (subst-database-updatedp))
    :measure (pseudo-term-count x)
    :verify-guards nil
    (b* (((unless (pseudo-term-case x :fncall))
          (mv nil nil nil nil))
         ((pseudo-term-fncall x))
         (rettype (tac-function-return-type x.fn))
         ((unless (member-eq rettype '(:set :rel)))
          (mv nil nil nil nil))
         ((mv rewrittenp result)
          (pseudo-term-case x
            :fncall
            (tac-try-basic-rewrites (tac-rewrites) x.fn x.args)
            :otherwise (mv nil nil)))
         ((when rewrittenp)
          (mv t (list (tac-ruleres-branch nil result)) nil nil))
         ((term-used-subst-database subst-database))
         ((mv rewrittenp result new-rule-substs rule-substs-updatedp)
          (if (eq rettype :set)
              ;; note: important that x not contain variable tac-w
              (tac-rewrite-pred-try-rules ruleset x assums subst-database.rule-substs)
            (mv nil nil nil nil)))
         ((when rewrittenp)
          (mv t result
              (and rule-substs-updatedp
                   (change-term-used-subst-database subst-database :rule-substs new-rule-substs))
              rule-substs-updatedp))
         ((unless (tac-context-fn-p x.fn))
          (mv nil nil nil nil))
         ((mv successp results-args new-arg-substs arg-substs-updatedp)
          (tac-apply-rule-in-context-args
           0 (tac-function-argument-types x.fn) x.args assums ruleset subst-database.arg-substs))
         ((when successp)
          (mv t (apply-fn-to-result-branches
                 x.fn
                 (tac-ruleres-branchlistlist-to-branch-argslist results-args))
              (and arg-substs-updatedp
                   (change-term-used-subst-database subst-database :arg-substs new-arg-substs))
              arg-substs-updatedp)))
      (mv nil nil nil nil)))

  (define tac-apply-rule-in-context-args ((n natp)
                                          (types tac-typelist-p)
                                          (x pseudo-term-listp)
                                          (assums pseudo-term-listp)
                                          (ruleset tac-rewritelist-p)
                                          (arg-substs arg-used-subst-database-p))
    :measure (pseudo-term-list-count x)
    :returns (mv successp
                 (results tac-ruleres-branchlistlist-p)
                 (new-arg-substs arg-used-subst-database-p)
                 (arg-substs-updatedp))
    (b* (((when (or (atom types)
                    (atom x)))
          (mv nil nil nil nil))
         (arg-substs (arg-used-subst-database-fix arg-substs))
         (term-substs (cdr (hons-assoc-equal (lnfix n) arg-substs)))
         ((mv successp results new-term-substs term-substs-updatedp)
          (tac-apply-rule-in-context (car x) assums ruleset term-substs))
         ((when successp)
          (mv t
              (cons results
                    (args-to-tac-ruleres-branchlistlist (take (1- (len types)) (cdr x))))
              (and term-substs-updatedp
                   (cons (cons (lnfix n) new-term-substs) arg-substs))
              term-substs-updatedp))
         ((mv successp results new-arg-substs arg-substs-updatedp)
          (tac-apply-rule-in-context-args (+ 1 (lnfix n)) (cdr types) (cdr x) assums ruleset arg-substs))
         ((when successp)
          (mv t (cons (list (tac-ruleres-branch nil (car x))) results)
              new-arg-substs arg-substs-updatedp)))
      (mv nil nil nil nil)))
  ///
  (verify-guards tac-apply-rule-in-context)
 
  (local (defthm tac-ruleres-branchlist-typed-of-single
           (equal (tac-ruleres-branchlist-typed
                   (list (tac-ruleres-branch nil x))
                   type ctx)
                  (or (not (tac-type-fix type))
                      (equal (tac-term-type x ctx)
                             (tac-type-fix type))))
           :hints(("Goal" :in-theory (enable tac-ruleres-branchlist-typed
                                             tac-ruleres-branch-typed)
                   :do-not-induct t))))
  
  (std::defret-mutual len-of-tac-apply-rule-in-context-args
    (defret len-of-<fn>
      (implies successp
               (equal (len results)
                      (len types)))
      :hints ('(:expand (<call>
                         (len types))))
      :fn tac-apply-rule-in-context-args)
    :skip-others t)

  (local (defthm tac-termlist-types-of-take
           (equal (tac-termlist-types (take n x) ctx)
                  (take n (tac-termlist-types x ctx)))
           :hints(("Goal" :in-theory (enable tac-termlist-types take)))))

  (local (defthm prefixp-of-take
           (implies (and (<= (len x) (nfix n))
                         (not (member-equal nil x)))
                    (iff (acl2::prefixp x (take n y))
                         (acl2::prefixp x y)))
           :hints(("Goal" :in-theory (enable acl2::prefixp take)))))

  
  (std::defret-mutual <fn>-preserves-type-lemma
    (defret <fn>-preserves-type-lemma
      (implies (and (tac-pred-rewrites-rhs-typed ruleset)
                    (tac-pred-rewrites-parse-ok ruleset)
                    (tac-term-type x ctx)
                    (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                    (not (member-equal 'tac-w (cmr::term-vars x)))
                    (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                    successp)
               (tac-ruleres-branchlist-typed results (tac-term-type x ctx) ctx))
      :hints ('(:expand (<call>
                         (cmr::term-vars x))
                :in-theory (enable tac-ruleres-branchlist-typed
                                   TAC-RULERES-BRANCH-TYPED
                                   tac-termlist-types)))
      :fn tac-apply-rule-in-context)
    (defret <fn>-preserves-type
      (implies (and (tac-pred-rewrites-rhs-typed ruleset)
                    (tac-pred-rewrites-parse-ok ruleset)
                    (tac-typelist-p types)
                    (not (member-equal nil types))
                    (acl2::prefixp types (tac-termlist-types x ctx))
                    (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                    (not (member-equal 'tac-w (cmr::termlist-vars x)))
                    (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                    successp)
               (tac-ruleres-branchlistlist-typed
                results types ctx))
      :hints ('(:expand (<call>
                         (:free (a b c) (acl2::prefixp a (cons b c)))
                         (cmr::termlist-vars x)
                         (:free (a b)
                          (tac-ruleres-branchlistlist-typed
                           (cons a b) types ctx)))
                :in-theory (enable tac-ruleres-branch-argslist-typed
                                   tac-termlist-types
                                   acl2::prefixp))
              ;; (and stable-under-simplificationp
              ;;      `(:expand (,(car (last clause))
              ;;                 (:free (a b c) (acl2::prefixp a (cons b c))))))
              )
      :fn tac-apply-rule-in-context-args))


  (defret <fn>-preserves-type
    (implies (and (tac-pred-rewrites-rhs-typed ruleset)
                  (tac-pred-rewrites-parse-ok ruleset)
                  (equal type (tac-term-type x ctx))
                  type
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  (not (member-equal 'tac-w (cmr::term-vars x)))
                  (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                  successp)
             (tac-ruleres-branchlist-typed results type ctx))
    :fn tac-apply-rule-in-context)

  (defret not-set-or-rel-type-implies-not-successp-<fn>
    (implies (and (not (equal (tac-function-return-type
                               (pseudo-term-fncall->fn x))
                              :set))
                  (not (equal (tac-function-return-type
                               (pseudo-term-fncall->fn x))
                              :rel)))
             (not successp))
    :hints(("Goal" :in-theory (enable tac-apply-rule-in-context)))
    :fn tac-apply-rule-in-context)

  (local (defthm tac-eval-ruleres-branchlist-singleton
           (implies (and (tac-typed-env-p env ctx)
                         (member-equal (tac-term-type x ctx) '(:set :rel)))
                    (equal (union-list
                            (tac-eval-ruleres-branchlist
                             (list (tac-ruleres-branch nil x))
                             env))
                           (tac-ev x env)))
           :hints(("Goal" :in-theory (enable tac-eval-ruleres-branchlist
                                             tac-eval-ruleres-branch
                                             tac-ev-cube
                                             union-list)))))

  (local (defthm take-when-prefixp
           (implies (acl2::prefixp x y)
                    (acl2::list-equiv (take (len x) y) x))
           :hints(("Goal" :in-theory (enable acl2::prefixp
                                             acl2::list-equiv)))))

  (local (defthm tac-ev-lst-of-take
           (equal (tac-ev-lst (take n x) a)
                  (take n (tac-ev-lst x a)))
           :hints(("Goal" :in-theory (enable take tac-ev-lst)))))

  (defthm tac-ev-apply-of-take-arg-types
    (implies (tac-function-return-type fn)
             (equal (tac-ev-apply fn (take (len (tac-function-argument-types fn)) args))
                    (tac-ev-apply fn args)))
    :hints(("Goal" :in-theory (enable tac-function-return-type))
           (and stable-under-simplificationp
                '(:in-theory (enable tac-ev-apply)))))
  
  (std::defret-mutual <fn>-eval-lemma
    (defret <fn>-eval-correct
      (implies (and ;; (member-equal (tac-term-type x ctx) '(:set :rel))
                    (tac-typed-env-p env ctx)
                    (tac-ev-theorem-rewritesp ruleset)
                    (tac-pred-rewrites-hyps-ok ruleset)
                    (tac-pred-rewrites-rhs-typed ruleset)
                    (tac-pred-rewrites-parse-ok ruleset)
                    (not (member-equal 'tac-w (cmr::term-vars x)))
                    (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                    (tac-term-type x ctx)
                    (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                    (tac-ev-cube assums env)
                    successp)
               (equal (union-list
                       (tac-eval-ruleres-branchlist results env))
                      (tac-ev x env)))
      :hints ('(:expand (<call>
                         (cmr::term-vars x))
                :do-not-induct t)
              (and stable-under-simplificationp
                   '(:expand ((tac-ev (cons (pseudo-term-fncall->fn x)
                                            (pseudo-term-call->args x))
                                      env)))))
      :fn tac-apply-rule-in-context)

    (defret <fn>-eval-correct
      (implies (and (tac-typed-env-p env ctx)
                    (tac-ev-theorem-rewritesp ruleset)
                    (tac-pred-rewrites-hyps-ok ruleset)
                    (tac-pred-rewrites-rhs-typed ruleset)
                    (tac-pred-rewrites-parse-ok ruleset)
                    (subsetp-equal types '(:set :rel))
                    (acl2::prefixp types (tac-termlist-types x ctx))
                    (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                    (not (member-equal 'tac-w (cmr::termlist-vars x)))
                    (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                    (tac-ev-cube assums env)
                    successp)
               (equal (union-multiarglists
                       (tac-eval-ruleres-branchlistlist results env))
                      (take (len types) (tac-ev-lst x env))))
      :hints ((and stable-under-simplificationp
                   '(:expand (<call>
                              (:free (a b) (union-multiarglists (cons a b)))
                              (subsetp-equal types '(:set :rel))
                              (:free (a b)
                               (tac-eval-ruleres-branchlistlist
                                (cons a b) env))
                              (cmr::termlist-vars x)
                              (tac-termlist-types x ctx)
                              (:free (a b) (acl2::prefixp types (cons a b))))
                     :do-not-induct t)))
      :fn tac-apply-rule-in-context-args))

  (local (defthm termlist-vars-of-take
           (implies (not (member-equal v (cmr::termlist-vars x)))
                    (not (member-equal v (cmr::termlist-vars (take n x)))))
           :hints(("Goal" :in-theory (enable cmr::termlist-vars)))))

  (std::defret-mutual <fn>-preserves-vars
    (defret <fn>-preserves-vars
      (implies (and successp
                    (tac-pred-rewrites-parse-ok ruleset)
                    (not (member-equal v (cmr::term-vars x)))
                    (not (member-equal v (cmr::termlist-vars assums))))
               (not (member-equal v (tac-ruleres-branchlist-vars results))))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:expand ((cmr::term-vars x)
                              (:free (a b) (tac-ruleres-branchlist-vars (cons a b)))
                              (:free (a b) (tac-ruleres-branch-vars (tac-ruleres-branch a b)))))))
      :fn tac-apply-rule-in-context)
    (defret <fn>-preserves-vars
      (implies (and successp
                    (tac-pred-rewrites-parse-ok ruleset)
                    (not (member-equal v (cmr::termlist-vars x)))
                    (not (member-equal v (cmr::termlist-vars assums))))
               (not (member-equal v (tac-ruleres-branchlistlist-vars results))))
      :hints ('(:expand (<call>
                         (cmr::termlist-vars x)
                         (:free (a b) (tac-ruleres-branchlistlist-vars (cons a b)))
                         (:free (a b) (tac-ruleres-branchlist-vars (cons a b)))
                         (:free (a b) (tac-ruleres-branch-vars (tac-ruleres-branch a b))))))
      :fn tac-apply-rule-in-context-args)))



