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

(include-book "logic")
(local (include-book "std/util/termhints" :dir :system))

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

(defthm union-of-subset
  (implies (subset x y)
           (equal (union y x) (sfix y)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::subset-in
                                    set::double-containment-no-backchain-limit))))


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
(local (defthm car-last-of-take
         (equal (car (last (take n x)))
                (if (zp n)
                    nil
                  (nth (- n 1) x)))
         :hints(("Goal" :in-theory (enable nth take)))))

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

(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (not (consp x)))))

(local (defthm car-of-append
         (equal (car (append x y))
                (if (consp x) (car x) (car y)))))


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

(defthmd preimage-of-compose-inverse
  (equal (preimage (preimage x y) z)
         (preimage x (compose z y))))


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


(defthm emptyp-when-in
  (implies (in e x)
           (not (emptyp x))))

(defthm emptyp-rw
  (implies (acl2::rewriting-positive-literal `(emptyp ,x))
           (iff (emptyp x)
                (not (in (head x) x)))))

(in-theory (disable set::in-head
                    set::in-tail-or-head))
