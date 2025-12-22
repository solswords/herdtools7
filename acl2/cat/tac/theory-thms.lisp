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

;; (in-theory (enable set::union-with-subset-left
;;                    set::union-with-subset-right
;;                    set::intersect-with-subset-left
;;                    set::intersect-with-subset-right))

(defthmd in-universe-when-in-event-set
  (implies (and (in e x)
                (event-set-p x))
           (in e (universe)))
  :hints(("goal" :use ((:instance event-set-p-implies-not-in-when-not-event))
          :in-theory (enable event-p))))

(defthm subset-of-universe-when-event-set-p
  (implies (event-set-p s)
           (subset s (universe)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    in-universe-when-in-event-set))))

(defthm setimage-of-nil
  (equal (setimage nil x)
         nil)
  :hints(("Goal" :in-theory (enable setimage))))

;; (local (defthm in-of-event-set-fix-forward
;;          (implies (in e (event-set-fix x))
;;                   (event-p e))
;;          :hints(("Goal" :in-theory (enable event-set-p-implies-not-in-when-not-event)))
;;          :rule-classes :forward-chaining))

(defthm setimage-of-id-relation
  (equal (setimage x (relidentity y))
         (setintersect x y))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-setimage-rw
                                    in-of-setimage-suff3
                                    ;; in-of-relation-fix
                                    in-of-event-set-fix)))
  :otf-flg t)

(defthm in-setimage-of-singleton
  (iff (in x (setimage (singleton y) z))
       (and (event-p x)
            (in (edge y x) (relation-fix z))))
  :hints(("Goal" :in-theory (enable in-of-setimage-rw
                                    in-of-setimage-suff
                                    in-of-event-set-fix))))

(defthm in-universe-when-event-p
  (implies (event-p x)
           (in x (universe)))
  :hints(("Goal" :in-theory (enable event-p))))

(defthm setimage-of-singleton-in-universe
  (implies (event-p e)
           (equal (setimage (singleton e) (relprod (universe) (universe)))
                  (universe)))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-setimage-rw
                                    in-of-setimage-suff
                                    in-of-relprod))
         (set::pick-a-point-subset-hint id clause world stable-under-simplificationp)
         (and stable-under-simplificationp
              '(:use ((:instance in-of-setimage-suff
                       (s (insert e nil))
                       (r (relprod (universe) (universe)))
                       (w e)
                       (v set::arbitrary-element)))
                :in-theory (enable event-p)))))

(defthm setimage-of-setunion
  (equal (setimage (setunion x y) z)
         (setunion (setimage x z) (setimage y z)))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-setimage-rw
                                    in-of-setimage-suff)))
  :otf-flg t)

(defthm setimage-of-relcompose
  (equal (setimage x (relcompose y z))
         (setimage (setimage x y) z))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-setimage-rw
                                     in-of-relcompose-rw
                                     in-of-relcompose-suff))
          (set::pick-a-point-subset-hint id clause world stable-under-simplificationp)
          (and stable-under-simplificationp
               '(:use ((:instance in-of-setimage-suff
                        (v set::arbitrary-element)
                        (s x) (r (relcompose y z))
                        (w (setimage-witness (setimage-witness
                                           set::arbitrary-element
                                           (setimage x y) z)
                                          x y)))
                       (:instance in-of-relcompose-suff
                        (pair (edge (setimage-witness (setimage-witness
                                                    set::arbitrary-element
                                                    (setimage x y) z)
                                                   x y)
                                    set::arbitrary-element))
                        (x y) (y z)
                        (mid (setimage-witness set::arbitrary-element (setimage x y) z))))))))

(defthm setimage-of-relinverse
  (equal (setimage x (relinverse y))
         (setpreimage y x))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-setimage-rw
                                     in-of-setpreimage-rw
                                     in-of-setimage-suff
                                     in-of-setpreimage-suff
                                     in-of-relinverse))))


(defthm setimage-of-singleton-intersect
  (equal (setimage (singleton e) (relintersect x y))
         (setintersect (setimage (singleton e) x)
                       (setimage (singleton e) y)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-setimage-rw))))

(defthm setpreimage-of-nil
  (equal (setpreimage x nil)
         nil)
  :hints(("Goal" :in-theory (enable setpreimage))))

(defthm setpreimage-of-relidentity
  (equal (setpreimage (relidentity s1) s2)
         (setintersect s1 s2))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-setpreimage-rw
                                    in-of-setpreimage-suff
                                    in-of-event-set-fix)))
  :otf-flg t)


(defthm setpreimage-of-singleton-in-universe
  (implies (event-p e)
           (equal (setpreimage (relprod (universe) (universe)) (singleton e))
                  (universe)))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-setimage-rw
                                    in-of-setpreimage-suff
                                    in-of-relprod))
         (set::pick-a-point-subset-hint id clause world stable-under-simplificationp)
         (and stable-under-simplificationp
              '(:use ((:instance in-of-setpreimage-suff
                       (s (singleton e))
                       (r (relprod (universe) (universe)))
                       (w e)
                       (v set::arbitrary-element)))))
         (and stable-under-simplificationp
              '(:in-theory (enable in-universe-when-in-event-set
                                   event-p)))))

(defthm setpreimage-of-setunion
  (equal (setpreimage z (setunion x y))
         (setunion (setpreimage z x) (setpreimage z y)))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-setpreimage-rw
                                    in-of-setpreimage-suff)))
  :otf-flg t)

(defthm setpreimage-of-relcompose
  (equal (setpreimage (relcompose z y) x)
         (setpreimage z (setpreimage y x)))
  :hints (("goal"
           :in-theory (e/d (set::double-containment-no-backchain-limit
                            pick-a-point-subset-strategy)))
          (set::pick-a-point-subset-hint id clause world stable-under-simplificationp)
          (and stable-under-simplificationp
               (acl2::use-termhint
                (b* ((set1 (setpreimage (relcompose z y) x))
                     ;; (set2 (setpreimage z (setpreimage y x)))
                     (e set::arbitrary-element)
                     ((when (in e set1))
                      (b* ((w1 (setpreimage-witness e (relcompose z y) x))
                           (w2 (relcompose-midpoint e w1 z y)))
                        `(:use ((:instance in-of-setpreimage-suff
                                 (v ,(acl2::hq e))
                                 (r z) (s (setpreimage y x))
                                 (w ,(acl2::hq w2)))
                                (:instance in-of-setpreimage-suff
                                 (v ,(acl2::hq w2))
                                 (r y) (s x)
                                 (w ,(acl2::hq w1)))))))
                     (w1 (setpreimage-witness e z (setpreimage y x)))
                     (w2 (setpreimage-witness w1 y x)))
                  `(:use ((:instance in-of-setpreimage-suff
                           (v ,(acl2::hq e))
                           (r (relcompose z y))
                           (s x) (w ,(acl2::hq w2)))
                          (:instance in-of-relcompose-suff
                           (pair (edge ,(acl2::hq e) ,(acl2::hq w2)))
                           (mid ,(acl2::hq w1))
                           (x z) (y y)))))
                :immediate-hints
                ('(:in-theory (e/d (set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-setpreimage-rw
                                    in-of-relcompose-rw
                                    ;; in-of-relcompose-suff
                                    in-of-event-set-fix
                                    in-of-relation-fix)
                                   (in-of-setpreimage-suff
                                    in-of-setpreimage-suff2
                                    in-of-setpreimage-suff3
                                    in-of-relcompose-suff))))))))

(defthm setpreimage-of-relinverse
  (equal (setpreimage (relinverse y) x)
         (setimage x y))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-setimage-rw
                                     in-of-setpreimage-rw
                                     in-of-setimage-suff
                                     in-of-setpreimage-suff
                                     in-of-relinverse))))

(defthm in-setpreimage-of-singleton
  (iff (in x (setpreimage z (singleton y)))
       (and (event-p x)
            (in (edge x y) (relation-fix z))))
  :hints(("Goal" :in-theory (enable in-of-setpreimage-rw
                                    in-of-setpreimage-suff3))))

(defthm setpreimage-of-singleton-intersect
  (equal (setpreimage (relintersect x y) (singleton e))
         (setintersect (setpreimage x (singleton e))
                       (setpreimage y (singleton e))))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-setpreimage-rw))))



(defthm relidentity-of-union
  (equal (relidentity (setunion x y))
         (relunion (relidentity x) (relidentity y)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-relidentity))))

(defthm relidentity-of-intersect
  (equal (relidentity (setintersect x y))
         (relintersect (relidentity x) (relidentity y)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-relidentity))))



(defthm relinverse-of-union
  (equal (relinverse (relunion x y))
         (relunion (relinverse x) (relinverse y)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-relinverse))))

(defthm relinverse-of-intersect
  (equal (relinverse (relintersect x y))
         (relintersect (relinverse x) (relinverse y)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-relinverse))))


(defthm relcompose-singleton-prod-1
  (equal (relcompose x (relprod (singleton y) z))
         (relprod (setpreimage x (singleton y)) z))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-relprod
                                    in-of-relcompose-rw
                                    in-of-relcompose-suff
                                    in-of-setpreimage-rw
                                    in-of-setpreimage-suff3
                                    in-of-event-set-fix)))
  :otf-flg t)

(defthm relcompose-singleton-prod-2
  (equal (relcompose (relprod z (singleton y)) x)
         (relprod z (setimage (singleton y) x)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-relprod
                                    in-of-relcompose-rw
                                    in-of-relcompose-suff2
                                    in-of-setimage-rw
                                    in-of-setimage-suff3
                                    in-of-event-set-fix)))
  :otf-flg t)

(defthm relcompose-singleton-prod-3
  (equal (relcompose x (relprod z (singleton y)))
         (relprod (setpreimage x z) (singleton y)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-relprod
                                    in-of-relcompose-rw
                                    in-of-relcompose-suff
                                    in-of-relcompose-suff2
                                    in-of-setpreimage-rw
                                    in-of-setpreimage-suff3
                                    in-of-event-set-fix
                                    ))))

(defthm relcompose-singleton-prod-4
  (equal (relcompose (relprod (singleton y) z) x)
         (relprod (singleton y) (setimage z x)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-relprod
                                    in-of-relcompose-rw
                                    in-of-relcompose-suff
                                    in-of-relcompose-suff2
                                    in-of-setimage-rw
                                    in-of-setimage-suff3
                                    in-of-event-set-fix
                                    ))))


(defthm subset-of-universe-rel
  (implies (relation-p x)
           (subset x (relprod (universe) (universe))))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    in-of-relprod
                                    relation-p-implies-not-in-when-not-edge)))
  :otf-flg t)


(defthm relcompose-of-nil
  (equal (relcompose nil x) nil)
  :hints(("Goal" :in-theory (enable relcompose))))

(defthm relcompose-of-nil2
  (equal (relcompose x nil) nil)
  :hints(("Goal" :in-theory (enable relcompose compose1))))

(defthm relation-path-p-of-relidentity
  (implies (not (event-equiv (car path)
                             (car (last path))))
           (not (relation-path-p path (relidentity x))))
  :hints(("Goal" :in-theory (enable relation-path-p))))


(local (defthm relation-path-p-implies-last-in-set
         (implies (not (in (event-fix (car (last path))) (event-set-fix x)))
                  (not (relation-path-p path (relidentity x))))
         :hints(("Goal" :in-theory (enable relation-path-p)))))

(defthm exists-path-of-relidentity
  (iff (exists-path src dst (relidentity x))
       (and (event-equiv src dst)
            (in (event-fix src) (event-set-fix x))))
  :hints(("Goal" :in-theory (enable ;; exists-path
                             relation-path-p)
          :use ((:instance exists-path-suff
                 (path (list src dst))
                 (x (relidentity x)))))
         (and stable-under-simplificationp
              '(:in-theory (enable exists-path))))
  :otf-flg t)


;; (defthm in-edge-when-not-event-p-dst
;;   (implies (and (event-rel-p x)
;;                 (not (event-p dst)))
;;            (not (in (edge src dst) (relation-fix x))))
;;   :hints(("Goal" :in-theory (enable event-rel-p in))))

;; (defthm relation-path-p-when-not-event-p-dst
;;   (implies (and (event-rel-p x)
;;                 (not (event-p (car (last path)))))
;;            (not (relation-path-p path x)))
;;   :hints(("Goal" :in-theory (enable relation-path-p))))

;; (defthm exists-path-when-not-event-p-last
;;   (implies (and (event-rel-p x)
;;                 (not (event-p dst)))
;;            (not (exists-path src dst x)))
;;   :hints(("Goal" :in-theory (enable exists-path))))

;; (local (defthm not-event-p-when-not-in-universe
;;          (implies (not (in x (universe)))
;;                   (not (event-p x)))
;;          :hints(("Goal" :in-theory (enable event-p)))))

(defthm relstar-of-relidentity
  (equal (relstar (relidentity s))
         (relidentity (universe)))
  :hints(("Goal" :in-theory (enable relstar
                                    set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    relplus-correct))))


(defthm relplus-of-relidentity
  (equal (relplus (relidentity s))
         (relidentity s))
  :hints(("Goal" :in-theory (enable relplus
                                    set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    relplus-correct))))

(defthm exists-path-of-universe-rel
  (exists-path src dst (relprod (universe) (universe)))
  :hints (("goal" :use ((:instance exists-path-suff
                         (path (list src dst))
                         (x (relprod (universe) (universe)))))
           :in-theory (enable relation-path-p
                              in-of-relprod))))

(defthm relstar-of-universe-rel
  (equal (relstar (relprod (universe) (universe)))
         (relprod (universe) (universe)))
  :hints(("Goal" :in-theory (enable relstar
                                    set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    relplus-correct
                                    in-of-relprod))))

(defthm relplus-of-universe-rel
  (equal (relplus (relprod (universe) (universe)))
         (relprod (universe) (universe)))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    relplus-correct
                                    in-of-relprod))))

(defthm relinverse-of-relidentity
  (equal (relinverse (relidentity r))
         (relidentity r))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-relinverse))))

(defthm relinverse-of-relprod
  (equal (relinverse (relprod s1 s2))
         (relprod s2 s1))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-relinverse
                                    in-of-relprod))))


(defthm relprod-of-nil
  (equal (relprod nil r) nil)
  :hints(("Goal" :in-theory (enable relprod))))

(defthm relprod-of-nil2
  (equal (relprod r nil) nil)
  :hints(("Goal" :in-theory (enable relprod
                                    cartesian1))))


(local (defthm edge-of-dst-and-equiv-src
         (implies (event-equiv src (edge->src x) )
                  (equal (edge src (edge->dst x))
                         (edge-fix x)))))

(local (defthm edge-of-src-and-equiv-dst
         (implies (event-equiv dst (edge->dst x))
                  (equal (edge (edge->src x) dst)
                         (edge-fix x)))))

(defthm intersect-relprod-singleton-1
  (equal (relintersect x (relprod (singleton y) z))
         (relprod (singleton y) (setintersect (setimage (singleton y) x) z)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-relprod
                                    in-of-setimage-rw
                                    in-of-setimage-suff
                                    in-of-event-set-fix
                                    ))))

(defthm intersect-relprod-singleton-2
  (equal (relintersect x (relprod z (singleton y)))
         (relprod (setintersect (setpreimage x (singleton y)) z) (singleton y)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-relprod
                                    in-of-setpreimage-rw
                                    in-of-setpreimage-suff3
                                    in-of-event-set-fix
                                    ))))

(defthm intersect-relprod-singleton-3
  (equal (relintersect (relprod (singleton y) z) x)
         (relprod (singleton y) (setintersect z (setimage (singleton y) x))))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-relprod
                                    in-of-setimage-rw
                                    in-of-setimage-suff
                                    in-of-event-set-fix))))

(defthm intersect-relprod-singleton-4
  (equal (relintersect (relprod z (singleton y)) x)
         (relprod (setintersect z (setpreimage x (singleton y))) (singleton y)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-relprod
                                    in-of-setpreimage-rw
                                    in-of-setpreimage-suff
                                    in-of-event-set-fix
                                    ))))

;; (defthm union-of-subset
;;   (implies (subset x y)
;;            (equal (union y x) (sfix y)))
;;   :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
;;                                     set::subset-in
;;                                     set::double-containment-no-backchain-limit))))


(defthm setimage-of-relunion
  (equal (setimage s (relunion r1 r2))
         (setunion (setimage s r1) (setimage s r2)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-setimage-rw))))

(defthm relcompose-of-relunion
  (equal (relcompose r (relunion r1 r2))
         (relunion (relcompose r r1) (relcompose r r2)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-relcompose-rw
                                     in-of-relcompose-suff
                                     in-of-relcompose-suff2))))

(defthm relcompose-of-relunion-2
  (equal (relcompose (relunion r1 r2) r)
         (relunion (relcompose r1 r) (relcompose r2 r)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-relcompose-rw
                                     in-of-relcompose-suff
                                     in-of-relcompose-suff2))))


(defthmd in-of-relplus-split
  (iff (in pair (relplus r))
       (or (in pair (relation-fix r))
           (in pair (relcompose r (relplus r)))))
  :hints (("goal" :in-theory (enable relplus-correct
                                     in-of-relcompose-rw
                                     in-of-relation-fix))
          (acl2::use-termhint
           (cond ((in pair (relplus r))
                  (let ((path (exists-path-witness
                               (edge->src pair) (edge->dst pair) r)))
                    `(:expand ((exists-path (edge->src pair)
                                            (edge->dst pair)
                                            r)
                               (relation-path-p ,(acl2::hq path) r))
                      . ,(and (consp (cddr path))
                              `(:use ((:instance in-of-relcompose-suff
                                       (x r) (y (relplus r))
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
                 (t (b* ((mid (relcompose-midpoint (edge->src pair)
                                                (edge->dst pair)
                                                r (relplus r)))
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
                 (equal dst (event-fix (car (last path))))
                 (equal n (- (len path) 2)))
            (in (edge (nth n path) dst) (relation-fix r)))
   :hints(("Goal" :in-theory (enable relation-path-p-implies-last-edge-lemma)))))

(local
 (defthmd relation-path-p-implies-last-edge2
   (implies (and (relation-path-p path r)
                 (equal dst (event-fix (car (last path))))
                 (equal n (- (len path) 2)))
            (in (edge (nth n path) dst) r))
   :hints(("Goal" :use relation-path-p-implies-last-edge
           :in-theory (e/d (in-of-relation-fix)
                           (relation-path-p-implies-last-edge))))))

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

(local (defthm len-when-consp
         (implies (consp x)
                  (<= 1 (len x)))
         :rule-classes :type-prescription))

(defthmd relcompose-relplus-invert
  (iff (in pair (relcompose (relplus r) r))
       (in pair (relcompose r (relplus r))))
  :hints (("goal" :in-theory (disable acl2::take-of-cons
                                      car-last-of-take))
          (acl2::use-termhint
           (b* (((edge pair)))
             (cond ((in pair (relcompose (relplus r) r))
                    (b* ((mid (relcompose-midpoint pair.src pair.dst
                                                (relplus r) r))
                         (path1 (exists-path-witness
                                 pair.src mid r))
                         (path (append path1 (list pair.dst))))
                      `(:expand ((exists-path ,(acl2::hq pair.src)
                                              ,(acl2::hq mid)
                                              r)
                                 (relation-path-p ,(acl2::hq path1) r)
                                 (:free (a b) (relation-path-p (list a b) r)))
                        :use ((:instance in-of-relcompose-suff
                               (pair pair)
                               (mid ,(acl2::hq (cadr path)))
                               (x r) (y (relplus r)))
                              (:instance exists-path-suff
                               (src ,(acl2::hq (cadr path)))
                               (dst ,(acl2::hq pair.dst))
                               (path ,(acl2::hq (cdr path)))
                               (x r)))
                        :in-theory (e/d (relplus-correct
                                         in-of-relcompose-rw
                                         in-of-relation-fix)
                                        (exists-path-suff)))))
                   (t (b* ((mid (relcompose-midpoint pair.src pair.dst
                                                  r (relplus r)))
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
                        :use ((:instance in-of-relcompose-suff
                               (pair pair)
                               (mid ,(acl2::hq new-mid))
                               (x (relplus r)) (y r))
                              (:instance exists-path-suff
                               (src ,(acl2::hq pair.src))
                               (dst ,(acl2::hq new-mid))
                               (path ,(acl2::hq new-path))
                               (x r)))
                        :in-theory (e/d (relplus-correct
                                         in-of-relcompose-rw
                                         relation-path-p-implies-last-edge2
                                         in-of-relation-fix)
                                        (exists-path-suff))))))))))

(defthmd in-of-relplus-split2
  (iff (in pair (relplus r))
       (or (in pair (relation-fix r))
           (in pair (relcompose (relplus r) r))))
  :hints (("goal" :use in-of-relplus-split
           :in-theory (e/d (relcompose-relplus-invert)))))
                              

(defthmd setimage-of-relcompose-inverse
  (equal (setimage (setimage x y) z)
         (setimage x (relcompose y z))))

(defthmd setpreimage-of-relcompose-inverse
  (equal (setpreimage z (setpreimage y x))
         (setpreimage (relcompose z y) x)))


(defthm in-relcompose-id
  (iff (in pair
           (relcompose r (relidentity (universe))))
       (in pair (relation-fix r)))
  :hints (("goal" :in-theory (enable in-of-relcompose-rw
                                     in-of-relation-fix)
           :use ((:instance in-of-relcompose-suff
                  (pair pair)
                  (mid (edge->dst pair))
                  (x r) (y (relidentity (universe))))))))

(defthm in-relcompose-id2
  (iff (in pair
           (relcompose (relidentity (universe)) r))
       (in pair (relation-fix r)))
  :hints (("goal" :in-theory (enable in-of-relcompose-rw
                                     in-of-relation-fix)
           :use ((:instance in-of-relcompose-suff
                  (pair pair)
                  (mid (edge->src pair))
                  (x (relidentity (universe))) (y r))))))


(defthm emptyp-when-in
  (implies (in e x)
           (not (emptyp x))))

(defthm emptyp-rw
  (implies (acl2::rewriting-positive-literal `(emptyp ,x))
           (iff (emptyp x)
                (not (in (head x) x)))))

(in-theory (disable set::in-head
                    set::in-tail-or-head))
