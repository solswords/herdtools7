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

(in-theory (enable set::union-with-subset-left
                   set::union-with-subset-right
                   set::intersect-with-subset-left
                   set::intersect-with-subset-right))


(defthm event-set-fix-of-union
  (equal (event-set-fix (union x y))
         (union (event-set-fix x)
                (event-set-fix y)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-event-set-fix))))

(defthm relation-fix-of-union
  (equal (relation-fix (union x y))
         (union (relation-fix x)
                (relation-fix y)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-relation-fix))))

(defthm subset-of-relation-fix
  (implies (subset x y)
           (subset (relation-fix x) (relation-fix y)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::subset-in
                                    in-of-relation-fix))))

(defthm subset-of-event-set-fix
  (implies (subset x y)
           (subset (event-set-fix x) (event-set-fix y)))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::subset-in
                                    in-of-event-set-fix))))

(defthm event-set-p-of-emptyset
  (event-set-p (emptyset)))

(defthm in-of-emptyset
  (not (in e (emptyset))))

(defthm relcompose-of-union-1
  (equal (relcompose (union x y) z)
         (union (relcompose x z)
                (relcompose y z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-relcompose-rw
                                     in-of-relcompose-suff
                                     in-of-relcompose-suff2))))

(defthm relcompose-of-subset-1
  (implies (subset (relation-fix x) (relation-fix y))
           (subset (relcompose x z)
                   (relcompose y z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-relcompose-rw
                                     in-of-relcompose-suff2
                                     set::subset-in))))

(defthm relcompose-of-nil-1
  (equal (relcompose nil z) (relidentity (emptyset)))
  :hints (("goal" :in-theory (e/d (set::double-containment-no-backchain-limit
                                   pick-a-point-subset-strategy
                                   in-of-relcompose-rw)
                                  ((emptyset) emptyset)))))

(defthm relcompose-of-union-2
  (equal (relcompose z (union x y))
         (union (relcompose z x)
                (relcompose z y)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-relcompose-rw
                                     in-of-relcompose-suff
                                     in-of-relcompose-suff2))))

(defthm relcompose-of-subset-2
  (implies (subset (relation-fix x) (relation-fix y))
           (subset (relcompose z x)
                   (relcompose z y)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-relcompose-rw
                                     in-of-relcompose-suff
                                     set::subset-in))))

(defthm relcompose-of-nil-2
  (equal (relcompose x nil) (relidentity (emptyset)))
  :hints (("goal" :in-theory (e/d (set::double-containment-no-backchain-limit
                                   pick-a-point-subset-strategy
                                   in-of-relcompose-rw)
                                  ((emptyset) emptyset)))))
  

(defthm setintersect-of-union-1
  (equal (setintersect (union x y) z)
         (union (setintersect x z)
                (setintersect y z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-event-set-fix))))

(defthm setintersect-of-subset-1
  (implies (subset (event-set-fix x) (event-set-fix y))
           (subset (setintersect x z)
                   (setintersect y z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     set::subset-in))))

(defthm setintersect-of-nil-1
  (equal (setintersect nil y) (emptyset))
  :hints(("Goal" :in-theory (enable setintersect))))
           

(defthm setintersect-of-union-2
  (equal (setintersect x (union y z))
         (union (setintersect x y)
                (setintersect x z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-event-set-fix))))

(defthm setintersect-of-subset-2
  (implies (subset (event-set-fix y) (event-set-fix z))
           (subset (setintersect x y)
                   (setintersect x z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     set::subset-in))))

(defthm setintersect-of-nil-2
  (equal (setintersect x nil) (emptyset))
  :hints(("Goal" :in-theory (enable setintersect))))

(defthm relintersect-of-union-1
  (equal (relintersect (union x y) z)
         (union (relintersect x z)
                (relintersect y z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-relation-fix))))

(defthm relintersect-of-subset-1
  (implies (subset (relation-fix x) (relation-fix y))
           (subset (relintersect x z)
                   (relintersect y z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     set::subset-in))))

(defthm relintersect-of-nil-1
  (equal (relintersect nil y) (relidentity (emptyset)))
  :hints(("Goal" :in-theory (enable relintersect))))

(defthm relintersect-of-union-2
  (equal (relintersect x (union y z))
         (union (relintersect x y)
                (relintersect x z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-relation-fix))))

(defthm relintersect-of-subset-2
  (implies (subset (relation-fix y) (relation-fix z))
           (subset (relintersect x y)
                   (relintersect x z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     set::subset-in))))

(defthm relintersect-of-nil-2
  (equal (relintersect x nil) (relidentity (emptyset)))
  :hints(("Goal" :in-theory (enable relintersect))))

(defthm relprod-of-union-1
  (equal (relprod (union x y) z)
         (union (relprod x z)
                (relprod y z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-relprod
                                     in-of-event-set-fix))))

(defthm relprod-of-subset-1
  (implies (subset x y)
           (subset (relprod x z)
                   (relprod y z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-relprod
                                     set::subset-in))))

(defthm relprod-of-nil-1
  (equal (relprod nil y)
         (relidentity (emptyset)))
  :hints(("Goal" :in-theory (enable relprod))))

(defthm relprod-of-union-2
  (equal (relprod x (union y z))
         (union (relprod x y)
                (relprod x z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-relprod
                                     in-of-event-set-fix))))

(defthm relprod-of-subset-2
  (implies (subset y z)
           (subset (relprod x y)
                   (relprod x z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-relprod
                                     set::subset-in))))

(defthm relprod-of-nil-2
  (equal (relprod x nil)
         (relidentity (emptyset)))
  :hints(("Goal" :in-theory (enable relprod
                                    cartesian1))))

(defthm setpreimage-of-union-1
  (equal (setpreimage z (union x y))
         (union (setpreimage z x)
                (setpreimage z y)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-setpreimage-rw
                                     in-of-event-set-fix
                                     ;; in-of-relation-fix
                                     ))))

(defthm setpreimage-of-subset-1
  (implies (subset (event-set-fix x) (event-set-fix y))
           (subset (setpreimage z x)
                   (setpreimage z y)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     set::subset-in
                                     in-of-setpreimage-rw
                                     ;; in-of-relation-fix
                                     ))))

(defthm setpreimage-of-nil-1
  (equal (setpreimage nil y) (emptyset))
  :hints (("goal" :in-theory (e/d (set::double-containment-no-backchain-limit
                                   pick-a-point-subset-strategy
                                   in-of-setpreimage-rw)
                                  (emptyset (emptyset))))))
       

(defthm setpreimage-of-union-2
  (equal (setpreimage (union y z) x)
         (union (setpreimage y x)
                (setpreimage z x)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-setpreimage-rw
                                     in-of-relation-fix))))

(defthm setpreimage-of-subset-2
  (implies (subset (relation-fix y) (relation-fix z))
           (subset (setpreimage y x)
                   (setpreimage z x)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     set::subset-in
                                     in-of-setpreimage-rw
                                     in-of-setpreimage-suff3
                                     ;; in-of-relation-fix
                                     ))))

(defthm setpreimage-of-nil-2
  (equal (setpreimage x nil) (emptyset))
  :hints (("goal" :in-theory (e/d (set::double-containment-no-backchain-limit
                                   pick-a-point-subset-strategy
                                   in-of-setpreimage-rw)
                                  (emptyset (emptyset))))))

  
(defthm setimage-of-union-1
  (equal (setimage (union x y) z)
         (union (setimage x z)
                (setimage y z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-setimage-rw
                                     in-of-event-set-fix
                                     ;; in-of-relation-fix
                                     ))))

(defthm setimage-of-subset-1
  (implies (subset (event-set-fix x) (event-set-fix y))
           (subset (setimage x z)
                   (setimage y z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-setimage-rw
                                     set::subset-in
                                     ;; in-of-relation-fix
                                     ))))

(defthm setimage-of-nil-1
  (equal (setimage nil y) (emptyset))
  :hints (("goal" :in-theory (e/d (set::double-containment-no-backchain-limit
                                   pick-a-point-subset-strategy
                                   in-of-setimage-rw)
                                  (emptyset (emptyset))))))

(defthm setimage-of-union-2
  (equal (setimage x (union y z))
         (union (setimage x y)
                (setimage x z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-setimage-rw
                                     in-of-relation-fix))))

(defthm setimage-of-subset-2
  (implies (subset (relation-fix y) (relation-fix z))
           (subset (setimage x y)
                   (setimage x z)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-setimage-rw
                                     set::subset-in))))

(defthm setimage-of-nil-2
  (equal (setimage x nil) (emptyset))
  :hints (("goal" :in-theory (e/d (set::double-containment-no-backchain-limit
                                   pick-a-point-subset-strategy
                                   in-of-setimage-rw)
                                  (emptyset (emptyset))))))

(defthm relinverse-of-?union
  (equal (relinverse (union x y))
         (union (relinverse x) (relinverse y)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-relation-fix))))

(defthm relinverse-of-subset
  (implies (subset (relation-fix x) (relation-fix y))
           (subset (relinverse x) (relinverse y)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     set::subset-in))))

(defthm relinverse-of-nil
  (equal (relinverse nil)
         (relidentity (emptyset))))

(defthm relidentity-of-?union
  (equal (relidentity (union x y))
         (union (relidentity x) (relidentity y)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-of-relation-fix
                                     in-of-event-set-fix))))

(defthm relidentity-of-subset
  (implies (subset (event-set-fix x) (event-set-fix y))
           (subset (relidentity x) (relidentity y)))
  :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     set::subset-in))))

(defthm relidentity-of-nil
  (equal (relidentity nil)
         (relidentity (emptyset))))
