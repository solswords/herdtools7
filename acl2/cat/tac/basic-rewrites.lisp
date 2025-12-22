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
(local (include-book "theory-thms"))
(acl2::def-ruleset! tac-rewrites nil)




(defmacro def-tac-rewrite (name &rest args)
  `(progn (defthm ,name . ,args)
          (acl2::add-to-ruleset tac-rewrites ,name)))

;; All these rewrite rules have these properties
;; - If the LHS matches with a well-typed (set-term-p/rel-term-p) term,
;;   then the RHS also is well-typed (in the same sense).
;; - If the LHS matches with a well-typed term, then the hyps are true.


(def-tac-rewrite setunion-of-emptyset
  (implies (event-set-p s)
           (equal (setunion (emptyset) s)
                  s))
  :hints(("Goal" :in-theory (enable setunion))))

(def-tac-rewrite setunion-of-emptyset-2
  (implies (event-set-p s)
           (equal (setunion s (emptyset))
                  s))
  :hints(("Goal" :in-theory (enable setunion))))


(def-tac-rewrite setunion-of-universe
  (implies (event-set-p s)
           (equal (setunion (universe) s)
                  (universe)))
  :hints(("Goal" :in-theory (enable setunion))))

(def-tac-rewrite setunion-of-universe-2
  (implies (event-set-p s)
           (equal (setunion s (universe))
                  (universe)))
  :hints(("Goal" :in-theory (enable setunion))))

(def-tac-rewrite setintersect-of-emptyset
  (equal (setintersect (emptyset) s) (emptyset))
  :hints(("Goal" :in-theory (enable setintersect))))

(def-tac-rewrite setintersect-of-emptyset-2
  (equal (setintersect s (emptyset))
         (emptyset))
  :hints(("Goal" :in-theory (enable setintersect))))

(def-tac-rewrite setintersect-of-universe
  (implies (event-set-p s)
           (equal (setintersect (universe) s)
                  s))
  :hints(("Goal" :in-theory (enable setintersect))))

(def-tac-rewrite setintersect-of-universe-2
  (implies (event-set-p s)
           (equal (setintersect s (universe))
                  s))
  :hints(("Goal" :in-theory (enable setintersect))))

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
  (equal (setpreimage (relcompose z y) x)
         (setpreimage z (setpreimage y x))))

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
                  r))
  :hints(("Goal" :in-theory (enable relunion))))

(def-tac-rewrite relunion-of-empty-2
  (implies (relation-p r)
           (equal (relunion r (relidentity (emptyset)))
                  r))
  :hints(("Goal" :in-theory (enable relunion))))

(def-tac-rewrite relunion-of-universe
  (implies (relation-p r)
           (equal (relunion (relprod (universe) (universe)) r)
                  (relprod (universe) (universe))))
  :hints(("Goal" :in-theory (enable relunion))))

(def-tac-rewrite relunion-of-universe-2
  (implies (relation-p r)
           (equal (relunion r (relprod (universe) (universe)))
                  (relprod (universe) (universe))))
  :hints(("Goal" :in-theory (enable relunion))))

(def-tac-rewrite relunion-of-relinverses
  (equal (relunion (relinverse x) (relinverse y))
         (relinverse (relunion x y))))

(def-tac-rewrite relintersect-of-relinverses
  (equal (relintersect (relinverse x) (relinverse y))
         (relinverse (relintersect x y)))) ;; or backward?

(def-tac-rewrite relintersect-of-emptyrel
  (equal (relintersect (relidentity (emptyset)) r)
         (relidentity (emptyset)))
  :hints(("Goal" :in-theory (enable relintersect))))

(def-tac-rewrite relintersect-of-emptyrel-2
  (equal (relintersect r (relidentity (emptyset)))
         (relidentity (emptyset)))
  :hints(("Goal" :in-theory (enable relintersect))))

(def-tac-rewrite relintersect-of-univrel
  (implies (and (relation-p r)
                (relation-p r))
           (equal (relintersect (relprod (universe) (universe)) r)
                  r))
  :hints(("Goal" :in-theory (enable relintersect))))

(def-tac-rewrite relintersect-of-univrel-2
  (implies (and (relation-p r)
                (relation-p r))
           (equal (relintersect r (relprod (universe) (universe)))
                  r))
  :hints(("Goal" :in-theory (enable relintersect))))

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
  (equal (relstar (relidentity s))
         (relidentity (universe))))

(def-tac-rewrite relplus-of-relidentity
  (equal (relplus (relidentity s))
         (relidentity s)))

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
