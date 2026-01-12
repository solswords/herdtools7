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
  :hints(("Goal" :in-theory (e/d (in-of-relprod))))
  :otf-flg t)

;; XR
(def-tac-positive-normalize in-setpreimage-singleton-prod
  (iff (pred-in-set w (setpreimage (relprod s (singleton e2))
                          (singleton e1)))
       (and (pred-equal e1 e2)
            (pred-in-set w s)))
  :hints(("Goal" :in-theory (e/d (in-of-relprod))))
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





;; *L
(def-tac-positive-normalize in-setimage-singleton-star
  (iff (pred-in-set w (setimage (singleton e) (relstar r)))
       (or (pred-in-set w (singleton e))
           (pred-in-set w (setimage (setimage (singleton e) r)
                                    (relstar r)))))
  :hints(("Goal" :in-theory (e/d (relstar
                                  setimage-of-relcompose-inverse
                                  in-of-relcompose-rw
                                  in-of-relplus-split
                                  in-of-relcompose-suff-rw)
                                 (setimage-of-relcompose))))
  :otf-flg t)

;; +L
(def-tac-positive-normalize in-setimage-singleton-plus
  (iff (pred-in-set w (setimage (singleton e) (relplus r)))
       (or (pred-in-set w (setimage (singleton e) r))
           (pred-in-set w (setimage (setimage (singleton e) r)
                                    (relplus r)))))
  :hints(("Goal" :in-theory (e/d (relplus
                                  setimage-of-relcompose-inverse
                                  in-of-relplus-split
                                  in-of-relcompose-rw
                                  in-of-relcompose-suff-rw)
                                 (setimage-of-relcompose))))
  :otf-flg t)


;; *R
(def-tac-positive-normalize in-setpreimage-singleton-star
  (iff (pred-in-set w (setpreimage (relstar r) (singleton e)))
       (or (pred-in-set w (singleton e))
           (pred-in-set w (setpreimage (relstar r)
                                       (setpreimage r (singleton e))))))
  :hints(("Goal" :in-theory (e/d (relstar
                                  setpreimage-of-relcompose-inverse
                                  in-of-relplus-split2
                                  in-of-relcompose-suff-rw2
                                  in-of-relcompose-rw)
                                 (setpreimage-of-relcompose))))
  :otf-flg t)

;; +R
(def-tac-positive-normalize in-setpreimage-singleton-plus
  (iff (pred-in-set w (setpreimage (relplus r) (singleton e)))
       (or (pred-in-set w (setpreimage r (singleton e)))
           (pred-in-set w (setpreimage (relplus r)
                                       (setpreimage r (singleton e))))))
  :hints(("Goal" :in-theory (e/d (relstar
                                  in-of-relplus-split2
                                  in-of-relcompose-rw
                                  in-of-relcompose-suff-rw
                                  setpreimage-of-relcompose-inverse)
                                 (setpreimage-of-relcompose
                                  in-of-relcompose-rw))))
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



;; ~*L
(def-tac-negative-normalize in-singleton-star-image
  (iff (pred-in-set w (setimage (singleton e) (relstar r)))
       (or (pred-in-set w (singleton e))
           (pred-in-set w (setimage (setimage (singleton e) r) (relstar r)))))
  :hints(("Goal" :in-theory (e/d (relstar
                                  setimage-of-relcompose-inverse
                                  in-of-relplus-split
                                  in-of-relcompose-suff
                                  in-of-relcompose-suff2
                                  in-of-relcompose-suff-rw
                                  in-of-relcompose-rw)
                                 (setimage-of-relcompose)))))

;; ~+L
(def-tac-negative-normalize in-singleton-plus-image
  (iff (pred-in-set w (setimage (singleton e) (relplus r)))
       (or (pred-in-set w (setimage (singleton e) r))
           (pred-in-set w (setimage (setimage (singleton e) r) (relplus r)))))
  :hints(("Goal" :in-theory (e/d (relstar
                                  setimage-of-relcompose-inverse
                                  in-of-relcompose-suff
                                  in-of-relcompose-suff2
                                  in-of-relcompose-suff-rw
                                  in-of-relplus-split
                                  in-of-relcompose-rw)
                                 (setimage-of-relcompose)))))

;; ~*R
(def-tac-negative-normalize in-singleton-star-preimage
  (iff (pred-in-set w (setpreimage (relstar r) (singleton e)))
       (or (pred-in-set w (singleton e))
           (pred-in-set w (setpreimage (relstar r) (setpreimage r (singleton e))))))
  :hints(("Goal" :in-theory (e/d (relstar
                                  setpreimage-of-relcompose-inverse
                                  in-of-relplus-split2
                                  in-of-relcompose-suff
                                  in-of-relcompose-suff2
                                  in-of-relcompose-suff-rw2
                                  in-of-relcompose-rw)
                                 (setpreimage-of-relcompose)))))


;; ~+R
(def-tac-negative-normalize in-singleton-plus-preimage
  (iff (pred-in-set w (setpreimage (relplus r) (singleton e)))
       (or (pred-in-set w (setpreimage r (singleton e)))
           (pred-in-set w (setpreimage (relplus r) (setpreimage r (singleton e))))))
  :hints(("Goal" :in-theory (e/d (relstar
                                  setpreimage-of-relcompose-inverse
                                  in-of-relplus-split2
                                  in-of-relcompose-suff
                                  in-of-relcompose-suff2
                                  in-of-relcompose-suff-rw
                                  in-of-relcompose-rw)
                                 (setpreimage-of-relcompose)))))

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

(local (defthm emptyp-intersect-singleton
         (iff (emptyp (setintersect (singleton e) s))
              (not (in (event-fix e) (event-set-fix s))))
         :hints (("goal" :use ((:instance emptyp-when-in
                                (x (setintersect (singleton e) s))
                                (e (event-fix e))))
                  :in-theory (disable emptyp-when-in)))))

(local (defthm emptyp-intersect-singleton2
         (iff (emptyp (setintersect s (singleton e)))
              (not (in (event-fix e) (event-set-fix s))))
         :hints (("goal" :use ((:instance emptyp-when-in
                                (x (setintersect s (singleton e)))
                                (e (event-fix e))))
                  :in-theory (disable emptyp-when-in)))))



;; ~XL
(def-tac-negative-normalize in-singleton-image-prod
  (iff (pred-in-set w (setimage (singleton e) (relprod s1 s2)))
       (and (pred-nonempty (setintersect (singleton e) s1))
            (pred-in-set w s2)))
  :hints(("Goal" :in-theory (enable in-of-relprod))))
  
;; ~XR
(def-tac-negative-normalize in-singleton-preimage-prod
  (iff (pred-in-set w (setpreimage (relprod s1 s2) (singleton e)))
       (and (pred-nonempty (setintersect (singleton e) s2))
            (pred-in-set w s1)))
  :hints(("Goal" :in-theory (enable in-of-relprod))))



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
  (implies (non-toplevel)
           (iff (pred-in-set w (setintersect (singleton e) s))
                (and (pred-in-set w (singleton e))
                     (pred-nonempty (setintersect (singleton e) s))))))

;; ~eR
(def-tac-negative-normalize in-singleton-intersect-2
  (implies (non-toplevel)
           (iff (pred-in-set w (setintersect s (singleton e)))
                (and (pred-in-set w (singleton e))
                     (pred-nonempty (setintersect s (singleton e)))))))



;; (defthm singleton-intersect-image
;;   (equal (intersect (insert e nil) (image s r))
;;          (intersect (preimage (insert e nil) r) s))
;;   :hints (("goal" :in-theory (enable set::double-containment-no-backchain-limit
;;                                      pick-a-point-subset-strategy))))


;; ~1XL
(def-tac-negative-normalize in-image-product-singleton-1
  (iff (pred-in-set w (setimage s1 (relprod (singleton e) s2)))
       (and (pred-in-set w s2)
            (pred-nonempty (setintersect s1 (singleton e)))))
  :hints(("Goal" :in-theory (enable in-of-setimage-rw
                                    in-of-relprod))))
;; ~1XR
(def-tac-negative-normalize in-image-product-singleton-2
  (iff (pred-in-set w (setpreimage (relprod s2 (singleton e)) s1))
       (and (pred-in-set w s2)
            (pred-nonempty (setintersect s1 (singleton e)))))
  :hints(("Goal" :in-theory (enable in-of-setpreimage-rw
                                    in-of-relprod))))

(local (defthm emptyp-rw-when-event-set-p
         (implies (and (acl2::rewriting-positive-literal `(emptyp ,x))
                       (event-set-p x))
                  (iff (emptyp x)
                       (not (and (in (head x) x)
                                 (event-p (head x))))))))
(local (in-theory (disable emptyp-rw)))

;; ~X1L
(def-tac-negative-normalize in-setimage-product-singleton-3
  (iff (pred-in-set w (setpreimage (relprod (singleton e) s1) s2))
       (and (pred-in-set w (singleton e))
            (pred-nonempty (setintersect s1 s2))))
  :hints(("Goal" :in-theory (e/d (in-of-setpreimage-rw
                                  in-of-relprod)
                                 (emptyp-when-in
                                  set::never-in-empty))
          :use ((:instance emptyp-when-in
                 (e (setpreimage-witness w (relprod (singleton e) s1) s2))
                 (x (setintersect s1 s2)))))))

;; ~X1R
(def-tac-negative-normalize in-setimage-product-singleton-4
  (iff (pred-in-set w (setimage s2 (relprod s1 (singleton e))))
       (and (pred-in-set w (singleton e))
            (pred-nonempty (setintersect s1 s2))))
  :hints(("Goal" :in-theory (e/d (in-of-setimage-rw
                                  in-of-relprod)
                                 (emptyp-when-in
                                  set::never-in-empty))
          :use ((:instance emptyp-when-in
                 (e (setimage-witness w s2 (relprod s1 (singleton e))))
                 (x (setintersect s1 s2)))))))


(acl2::def-ruleset tac-negative-toplevel-normalize-rules nil)
(defmacro def-tac-negative-toplevel-normalize (name &rest args)
  `(progn (defthm ,name . ,args)
          (acl2::add-to-ruleset tac-negative-toplevel-normalize-rules ,name)))



;; ~.1,2L
(def-tac-negative-toplevel-normalize nonempty-singleton-intersect-setimage-1
  (implies (not-singleton-set-p s)
           (iff (pred-nonempty (setintersect (singleton e) (setimage s r)))
                (pred-nonempty (setintersect (setpreimage r (singleton e)) s))))
  :hints(("Goal" :in-theory (e/d (in-of-setimage-rw)))
         (and stable-under-simplificationp
              '(:in-theory (e/d (in-of-setimage-rw)
                                (emptyp-when-in
                                 set::never-in-empty))
                :use ((:instance emptyp-when-in
                       (x (setintersect (setpreimage r (singleton e)) s))
                       (e (setimage-witness e s r)))))))
  :otf-flg t)

;; ~.1,2R
(def-tac-negative-toplevel-normalize nonempty-singleton-intersect-setimage-2
  (implies (not-singleton-set-p s)
           (iff (pred-nonempty (setintersect (setimage s r) (singleton e)))
                (pred-nonempty (setintersect s (setpreimage r (singleton e))))))
  :hints(("Goal" :in-theory (e/d (in-of-setimage-rw)))
         (and stable-under-simplificationp
              '(:in-theory (e/d (in-of-setimage-rw)
                                (emptyp-when-in
                                 set::never-in-empty))
                :use ((:instance emptyp-when-in
                       (x (setintersect s (setpreimage r (singleton e))))
                       (e (setimage-witness e s r)))))))
  :otf-flg t)




;; ~.2,1L
(def-tac-negative-toplevel-normalize nonempty-singleton-intersect-setimage-3
  (implies (not-singleton-set-p s)
           (iff (pred-nonempty (setintersect (singleton e) (setpreimage r s)))
                (pred-nonempty (setintersect (setimage (singleton e) r) s))))
  :hints(("Goal" :in-theory (e/d (in-of-setpreimage-rw)))
         (and stable-under-simplificationp
              '(:in-theory (e/d (in-of-setpreimage-rw)
                                (emptyp-when-in
                                 set::never-in-empty))
                :use ((:instance emptyp-when-in
                       (x (setintersect (setimage (singleton e) r) s))
                       (e (setpreimage-witness e r s)))))))
  :otf-flg t)
;; ~.2,1R
(def-tac-negative-toplevel-normalize nonempty-singleton-intersect-setimage-4
  (implies (not-singleton-set-p s)
           (iff (pred-nonempty (setintersect (setpreimage r s) (singleton e)))
                (pred-nonempty (setintersect s (setimage (singleton e) r)))))
  :hints(("Goal" :in-theory (e/d (in-of-setpreimage-rw)))
         (and stable-under-simplificationp
              '(:in-theory (e/d (in-of-setpreimage-rw)
                                (emptyp-when-in
                                 set::never-in-empty))
                :use ((:instance emptyp-when-in
                       (x (setintersect s (setimage (singleton e) r)))
                       (e (setpreimage-witness e r s)))))))
  :otf-flg t)

;; ~\cap1L
(def-tac-negative-toplevel-normalize nonempty-singleton-intersect-intersect-1
  (iff (pred-nonempty (setintersect (singleton e) (setintersect s1 s2)))
       (and (pred-nonempty (setintersect (singleton e) s1))
            (pred-nonempty (setintersect (singleton e) s2)))))
;; ~\cap1R
(def-tac-negative-toplevel-normalize nonempty-singleton-intersect-intersect-2
  (iff (pred-nonempty (setintersect (setintersect s1 s2) (singleton e)))
       (and (pred-nonempty (setintersect s1 (singleton e)))
            (pred-nonempty (setintersect s2 (singleton e))))))

;; ~\cap_e
(def-tac-negative-toplevel-normalize nonempty-singleton-intersect-singleton
  (iff (pred-nonempty (setintersect (singleton e1) (singleton e2)))
       (pred-equal e1 e2)))

;; ~0
(def-tac-negative-toplevel-normalize pred-nonempty-of-singleton
  (iff (pred-nonempty (singleton e))
       (pred-true))
  :hints(("Goal" :in-theory (enable singleton))))

;; ~=
(def-tac-negative-toplevel-normalize pred-equal-same
  (iff (pred-equal e e)
       (pred-true)))

