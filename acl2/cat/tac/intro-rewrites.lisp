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
(local (include-book "propagation"))
(local (include-book "theory-thms"))
(local (include-book "std/util/termhints" :dir :System))
(local (std::add-default-post-define-hook :fix))

;; We want to be able to introduce new event variables in certain situations.
;; E.g., rat-cat-sat's aL/aR rules: if we have a positive predicate of {e}.a
;; (resp. a.{e}), then we introduce a new event variable f, assume (e,f) in a,
;; and replace {e}.a by {f} in the positive predicate.

;; Two challenges here:
;;  a) how do we make sense of this wrt descending through union-free contexts
;;  b) how do we introduce a fresh variable and keep everything invertible.

;; For a), we express the descent through union-free contexts in terms of
;; the existence of intersections. We begin by expressing a set-nonempty predicate
;; as the existence of the intersection of the universe with the set.  For example:
;; (pred-nonempty (setimage (setimage s r1) r2))
;; becomes
;; (pred-set-intersects (universe) (setimage (setimage s r1) r2))

;; At each stage of rewriting here, we have the target term set as the second
;; argument to a pred-set-intersects or pred-rel-intersects call, where the
;; first argument is some accumulation of stuff from the context. The way we
;; accumulate that first argument is determined by "intersect-propagate" rules
;; each of which descends into the second argument and accumulates something
;; onto the first argument. After eventually applying a rewrite (not just a
;; propagation) to the rule, we reverse the propagation to replace the
;; resulting term in its context.

;; For example, to descend into the first argument of the setimage, we apply
;; the rule intersects-setimage-propagate-to-set:
;; (pred-set-intersects (universe) (setimage (setimage s r1) r2))
;; -->
;; (pred-set-intersects (setpreimage r2 (universe)) (setimage s r1))
;; To descend into the second argument of this inner setimage, we instead apply the rule
;; intersects-setimage-propagate-to-rel:
;; -->
;; (pred-rel-intersects (relprod s (setpreimage r2 (universe))) r1)
;; When we have successfully applied some rewrite to 

;; For b), we always introduce fresh variables in the same way, to a
;; pred-set-intersects term:
;; (pred-set-intersects s1 s2)
;; --> (pred-in-set-intersection (nonempty-witness (setintersect s1 s2)) s1 s2)
;; Then generalize away the witness to a fresh variable:
;; --> (pred-in-set-intersection f s1 s2)
;; This generalization preserves satisfiability:
;; if the original (pred-set-intersects s1 s2) is true under some environment,
;; then the new term is true under that environment with f assigned to the
;; nonempty-witness; if the new term is true under some environment, then the
;; original term is also true under that environment.

;; In this schema, we could stop at any stage and introduce a fresh witness
;; variable for the current intersection. However, we actually have only a few
;; specific situations where we want to (corresponding to rat-cat-sat's
;; aL/aR/A/T_1 rules). These mainly just give us certain patterns for when we
;; want to introduce the fresh variables, but also affect how exactly we want
;; to express the conclusion. E.g., for aL, we want the following steps:
;; (pred-set-intersects w (setimage (singleton e) a))
;; -->
;; (pred-in-set-intersection f w (setimage (singleton e) a))
;; -->
;; (pred-in-rel e f a)
;; and
;; (pred-set-intersects w (singleton f))
;; where the pred-in-rel term is a new assumption and the pred-set-intersects
;; term says that (singleton f) replaces the (setimage (singleton e) a) term
;; where it occurred in its context.  In fact, the (pred-set-intersects w
;; (singleton f)) term will be the same for all variable generation rules --
;; the conjunct (pred-in-rel e f a), which expresses the condition under which
;; f is contained in the target term, is what varies.  So this particular
;; variable generation rule can be expressed as simply
;; (iff (pred-in-set f (setimage (singleton e) a))
;;      (pred-in-rel e f a)).


(table tac-rules 'intersect-propagate-rules nil)

(defmacro def-tac-intersect-propagate (name &rest args)
  `(progn (defthm ,name ,@args :rule-classes nil)
          (table tac-rules 'intersect-propagate-rules
                 (cons ',name (cdr (assoc 'intersect-propagate-rules (table-alist 'tac-rules world)))))))


(defthm setimage-of-universe-emptyp
  (iff (emptyp (setimage (universe) r))
       (emptyp (relation-fix r)))
  :hints(("Goal" :in-theory (e/d (in-of-setimage-rw)
                                 (in-of-setimage-suff
                                  in-of-setimage-suff2
                                  in-of-setimage-suff3))
          :use (;; (:instance set::never-in-empty
                ;;  (x (setimage (universe) r))
                ;;  (a (head (relation-fix r))))
                (:instance in-of-setimage-suff
                 (s (universe))
                 (v (edge->dst (head (relation-fix r))))
                 (w (edge->src (head (relation-fix r)))))))))


(defthm pred-set-intersects-with-universe
  (iff (pred-set-intersects (universe) x)
       (pred-nonempty x))
  :hints (("goal" :use ((:instance set::never-in-empty
                         (x (setintersect (universe) x))
                         (a (head (event-set-fix x)))))
           :in-theory (disable set::never-in-empty))))



;; Propagate set-intersects and rel-intersects predicates into arguments
(def-tac-intersect-propagate intersects-setimage-propagate-to-set
  (iff (pred-set-intersects w (setimage s r))
       (pred-set-intersects (setpreimage r w) s))
  :hints((acl2::use-termhint
          (b* ((ss s)
               (pre (setpreimage r w))
               (im (setimage s r))
               (int (setintersect w im))
               (preint (setintersect pre s))
               ;; considering one direction now: w intersects (setimage s r),
               ;; need to prove it also intersects (setimage ss r).
               ;; First show that then (preimage w r) intersects s.
               (int-witness (head int))
               (im-witness (setimage-witness int-witness s r))
               ;; In terms of variables above, int is nonempty, so head of int is in
               ;; both w and im. Im-witness is therefore in s and (im-witness, int-witness) in r.
               ;; This means im-witness is in both s and (setpreimage w r).
               ((unless (pred-set-intersects pre s))
                `(;; :computed-hint-replacement
                  ;; ((and stable-under-simplificationp
                  ;;       '(
                          :use ((:instance set::never-in-empty
                                 (x ,(acl2::hq preint))
                                 (a ,(acl2::hq im-witness))))
                  :in-theory (e/d (in-of-setimage-rw)
                                  (set::never-in-empty))))
               ;; Now we have (pred-set-intersects (setpreimage r w) ss)
               ;; and need to show (pred-set-intersects w (setimage ss r).
               ;; Same sort of thing...
               (preintss (setintersect pre ss))
               (preintss-witness (head preintss))
               (preim-witness (setpreimage-witness preintss-witness r w))
               (intss (setintersect w (setimage ss r))))
            `(:use ((:instance set::never-in-empty
                     (x ,(acl2::hq intss))
                     (a ,(acl2::hq preim-witness))))
              :in-theory (e/d (in-of-setpreimage-rw)
                              (set::never-in-empty)))))))





(def-tac-intersect-propagate intersects-setimage-propagate-to-rel
  (iff (pred-set-intersects w (setimage s r))
       (pred-rel-intersects (relprod s w) r))
  :hints((acl2::use-termhint
          (b* ((rr r)
               (prod (relprod s w))
               (im (setimage s r))
               (int (setintersect w im))
               ;; considering one direction now: w intersects (setimage s r),
               ;; need to prove it also intersects (setimage s rr).
               ;; First show that then (relprod s w) intersects r.
               (int-witness (head int))
               (im-witness (setimage-witness int-witness s r))
               (prod-int (relintersect prod r))
               ;; In terms of variables above, int is nonempty, so head of int
               ;; is in both w and im. Im-witness is therefore in s and
               ;; (im-witness, int-witness) in both r and s x w.
               ((unless (pred-rel-intersects prod r))
                `(;; :computed-hint-replacement
                  ;; ((and stable-under-simplificationp
                  ;;       '(
                  :use ((:instance set::never-in-empty
                         (x ,(acl2::hq prod-int))
                         (a ,(acl2::hq (edge im-witness int-witness)))))
                  :in-theory (e/d (in-of-setimage-rw
                                   in-of-relprod)
                                  (set::never-in-empty))))
               ;; Now we have (pred-rel-intersects prod rr)
               ;; and need to show (pred-set-intersects w (setimage s rr).
               ;; Same sort of thing...
               (prodintrr (relintersect prod rr))
               (prodintrr-witness (head prodintrr))
               (intrr (setintersect w (setimage s rr))))
            `(:use ((:instance set::never-in-empty
                     (x ,(acl2::hq intrr))
                     (a ,(acl2::hq (edge->dst prodintrr-witness))))
                    (:instance in-of-setimage-suff
                     (r rr)
                     (w ,(acl2::hq (edge->src prodintrr-witness)))
                     (v ,(acl2::hq (edge->dst prodintrr-witness)))))
              :in-theory (e/d (in-of-relprod)
                              (set::never-in-empty
                               in-of-setimage-suff))))))
  :otf-flg t)


;; Propagate set-intersects and rel-intersects predicates into arguments
(def-tac-intersect-propagate intersects-setpreimage-propagate-to-set
  (iff (pred-set-intersects w (setpreimage r s))
       (pred-set-intersects (setimage w r) s))
  :hints (("goal" :use ((:instance intersects-setimage-propagate-to-set
                         (w s) (s w)))
           :in-theory (e/d (setintersect
                            set::intersect-symmetric)
                           (emptyp-rw)))))


(def-tac-intersect-propagate intersects-setpreimage-propagate-to-rel
  (iff (pred-set-intersects w (setpreimage r s))
       (pred-rel-intersects (relprod w s) r))
  :hints((acl2::use-termhint
          (b* ((rr r)
               (prod (relprod w s))
               (im (setpreimage r s))
               (int (setintersect w im))
               ;; considering one direction now: w intersects (setimage s r),
               ;; need to prove it also intersects (setimage s rr).
               ;; First show that then (relprod s w) intersects r.
               (int-witness (head int))
               (im-witness (setpreimage-witness int-witness r s))
               (prod-int (relintersect prod r))
               ;; In terms of variables above, int is nonempty, so head of int
               ;; is in both w and im. Im-witness is therefore in s and
               ;; (im-witness, int-witness) in both r and s x w.
               ((unless (pred-rel-intersects prod r))
                `(;; :computed-hint-replacement
                  ;; ((and stable-under-simplificationp
                  ;;       '(
                  :use ((:instance set::never-in-empty
                         (x ,(acl2::hq prod-int))
                         (a ,(acl2::hq (edge int-witness im-witness)))))
                  :in-theory (e/d (in-of-setpreimage-rw
                                   in-of-relprod)
                                  (set::never-in-empty))))
               ;; Now we have (pred-rel-intersects prod rr)
               ;; and need to show (pred-set-intersects w (setimage s rr).
               ;; Same sort of thing...
               (prodintrr (relintersect prod rr))
               (prodintrr-witness (head prodintrr))
               (intrr (setintersect w (setpreimage rr s))))
            `(:use ((:instance set::never-in-empty
                     (x ,(acl2::hq intrr))
                     (a ,(acl2::hq (edge->src prodintrr-witness))))
                    (:instance in-of-setpreimage-suff
                     (r rr)
                     (w ,(acl2::hq (edge->dst prodintrr-witness)))
                     (v ,(acl2::hq (edge->src prodintrr-witness)))))
              :in-theory (e/d (in-of-relprod)
                              (set::never-in-empty
                               in-of-setpreimage-suff))))))
  :otf-flg t)

(encapsulate nil
  (local (defthm setintersect-tmp
           (equal (setintersect (setintersect w s2) s1)
                  (setintersect w (setintersect s1 s2)))
           :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                             set::double-containment-no-backchain-limit)))))

  (def-tac-intersect-propagate intersects-setintersect-propagate-1
    (iff (pred-set-intersects w (setintersect s1 s2))
         (pred-set-intersects (setintersect w s2) s1))))

(encapsulate nil
  (local (defthm setintersect-tmp
           (equal (setintersect (setintersect w s1) s2)
                  (setintersect w (setintersect s1 s2)))
           :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                             set::double-containment-no-backchain-limit)))))

  (def-tac-intersect-propagate intersects-setintersect-propagate-2
    (iff (pred-set-intersects w (setintersect s1 s2))
         (pred-set-intersects (setintersect w s1) s2))))


(def-tac-intersect-propagate intersects-relidentity
  (iff (pred-rel-intersects w (relidentity s))
       (pred-set-intersects (range (relintersect w (relidentity (universe)))) s))
  :hints (("goal" :use ((:instance set::never-in-empty
                         (x (setintersect (range (relintersect w (relidentity (universe)))) s))
                         (a (EDGE->SRC (HEAD (RELINTERSECT W (RELIDENTITY S))))))
                        (:instance set::never-in-empty
                         (x (relintersect w (relidentity s)))
                         (a (edge (head (setintersect (range (relintersect w (relidentity (universe)))) s))
                                  (head (setintersect (range (relintersect w (relidentity (universe)))) s))))))
           :in-theory (e/d (in-of-range-suff-free
                            in-of-range-rw)
                           (set::never-in-empty))))
  :otf-flg t)


(encapsulate nil
  (local (defthm relintersect-tmp
           (equal (relintersect (relintersect w r2) r1)
                  (relintersect w (relintersect r1 r2)))
           :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                             set::double-containment-no-backchain-limit)))))

  (def-tac-intersect-propagate intersects-relintersect-propagate-1
    (iff (pred-rel-intersects w (relintersect r1 r2))
         (pred-rel-intersects (relintersect w r2) r1))))

(encapsulate nil
  (local (defthm relintersect-tmp
           (equal (relintersect (relintersect w r1) r2)
                  (relintersect w (relintersect r1 r2)))
           :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                             set::double-containment-no-backchain-limit)))))

  (def-tac-intersect-propagate intersects-relintersect-propagate-2
    (iff (pred-rel-intersects w (relintersect r1 r2))
         (pred-rel-intersects (relintersect w r1) r2))))


(def-tac-intersect-propagate intersects-relcompose-propagate-1
  (iff (pred-rel-intersects w (relcompose r1 r2))
       (pred-rel-intersects (relcompose w (relinverse r2)) r1))
  :hints ((acl2::use-termhint
           (b* ((comp (relcompose r1 r2))
                (compint (relintersect w comp))
                (compinv (relcompose w (relinverse r2)))
                (compinvint (relintersect compinv r1))
                ((when (pred-rel-intersects w (relcompose r1 r2)))
                 (b* (((edge intw) (head compint))
                      (compw (relcompose-midpoint intw.src intw.dst r1 r2)))
                   `(:use ((:instance set::never-in-empty
                            (x ,(acl2::hq compinvint))
                            (a ,(acl2::hq (edge intw.src compw))))
                           (:instance in-of-relcompose-suff
                            (pair ,(acl2::hq (edge intw.src compw)))
                            (mid ,(acl2::hq intw.dst))
                            (x w) (y (relinverse r2))))
                     :in-theory (e/d (in-of-relcompose-rw)
                                     (set::never-in-empty)))))
                ((edge intw) (head compinvint))
                (compw (relcompose-midpoint intw.src intw.dst w (relinverse r2))))
             `(:use ((:instance set::never-in-empty
                      (x ,(acl2::hq compint))
                      (a ,(acl2::hq (edge intw.src compw))))
                     (:instance in-of-relcompose-suff
                      (pair ,(acl2::hq (edge intw.src compw)))
                      (mid ,(acl2::hq intw.dst))
                      (x r1) (y r2)))
               :in-theory (e/d (in-of-relcompose-rw)
                               (set::never-in-empty))))))
  :otf-flg t)


(def-tac-intersect-propagate intersects-relcompose-propagate-2
  (iff (pred-rel-intersects w (relcompose r1 r2))
       (pred-rel-intersects (relcompose (relinverse r1) w) r2))
  :hints ((acl2::use-termhint
           (b* ((comp (relcompose r1 r2))
                (compint (relintersect w comp))
                (compinv (relcompose (relinverse r1) w))
                (compinvint (relintersect compinv r2))
                ((when (pred-rel-intersects w (relcompose r1 r2)))
                 (b* (((edge intw) (head compint))
                      (compw (relcompose-midpoint intw.src intw.dst r1 r2)))
                   `(:use ((:instance set::never-in-empty
                            (x ,(acl2::hq compinvint))
                            (a ,(acl2::hq (edge compw intw.dst))))
                           (:instance in-of-relcompose-suff
                            (pair ,(acl2::hq (edge compw intw.dst)))
                            (mid ,(acl2::hq intw.src))
                            (x (relinverse r1)) (y w)))
                     :in-theory (e/d (in-of-relcompose-rw)
                                     (set::never-in-empty)))))
                ((edge intw) (head compinvint))
                (compw (relcompose-midpoint intw.src intw.dst (relinverse r1) w)))
             `(:use ((:instance set::never-in-empty
                      (x ,(acl2::hq compint))
                      (a ,(acl2::hq (edge compw intw.dst))))
                     (:instance in-of-relcompose-suff
                      (pair ,(acl2::hq (edge compw intw.dst)))
                      (mid ,(acl2::hq intw.src))
                      (x r1) (y r2)))
               :in-theory (e/d (in-of-relcompose-rw)
                               (set::never-in-empty))))))
  :otf-flg t)

(def-tac-intersect-propagate intersects-relinverse-propagate
  (iff (pred-rel-intersects w (relinverse r))
       (pred-rel-intersects (relinverse w) r))
  :hints (("goal" :use ((:instance set::never-in-empty
                         (x (relintersect w (relinverse r)))
                         (a (edge (edge->dst (head (relintersect (relinverse w) r)))
                                  (edge->src (head (relintersect (relinverse w) r))))))
                        (:instance set::never-in-empty
                         (x (relintersect (relinverse w) r))
                         (a (edge (edge->dst (head (relintersect w (relinverse r))))
                                  (edge->src (head (relintersect w (relinverse r))))))))
           :in-theory (disable set::never-in-empty))))


(def-tac-intersect-propagate intersects-relprod-propagate-1
  (iff (pred-rel-intersects w (relprod s1 s2))
       (pred-set-intersects (setpreimage w s2) s1))
  :hints(("Goal" :use ((:instance intersects-setpreimage-propagate-to-rel
                        (r w) (s s2) (w s1)))
          :in-theory (e/d (setintersect
                           relintersect
                           set::intersect-symmetric)
                          (emptyp-rw)))))

(def-tac-intersect-propagate intersects-relprod-propagate-2
  (iff (pred-rel-intersects w (relprod s1 s2))
       (pred-set-intersects (setimage s1 w) s2))
  :hints(("Goal" :use ((:instance intersects-setimage-propagate-to-rel
                        (r w) (s s1) (w s2)))
          :in-theory (e/d (setintersect
                           relintersect
                           set::intersect-symmetric)
                          (emptyp-rw)))))





(table tac-rules 'var-intro-rules nil)




(defmacro def-tac-var-intro (name &rest args)
  `(progn (defthm ,name ,@args :rule-classes nil)
          (table tac-rules 'var-intro-rules
                 (cons ',name (cdr (assoc 'var-intro-rules (table-alist 'tac-rules world)))))))

(local (in-theory (disable (singleton))))



;; (local (defthm emptyp-setintersect-with-singleton
;;          (iff (emptyp (setintersect w (singleton e)))
;;               (not (pred-in-set e w)))
;;          :hints (("goal" :use ((:instance set::never-in-empty
;;                                 (x (setintersect w (singleton e)))
;;                                 (a (event-fix e))))
;;                   :in-theory (disable set::never-in-empty)))
;;          :otf-flg t))

(def-tac-var-intro intro-intersects-singleton-setimage-with-base-rel
  (implies (base-rel-p a)
           (iff (pred-in-set f (setimage (singleton e) a))
                (pred-in-rel e f a)))
  :hints(("Goal" :in-theory (e/d (in-of-setimage-rw)))))




(def-tac-var-intro intro-intersects-singleton-setpreimage-with-base-rel
  (implies (base-rel-p a)
           (iff (pred-in-set f (setpreimage a (singleton e)))
                (pred-in-rel f e a)))
  :hints(("Goal" :in-theory (e/d (in-of-setpreimage-rw)))))


(def-tac-var-intro intro-intersects-base-set
  (implies (base-set-p a)
           (iff (pred-in-set f a)
                (pred-in-set f a))))

(def-tac-var-intro intro-intersects-universe
  (iff (pred-in-set f (universe))
       (pred-true)))
