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

(in-package "CAT")

(include-book "built-in-ops")

(defsection exists-bounded-path
  (defun-sk exists-bounded-path (src dst len x)
    (exists path
            (and (relation-path-p path x)
                 (equal src (car path))
                 (equal dst (car (last path)))
                 (<= (len path) (nfix len)))))

  (in-theory (disable exists-bounded-path))

  (defthmd exists-path-when-exists-bounded-path
    (implies (exists-bounded-path src dst len x)
             (exists-path src dst x))
    :hints(("Goal" :in-theory (enable exists-bounded-path))))

  (defthmd exists-bounded-path-when-exists-path
    (implies (and (exists-path src dst x)
                  (<= (len (exists-path-witness src dst x)) (nfix len)))
             (exists-bounded-path src dst len x))
    :hints(("Goal" :in-theory (enable exists-path)))))

(define bounded-transitive-closure ((n natp)
                                    (x relation-p))
  :returns (closure relation-p)
  :verify-guards nil
  (if (zp n)
      (relation-fix x)
    (union (relation-fix x)
           (compose x (bounded-transitive-closure (1- n) x))))
  ///
  (verify-guards bounded-transitive-closure)
             
  (defthm in-bounded-transitive-closure-when-relation-path-p
    (implies (and (relation-path-p path x)
                  (<= (len path) (+ 2 (nfix n))))
             (in (evtpair (car path)
                          (car (last path)))
                 (bounded-transitive-closure n x)))
    :hints (("goal" :induct (nthcdr n path)
             :expand ((relation-path-p path x)
                      (bounded-transitive-closure n x))
             :in-theory (enable member-of-compose-suff-rw))))
  
  (defthm in-bounded-transitive-closure-when-exists-bounded-path
    (implies (and (exists-bounded-path (evtpair->from pair)
                                       (evtpair->to pair) (+ 2 (nfix n)) x)
                  (evtpair-p pair))
             (in pair (bounded-transitive-closure n x)))
    :hints (("goal" :in-theory (e/d (exists-bounded-path)
                                    (in-bounded-transitive-closure-when-relation-path-p))
             :use ((:instance in-bounded-transitive-closure-when-relation-path-p
                    (path (exists-bounded-path-witness (evtpair->from pair)
                                                       (evtpair->to pair)
                                                       (+ 2 (nfix n)) x))))
             :do-not-induct t))))

(define bounded-transitive-closure-path ((src evt-p)
                                         (dst evt-p)
                                         (n natp) (x relation-p))
  :returns (path evtlist-p)
  :guard (in (evtpair src dst) (bounded-transitive-closure n x))
  :measure (nfix n)
  :guard-hints (("goal" :expand ((bounded-transitive-closure n x))
                 :in-theory (enable member-of-compose-necc)))
  (if (zp n)
      (list (evt-fix src) (evt-fix dst))
    (if (in (evtpair src dst) (relation-fix x))
        (list (evt-fix src) (evt-fix dst))
      (let ((closure (bounded-transitive-closure (1- n) x)))
        (cons (evt-fix src)
              (bounded-transitive-closure-path (compose-midpoint src dst x closure) dst
                                               (1- n) x)))))
  ///
  (defret car-of-<fn>
    (equal (car path) (evt-fix src)))

  (defret car-last-of-<fn>
    (equal (car (last path)) (evt-fix dst)))
  
  (defret relation-path-p-of-<fn>
    (implies (in (evtpair src dst) (bounded-transitive-closure n x))
             (relation-path-p path x))
    :hints(("Goal" :induct <call>
            :in-theory (enable member-of-compose-rw)
            :expand ((:free (a b) (relation-path-p (cons a b) x))
                     (bounded-transitive-closure n x)))))

  (defret len-of-<fn>
    (<= (len path) (+ 2 (nfix n)))
    :rule-classes :linear))


(defthmd bounded-transitive-closure-correct
  (iff (in pair (bounded-transitive-closure n x))
       (and (evtpair-p pair)
            (exists-bounded-path (evtpair->from pair)
                                 (evtpair->to pair)
                                 (+ 2 (nfix n))
                                 x)))
  :hints (("goal" :use ((:instance exists-bounded-path-suff
                         (path (bounded-transitive-closure-path
                                (evtpair->from pair)
                                (evtpair->to pair)
                                n x))
                         (src (evtpair->from pair))
                         (dst (evtpair->to pair))
                         (len (+ 2 (nfix n)))))
           :in-theory (disable exists-bounded-path-suff))))


(define max-path-length ((rel relation-p) (x relation-p))
  :guard (subset rel (transitive-closure x))
  :returns (max-len natp :rule-classes :type-prescription)
  :measure (acl2-count (relation-fix rel))
  :guard-hints (("goal" :expand ((subset rel (transitive-closure x)))))
  (b* ((rel (relation-fix rel)))
    (if (emptyp rel)
        0
      (b* ((pair (head rel)))
        (max (if (in pair (transitive-closure x))
                 (len (transitive-path (evtpair->from pair)
                                       (evtpair->to pair)
                                       x))
               0)
             (max-path-length (tail rel) x)))))
  ///
  (defret path-length-less-than-<fn>
    (implies (and (in pair (relation-fix rel))
                  (in pair (transitive-closure x)))
             (<= (len (transitive-path (evtpair->from pair)
                                       (evtpair->to pair)
                                       x))
                 max-len))
    :rule-classes :linear)

  (defret max-len-when-nonempty
    (implies (and (not (emptyp (relation-fix rel)))
                  (subset (relation-fix rel) (transitive-closure x)))
             (<= 2 max-len))
    :hints(("Goal" :induct <call>
            :expand ((subset (relation-fix rel) (transitive-closure x)))))
    :rule-classes :linear))

(define transitive-closure-bound ((x relation-p))
  :returns (bound natp :rule-classes :type-prescription)
  (let* ((closure (transitive-closure x))
         (max-len (max-path-length closure x)))
    (max 0 (- max-len 2)))
  ///
  (defthmd in-transitive-closure-when-in-bounded-transitive-closure
    (implies (in pair (bounded-transitive-closure n x))
             (in pair (transitive-closure x)))
    :hints(("Goal" :in-theory (enable transitive-closure-correct
                                      bounded-transitive-closure-correct
                                      exists-path-when-exists-bounded-path))))


  
  (defretd in-bounded-transitive-closure-when-in-transitive-closure
    (implies (in pair (transitive-closure x))
             (in pair (bounded-transitive-closure bound x)))
    :hints(("Goal" :in-theory (e/d ;; transitive-closure-correct
                               (bounded-transitive-closure-correct
                                exists-path-when-exists-bounded-path)
                               (path-length-less-than-max-path-length))
            :use ((:instance exists-bounded-path-suff
                   (src (evtpair->from pair))
                   (dst (evtpair->to pair))
                   (len (max-path-length (transitive-closure x) x))
                   (path (transitive-path (evtpair->from pair)
                                          (evtpair->to pair)
                                          x)))
                  (:instance path-length-less-than-max-path-length
                   (rel (transitive-closure x)))))))
  
  (defretd transitive-closure-in-terms-of-bounded
    (equal (transitive-closure x)
           (bounded-transitive-closure bound x))
    :hints (("goal" :in-theory (e/d (set::double-containment-no-backchain-limit
                                     pick-a-point-subset-strategy
                                     in-transitive-closure-when-in-bounded-transitive-closure
                                     in-bounded-transitive-closure-when-in-transitive-closure)
                                    (transitive-closure-bound)))
            (SET::PICK-A-POINT-SUBSET-HINT ID acl2::CLAUSE
                                           WORLD STABLE-UNDER-SIMPLIFICATIONP))))

