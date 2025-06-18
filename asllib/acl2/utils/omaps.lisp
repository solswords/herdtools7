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

(in-package "OMAP")

(include-book "std/omaps/core" :dir :system)
(local (include-book "std/lists/sets" :dir :system))






(local (defthm mapp-of-acons
         (implies (and (mapp rest)
                       (case-split
                         (or (emptyp rest)
                             (<< key (mv-nth 0 (head rest))))))
                  (mapp (cons (cons key val) rest)))
         :hints(("Goal" :in-theory (enable mapp emptyp head)))))

(local (defthm head-of-acons
         (implies (and (mapp rest)
                       (case-split
                         (or (emptyp rest)
                             (<< key (mv-nth 0 (head rest))))))
                  (equal (head (cons (cons key val) rest))
                         (mv key val)))
         :hints(("Goal" :in-theory (enable emptyp head)))))

(local (defthm emptyp-of-acons
         (implies (and (mapp rest)
                       (case-split
                         (or (emptyp rest)
                             (<< key (mv-nth 0 (head rest))))))
                  (not (emptyp (cons (cons key val) rest))))
         :hints(("Goal" :in-theory (enable emptyp)))))

(local (defthm tail-of-acons
         (implies (and (mapp rest)
                       (case-split
                         (or (emptyp rest)
                             (<< key (mv-nth 0 (head rest))))))
                  (equal (tail (cons (cons key val) rest))
                         rest))
         :hints(("Goal" :in-theory (enable tail)))))

(local (defthm head-ordered
         (implies (not (emptyp (tail x)))
                  (<< (mv-nth 0 (head x))
                      (mv-nth 0 (head (tail x)))))
         :hints(("Goal" :in-theory (enable head tail emptyp mfix mapp)))))

(defthm emptyp-of-keys
  (equal (set::emptyp (keys x))
         (emptyp x))
  :hints(("Goal" :in-theory (enable keys))))


#!set
(local
 (encapsulate nil
   (defthm head-of-cons
     (implies (and (setp b)
                   (or (emptyp b)
                       (<< a (head b))))
              (equal (head (cons a b)) a))
     :hints(("Goal" :in-theory (enable setp head emptyp
                                       setp-of-cons))))

   (defthm head-of-insert
     (equal (set::head (set::insert x y))
            (if (or (set::emptyp y)
                    (<< x (set::head y)))
                x
              (set::head y)))
     :hints(("Goal" :in-theory (enable set::insert set::head set::tail
                                       set::emptyp set::sfix set::setp))))))
                                       

(defsection keys-redef
  (local (defthm insert-is-cons-when-ordered
           (implies (or (set::emptyp y)
                        (<< x (set::head y)))
                    (equal (set::insert x y)
                           (cons x (set::sfix y))))
           :hints(("Goal" :in-theory (enable set::insert)))))
  
  (local
   (defthm head-of-omap-keys
     (equal (set::head (keys x))
            (mv-nth 0 (head x)))
     :hints(("Goal" :in-theory (e/d (keys) (head-ordered))
             :induct t)
            '(:use head-ordered))))
  
  (defthmd keys-redef
    (equal (keys x)
           (if (emptyp x)
               nil
             (mv-let (key val)
               (head x)
               (declare (ignore val))
               (cons key (keys (tail x))))))
    :hints(("Goal" ;; :in-theory (enable emptyp
                   ;;                    mfix
                   ;;                    tail
                   ;;                    head)
            :expand ((mapp x)
                     (keys x))
            :do-not-induct t))
    :rule-classes ((:definition :controller-alist ((keys t))))))

;; (local (defthm mv-nth-of-if
;;          (equal (mv-nth n (if x y z))
;;                 (if x (mv-nth n y) (mv-nth n z)))))

(define key-ord-values ((x mapp))
  (if (emptyp x)
      nil
    (mv-let (key val)
      (head x)
      (declare (ignore key))
      (cons val (key-ord-values (tail x)))))
  ///
  (defthm from-lists-of-omap-keys-values
    (equal (from-lists (keys x)
                             (key-ord-values x))
           (mfix x))
    :hints(("Goal" :induct (key-ord-values x)
            :expand ((:with keys-redef (keys x))
                     (key-ord-values x)
                     (:free (a b c d) (from-lists (cons a b) (cons c d)))))))

  (defthm key-ord-values-of-update
    (subsetp-equal (key-ord-values (update key val x))
                   (cons val (key-ord-values x)))
    :hints(("Goal" :in-theory (enable update)
            :expand ((:free (X y) (key-ord-values (cons x y)))
                     (:free (x y) (tail (cons x y))))))))

;; (defthm keys-of-from-lists-when-setp
;;   (implies (set::setp keys)
;;            (equal (keys (from-lists keys vals))
;;                   keys))
;;   :hints(("Goal" :in-theory (enable from-lists keys
