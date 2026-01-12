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

(include-book "iterative")

(defconst *haz1baserel-abstraction*
  '(relunion (relcompose (relidentity r)
                         (relcompose po&loc
                                     (relcompose (relidentity r)
                                                 (relcompose ca&ext (relidentity w)))))
             (relunion (relcompose (relidentity w)
                                   (relcompose rf&ext (relidentity r)))
                       (relcompose (relidentity (setunion r w))
                                   (relcompose ca&ext (relidentity w))))))

(defconst *haz2baserel-abstraction*
  '(relunion (relcompose (relidentity w)
                         (relcompose rf&ext
                                     (relcompose (relidentity r)
                                                 (relcompose po&loc (relidentity r)))))
             (relunion (relcompose (relidentity w)
                                   (relcompose rf&ext (relidentity r)))
                       (relcompose (relidentity (setunion r w))
                                   (relcompose ca&ext (relidentity w))))))


(defconst *haz1baserel-abstraction-condensed*
  '(relunion (relcompose po&loc ca&ext)
             (relunion rf&ext ca&ext)))

(defconst *haz2baserel-abstraction-condensed*
  '(relunion (relcompose rf&ext po&loc)
             (relunion rf&ext ca&ext)))

(defconst *haz1baserel-set*
  `(setimage (universe)
             (relintersect (relidentity (universe))
                           (relplus ,*haz1baserel-abstraction*))))

(defconst *haz2baserel-set*
  `(setimage (universe)
             (relintersect (relidentity (universe))
                           (relplus ,*haz2baserel-abstraction*))))

(defconst *rel-props*
  '((not (pred-nonempty (setimage (universe) (relcompose po&loc rf&ext))))
    (not (pred-nonempty (setimage (universe) (relcompose rf&ext rf&ext))))
    (not (pred-nonempty (setimage (universe) (relcompose ca&ext po&loc))))))

(defconst *assums-1*
  `((not (pred-nonempty (setintersect (universe) (setintersect r w))))
    (not (pred-nonempty ,*haz2baserel-set*))
    (pred-nonempty ,*haz1baserel-set*)))

(defconst *haz1baserel-set-condensed*
  `(setimage (universe)
             (relintersect (relidentity (universe))
                           (relplus ,*haz1baserel-abstraction-condensed*))))

(defconst *haz2baserel-set-condensed*
  `(setimage (universe)
             (relintersect (relidentity (universe))
                           (relplus ,*haz2baserel-abstraction-condensed*))))

(defconst *assums-1-condensed*
  (append `((not (pred-nonempty ,*haz2baserel-set-condensed*))
            (pred-nonempty ,*haz1baserel-set-condensed*))
          *rel-props*))
            
#|  

(iterative-rewrite-top 1 *assums-1*)

(iterative-rewrite-top
 1
 '((PRED-IN-REL |E0| |E1| PO&LOC)
   (PRED-NONEMPTY (SETINTERSECT (SINGLETON |E0|)
                                (SETIMAGE (SINGLETON |E1|) CA&EXT)))
   (not (pred-nonempty (setimage (universe) (relcompose ca&ext po&loc))))))

(trace$ (iterative-rewrite-and-intro
         :entry (list 'irao assums freevars eventvars)
         :exit (list 'irao value)))

(trace$ (apply-a-rewrite-to-assums :entry (list 'apply-a-rewrite)
                        :exit (list 'apply-a-rewrite (first values) (second values))))

(iterative-rewrite-top
 1
 '((PRED-IN-REL |E0| |E1| PO&LOC)
   (PRED-NONEMPTY (SETINTERSECT (SINGLETON |E0|)
                                (SETIMAGE (SINGLETON |E1|) CA&EXT)))
   (not (pred-nonempty (setimage (universe) (relcompose ca&ext po&loc))))))

|#

(defconst *assums-2*
  `((not (pred-nonempty ,*haz1baserel-set*))
    (pred-nonempty ,*haz2baserel-set*)
    (not (pred-nonempty (setintersect r w)))))

