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

(include-book "interp-types")
(include-book "tools/templates" :dir :system)
(local (include-book "std/lists/sets" :dir :System))

(local (std::add-default-post-define-hook :fix))


(define evt->loc ((x evt-p))
  :returns (loc acl2::maybe-natp :rule-classes :type-prescription)
  (b* (((evt x)))
    (evttype-case x.data
      :evt-r x.data.addr
      :evt-w x.data.addr
      :otherwise nil)))


(define evtlist-filter-type ((type evtkind-p)
                             (x evtlist-p))
  :returns (new-x evtlist-p)
  (if (atom x)
      nil
    (if (eq (evttype-kind (evt->data (car x))) (evtkind-fix type))
        (cons (evt-fix (car x))
              (evtlist-filter-type type (cdr x)))
      (evtlist-filter-type type (cdr x)))))

(define evtlist-filter-init-writes ((x evtlist-p))
  :returns (new-x evtlist-p)
  (if (atom x)
      nil
    (if (b* (((evt x1) (car x)))
          (evttype-case x1.data
            :evt-w x1.data.initp
            :otherwise nil))
        (cons (evt-fix (car x))
              (evtlist-filter-init-writes (cdr x)))
      (evtlist-filter-init-writes (cdr x)))))






(define empty-relation ()
  :returns (rel relation-p)
  nil)

(define id-relation ((x evtlist-p))
  :returns (rel relation-p)
  (b* ((x (evtlist-fix x)))
    (pairlis$ x x)))

(define cartesian1 ((x evt-p)
                               (y evtlist-p))
  :returns (rel relation-p)
  (if (atom y)
      nil
    (cons (cons (evt-fix x) (evt-fix (car y)))
          (cartesian1 x (cdr y))))
  ///
  (defretd member-of-<fn>
    (iff (member-equal pair rel)
         (and (consp pair)
              (Equal (car pair) (evt-fix x))
              (member-equal (cdr pair) (evtlist-fix y))))))

(define cartesian ((x evtlist-p)
                   (y evtlist-p))
  :returns (rel relation-p)
  (if (atom x)
      nil
    (append (cartesian1 (car x) y)
            (cartesian (cdr x) y)))
  ///
  (defretd member-of-<fn>
    (iff (member-equal pair rel)
         (and (consp pair)
              (member-equal (car pair) (evtlist-fix x))
              (member-equal (cdr pair) (evtlist-fix y))))
    :hints(("Goal" :in-theory (enable member-of-cartesian1)))))




(defmacro defrelation (name cond)
  (acl2::template-subst
   '(progn
      (define <name>1-product ((x evt-p) (y evtlist-p))
        :returns (rel relation-p)
        (if (atom y)
            nil
          (if (b* ((?y (car y)))
                <cond>)
              (cons (cons (evt-fix x)
                          (evt-fix (car y)))
                    (<name>1-product x (cdr y)))
            (<name>1-product x (cdr y))))
        ///
        (defretd member-of-<fn>
          (iff (member-equal pair rel)
               (and (consp pair)
                    (equal (car pair) (evt-fix x))
                    (member-equal (cdr pair) (evtlist-fix y))
                    (b* ((?x (car pair))
                         (?y (cdr pair)))
                      <cond>)))))

      (define <name>-product ((x evtlist-p) (y evtlist-p))
        :returns (rel relation-p)
        (if (atom x)
            nil
          (append (<name>1-product (car x) y)
                  (<name>-product (cdr x) y)))
        ///
        (defretd member-of-<fn>
          (iff (member-equal pair rel)
               (and (consp pair)
                    (member-equal (car pair) (evtlist-fix x))
                    (member-equal (cdr pair) (evtlist-fix y))
                    (b* ((?x (car pair))
                         (?y (cdr pair)))
                      <cond>)))
          :hints(("Goal" :in-theory (enable member-of-<name>1-product)))))

      (define <name>-relation ((x evtlist-p))
        :returns (rel relation-p)
        (<name>-product x x)
        ///
        (defret member-of-<fn>
          (iff (member-equal pair rel)
               (and (consp pair)
                    (member-equal (car pair) (evtlist-fix x))
                    (member-equal (cdr pair) (evtlist-fix x))
                    (b* ((?x (car pair))
                         (?y (cdr pair)))
                      <cond>)))
          :hints(("Goal" :in-theory (enable member-of-<name>-product))))))
   :str-alist `(("<NAME>" . ,(symbol-name name)))
   :atom-alist `((<cond> . ,cond))
   :pkg-sym 'cat-pkg))

(defrelation cartesian t)

(defrelation loc (equal (evt->loc x) (evt->loc y)))

(defrelation ext (not (equal (evt->procid x) (evt->procid y))))

(defrelation po (and (equal (evt->procid x) (evt->procid y))
                     (< (evt->po-index x) (evt->po-index y))))

(defrelation rf (b* (((evt x))
                     ((evt y)))
                  (evttype-case x.data
                         :evt-r (equal x.data.from y.uid)
                         :otherwise nil)))



;; For any pair (dst, dst2) in x, includes (src, dst2) in result.
(define compose1 ((src evt-p)
                  (dst evt-p)
                  (x relation-p))
  :returns (compose relation-p)
  (if (atom x)
      nil
    (if (and (mbt (consp (car x)))
             (equal (evt-fix dst) (evt-fix (caar x))))
        (cons (cons (evt-fix src) (evt-fix (cdar x)))
              (compose1 src dst (cdr x)))
      (compose1 src dst (cdr x))))
  ///
  (defretd member-of-<fn>
    (iff (member-equal pair compose)
         (and (consp pair)
              (equal (car pair) (evt-fix src))
              (member-equal (cons (evt-fix dst) (cdr pair))
                            (relation-fix x))))))

(define compose ((x relation-p)
                 (y relation-p))
  :returns (compose relation-p)
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (append (compose1 (caar x) (cdar x) y)
                (compose (cdr x) y))
      (compose (cdr x) y)))
  ///
  (defretd member-of-compose-suff
    (implies (and (consp pair)
                  (member-equal (cons (car pair) mid) (relation-fix x))
                  (member-equal (cons mid (cdr pair)) (relation-fix y)))
             (member-equal pair compose))
    :hints(("Goal" :in-theory (enable member-of-compose1)))))

(define compose-midpoint ((src evt-p)
                          (dst evt-p)
                          (x relation-p)
                          (y relation-p))
  :returns (mid (iff (evt-p mid) mid))
  ;; Witness for compose membership. If (src . dst) are in the composition of x
  ;; and y, then (compose-midpoint src dst x y) produces mid such that (src
  ;; . mid) is in x and (mid . dst) is in y.
  (if (atom x)
      nil
    (if (and (mbt (consp (car x)))
             (equal (evt-fix src) (evt-fix (caar x)))
             (member-equal (cons (evt-fix (cdar x)) (evt-fix dst))
                           (relation-fix y)))
        (evt-fix (cdar x))
      (compose-midpoint src dst (cdr x) y)))
  ///
  (local (defthm member-cons-relation
           (implies (And (relation-p y)
                         (not (and (evt-p dst)
                                   (evt-p src))))
                    (not (member-equal (cons src dst) y)))))

  (local (defthm member-relation-not-consp
           (implies (And (relation-p y)
                         (not (consp pair)))
                    (not (member-equal pair y)))))
  
  (defret compose-midpoint-witnesses
    (implies (and (member-equal (cons src mid1) (relation-fix x))
                  (member-equal (cons mid1 dst) (relation-fix y)))
             (and (member-equal (cons src mid) (relation-fix x))
                  (member-equal (cons mid dst) (relation-fix y))))
    :hints(("Goal" :in-theory (enable relation-fix)
            :cases ((and (evt-p src) (evt-p mid1) (evt-p dst)))))
    :otf-flg t)

  (defretd member-of-compose-necc
    :pre-bind ((src (car pair))
               (dst (cdr pair)))
    (implies (not (and (member-equal (cons (car pair) mid) (relation-fix x))
                       (member-equal (cons mid (cdr pair)) (relation-fix y))))
             (not (member-equal pair (compose x y))))
    :hints(("Goal" :in-theory (enable compose
                                      member-of-compose-suff
                                      member-of-compose1)
            :cases ((and (evt-p (car pair)) (evt-p (cdr pair))))))
    :otf-flg t)
                         
  (defretd member-of-compose
    :pre-bind ((src (car pair))
               (dst (cdr pair)))
    (iff (member-equal pair (compose x y))
         (and (consp pair)
              (member-equal (cons (car pair) mid) (relation-fix x))
              (member-equal (cons mid (cdr pair)) (relation-fix y))))
    :hints(("Goal" :in-theory (enable member-of-compose-necc
                                      member-of-compose-suff)))))


(define domain ((x relation-p))
  :returns (dom evtlist-p)
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (cons (evt-fix (caar x))
              (domain (cdr x)))
      (domain (cdr x))))
  ///
  (defretd member-of-domain-suff
    (implies (member-equal (cons src dst) (relation-fix x))
             (member-equal src (domain x)))))

(define domain-witness ((src evt-p) (x relation-p))
  :returns (dst (iff (evt-p dst) dst))
  (if (atom x)
      nil
    (if (and (mbt (consp (car x)))
             (equal (evt-fix src)
                    (evt-fix (caar x))))
        (evt-fix (cdar x))
      (domain-witness src (cdr x))))
  ///

  (local (defthm equal-of-evt-fix
           (equal (equal x (evt-fix x))
                  (evt-p x))))
  
  (local (defthm member-cons-relation
           (implies (And (relation-p y)
                         (not (and (evt-p dst)
                                   (evt-p src))))
                    (not (member-equal (cons src dst) y)))))

  (defret domain-witness-witnesses
    (implies (member-equal (cons src dst1) (relation-fix x))
             (member-equal (cons src dst) (relation-fix x))))
  
  (defretd member-of-domain-necc
    (implies (not (member-equal (cons src dst) (relation-fix x)))
             (not (member-equal src (domain x))))
    :hints(("Goal" :in-theory (enable domain))))

  (defretd member-of-domain
    (iff (member-equal src (domain x))
         (member-equal (cons src dst) (relation-fix x)))
    :hints(("Goal" :in-theory (enable member-of-domain-necc
                                      member-of-domain-suff)))))



(define range ((x relation-p))
  :returns (dom evtlist-p)
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (cons (evt-fix (cdar x))
              (range (cdr x)))
      (range (cdr x))))
  ///
  (defretd member-of-range-suff
    (implies (member-equal (cons src dst) (relation-fix x))
             (member-equal dst (range x)))))

(define range-witness ((dst evt-p) (x relation-p))
  :returns (src (iff (evt-p src) src))
  (if (atom x)
      nil
    (if (and (mbt (consp (car x)))
             (equal (evt-fix dst)
                    (evt-fix (cdar x))))
        (evt-fix (caar x))
      (range-witness dst (cdr x))))
  ///

  (local (defthm equal-of-evt-fix
           (equal (equal x (evt-fix x))
                  (evt-p x))))
  
  (local (defthm member-cons-relation
           (implies (And (relation-p y)
                         (not (and (evt-p dst)
                                   (evt-p src))))
                    (not (member-equal (cons src dst) y)))))

  (defret range-witness-witnesses
    (implies (member-equal (cons src1 dst) (relation-fix x))
             (member-equal (cons src dst) (relation-fix x))))
  
  (defretd member-of-range-necc
    (implies (not (member-equal (cons src dst) (relation-fix x)))
             (not (member-equal dst (range x))))
    :hints(("Goal" :in-theory (enable range))))

  (defretd member-of-range
    (iff (member-equal dst (range x))
         (member-equal (cons src dst) (relation-fix x)))
    :hints(("Goal" :in-theory (enable member-of-range-necc
                                      member-of-range-suff)))))


    
