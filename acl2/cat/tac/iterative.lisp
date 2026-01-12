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
(include-book "rewrite-assums")
(include-book "intro-rewriter")
(include-book "std/strings/decimal" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (std::add-default-post-define-hook :fix))


(local (defthm pseudo-var-p-by-first-character
         (implies (and (not (equal (char str 0) #\N))
                       (stringp str)
                       (symbolp pkg)) 
                  (pseudo-var-p (intern-in-package-of-symbol str pkg)))
         :hints (("goal" :use ((:instance symbol-name-intern-in-package-of-symbol
                                (s str) (any-symbol pkg)))
                  :in-theory (e/d (pseudo-var-p)
                                  (symbol-name-intern-in-package-of-symbol))))))

(define anonymous-var ((n natp))
  :returns (name pseudo-var-p)
  (intern-in-package-of-symbol
   (concatenate 'string "_E" (str::natstr n)) 'tac-pkg)
  ///
  (local (defthm equal-of-intern-in-package-of-symbol
           (implies (and (stringp str1) (stringp str2)
                         (symbolp pkg))
                    (equal (equal (intern-in-package-of-symbol str1 pkg)
                                  (intern-in-package-of-symbol str2 pkg))
                           (equal str1 str2)))
           :hints (("goal" ;; :use ((:instance intern-in-package-of-symbol-symbol-name
                    ;;               (x (intern-in-package-of-symbol str1 pkg))
                    ;;               (y pkg))
                    ;;              (:instance intern-in-package-of-symbol-symbol-name
                    ;;               (x (intern-in-package-of-symbol str2 pkg))
                    ;;               (y pkg)))
                    ;; :in-theory (disable intern-in-package-of-symbol-symbol-name)
                    :use ((:instance symbol-name-intern-in-package-of-symbol
                           (s str1) (any-symbol pkg))
                          (:instance symbol-name-intern-in-package-of-symbol
                           (s str2) (any-symbol pkg)))
                    :in-theory (disable symbol-name-intern-in-package-of-symbol)))))
  
  (defthm anonymous-var-unique
    (iff (equal (anonymous-var n) (anonymous-var m))
         (acl2::nat-equiv n m))))

(define anonymous-var-p ((x pseudo-var-p))
  (let ((x (pseudo-var-fix x)))
    (and (<= 2 (length (symbol-name x)))
         (equal (char (symbol-name x) 0) #\_)
         (equal (char (symbol-name x) 1) #\E)))
  ///
  (defthm anonymous-var-p-of-anonymous-var
    (anonymous-var-p (anonymous-var n))
    :hints(("Goal" :in-theory (enable anonymous-var)))))

;; (define anonymous-vars-p ((x cmr::pseudo-var-list-p))
;;   (if (atom x)
;;       t
;;     (and (anonymous-var-p (car x))
;;          (anonymous-vars-p (cdr x)))))

(define has-anonymous-var ((x cmr::pseudo-var-list-p))
  (if (atom x)
      nil
    (or (anonymous-var-p (car x))
        (has-anonymous-var (cdr x)))))


(define anonymous-vars-aux ((n natp) (max natp))
  :measure (nfix (- (nfix max) (nfix n)))
  :guard (<= n max)
  :returns (vars cmr::pseudo-var-list-p)
  (if (mbe :logic (zp (- (nfix max) (nfix n)))
           :exec (eql n max))
      nil
    (cons (anonymous-var n)
          (anonymous-vars-aux (1+ (lnfix n)) max)))
  ///
  ;; (defret anonymous-vars-p-of-<fn>
  ;;   (anonymous-vars-p vars)
  ;;   :hints(("Goal" :in-theory (enable anonymous-vars-p))))

  (local (defthm anonymous-var-not-member-when-no-anonymous
           (implies (not (has-anonymous-var x))
                    (not (member-equal (anonymous-var n) x)))
           :hints(("Goal" :in-theory (enable has-anonymous-var)))))
  
  (defret <fn>-no-intersection-when-no-anonymous-vars
    (implies (not (has-anonymous-var x))
             (not (intersectp-equal vars x)))
    :hints(("Goal" :in-theory (enable intersectp-equal))))

  (defret len-of-<fn>
    (equal (len vars) (nfix (- (nfix max) (nfix n)))))

  (defret member-lesser-of-<fn>
    (implies (< (nfix m) (nfix n))
             (not (member-equal (anonymous-var m) vars))))

  (defret member-non-anonymous-of-<fn>
    (implies (not (anonymous-var-p x))
             (not (member-equal x vars))))

  (defret no-duplicatesp-of-<fn>
    (no-duplicatesp-equal vars)))

(define anonymous-vars ((n natp))
  :returns (vars cmr::pseudo-var-list-p)
  (anonymous-vars-aux 0 n)
  ///
  (defret <fn>-no-intersection-when-no-anonymous-vars
    (implies (not (has-anonymous-var x))
             (not (intersectp-equal vars x))))

  (defret len-of-<fn>
    (equal (len vars) (nfix n)))

  (defret member-non-anonymous-of-<fn>
    (implies (not (anonymous-var-p x))
             (not (member-equal x vars))))
  
  (defret no-duplicatesp-of-<fn>
    (no-duplicatesp-equal vars)))
  


(local (defthm tac-ev-disj-of-conjunctions-of-append
         (iff (tac-ev-disj-of-conjunctions (append x y) env)
              (or (tac-ev-disj-of-conjunctions x env)
                  (tac-ev-disj-of-conjunctions y env)))
         :hints(("Goal" :in-theory (enable tac-ev-disj-of-conjunctions)))))

(local (defthm intersectp-equal-of-append-2
         (iff (intersectp-equal a (append b c))
              (or (intersectp-equal a b)
                  (intersectp-equal a c)))
         :hints(("Goal" :in-theory (enable intersectp-equal)))))

(local (defret intersectp-vars-of-tac-fvi-rewrite-assums
         (implies (and (not (intersectp-equal vars (cmr::termlist-vars assums)))
                       (not (member-equal (pseudo-var-fix freevar) vars)))
                  (not (intersectp-equal vars (cmr::termlist-vars new-assums))))
         :hints(("Goal" :in-theory (enable member-equal intersectp-equal)))
         :fn tac-fvi-rewrite-assums))

(local (defret intersectp-vars-of-rewrite-assums
         (implies (and (not (intersectp-equal vars (cmr::termlist-vars assums)))
                       (not (intersectp-equal vars (cmr::pseudo-var-list-fix eventvars))))
                  (not (intersectp-equal vars (tac-caselist-vars results))))
         :hints(("Goal" :in-theory (enable intersectp-equal)))
         :fn rewrite-assums))


(local (defthm intersectp-equal-of-cons
         (iff (intersectp-equal a (cons b c))
              (or (member-equal b a)
                  (intersectp-equal a c)))
         :hints(("Goal" :in-theory (enable intersectp-equal)))))

(defines iterative-rewrite-and-intro
  (define iterative-rewrite-and-intro ((assums pseudo-term-listp)
                                       (substmap used-subst-map-p)
                                       (freevars cmr::pseudo-var-list-p)
                                       (eventvars cmr::pseudo-var-list-p))
    :measure (acl2::nat-list-measure (list (len freevars) 0))
    :returns (results tac-caselist-p)
    :verify-guards nil
    (b* ((cases (rewrite-assums 1000 assums substmap eventvars))
         ((when (atom freevars)) cases))
      (iterative-rewrite-and-intro-cases cases freevars eventvars)))

  (define iterative-rewrite-and-intro-cases ((cases tac-caselist-p)
                                             (freevars cmr::pseudo-var-list-p)
                                             (eventvars cmr::pseudo-var-list-p))
    :guard (consp freevars)
    :measure (acl2::nat-list-measure (list (1- (len freevars)) (len cases)))
    :returns (results tac-caselist-p)
    (b* (((when (atom cases)) nil)
         ((tac-case case1) (car cases))
         ((mv ok new-case) (tac-fvi-rewrite-assums case1.assums (car freevars)))
         ((when ok)
          (append (iterative-rewrite-and-intro new-case case1.substmap (cdr freevars)
                                               (cons (pseudo-var-fix (car freevars))
                                                     eventvars))
                  (iterative-rewrite-and-intro-cases (cdr cases) freevars eventvars))))
      (cons (tac-case-fix (car cases))
            (iterative-rewrite-and-intro-cases (cdr cases) freevars eventvars))))
  ///
  (verify-guards iterative-rewrite-and-intro)

  (local (defthm termlistlist-vars-of-append
           (acl2::set-equiv (termlistlist-vars (append a b))
                            (append (termlistlist-vars a)
                                    (termlistlist-vars b)))
           :hints(("Goal" :in-theory (enable termlistlist-vars)))))
  
  (std::defret-mutual vars-of-<fn>
    (defret vars-of-<fn>
      (implies (and (not (member-equal v (cmr::termlist-vars assums)))
                    (not (member-equal v (cmr::pseudo-var-list-fix freevars)))
                    (not (member-equal v (cmr::pseudo-var-list-fix eventvars))))
               (not (member-equal v (tac-caselist-vars results))))
      :fn iterative-rewrite-and-intro)
    (defret vars-of-<fn>
      (implies (and (not (member-equal v (tac-caselist-vars cases)))
                    (not (member-equal v (cmr::pseudo-var-list-fix freevars)))
                    (not (member-equal v (cmr::pseudo-var-list-fix eventvars)))
                    (consp freevars))
               (not (member-equal v (tac-caselist-vars results))))
      :hints ('(:expand (<call>
                         (tac-caselist-vars cases)
                         (:free (x y) (tac-caselist-vars (cons x y)))
                         (cmr::pseudo-var-list-fix freevars))))
      :fn iterative-rewrite-and-intro-cases))
  
  (std::defret-mutual type-of-<fn>
    (defret type-of-<fn>
      (implies (and (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                    (not (member-equal 'tac-w (cmr::pseudo-var-list-fix freevars)))
                    (not (member-equal 'tac-w (cmr::pseudo-var-list-fix eventvars)))
                    (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                    (event-vars-p freevars ctx)
                    (event-vars-p eventvars ctx))
               (tac-caselist-typed results ctx))
      :hints ('(:expand (<call>)))
      :fn iterative-rewrite-and-intro)
    (defret type-of-<fn>
      (implies (and (not (member-equal 'tac-w (tac-caselist-vars cases)))
                    (not (member-equal 'tac-w (cmr::pseudo-var-list-fix freevars)))
                    (not (member-equal 'tac-w (cmr::pseudo-var-list-fix eventvars)))
                    (tac-caselist-typed cases ctx)
                    (event-vars-p freevars ctx)
                    (event-vars-p eventvars ctx)
                    (consp freevars))
               (tac-caselist-typed results ctx))
      :hints ('(:expand (<call>
                         (event-vars-p freevars ctx)
                         (:Free (a b) (event-vars-p (cons a b) ctx))
                         (tac-caselist-vars cases)
                         (tac-caselist-typed cases ctx)
                         (:free (a b) (tac-caselist-typed (cons a b) ctx)))))
      :fn iterative-rewrite-and-intro-cases))

  (std::defret-mutual eval-implies-orig-of-<fn>
    (defret eval-implies-orig-of-<fn>
      (implies (and (tac-typed-env-p env ctx)
                    (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                    (not (member-equal 'tac-w (cmr::pseudo-var-list-fix freevars)))
                    (not (member-equal 'tac-w (cmr::pseudo-var-list-fix eventvars)))
                    (not (intersectp-equal (cmr::pseudo-var-list-fix freevars)
                                           (cmr::termlist-vars assums)))
                    (not (intersectp-equal (cmr::pseudo-var-list-fix freevars)
                                           (cmr::pseudo-var-list-fix eventvars)))
                    (no-duplicatesp-equal (cmr::pseudo-var-list-fix freevars))
                    (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                    (event-vars-p freevars ctx)
                    (event-vars-p eventvars ctx))
               (implies (tac-ev-caselist results env)
                        (tac-ev-cube assums env)))
      :hints ('(:expand (<call>)))
      :fn iterative-rewrite-and-intro
      :rule-classes nil)
    (defret eval-implies-orig-of-<fn>
      (implies (and (tac-typed-env-p env ctx)
                    (not (member-equal 'tac-w (tac-caselist-vars cases)))
                    (not (member-equal 'tac-w (cmr::pseudo-var-list-fix freevars)))
                    (not (member-equal 'tac-w (cmr::pseudo-var-list-fix eventvars)))
                    (not (intersectp-equal (cmr::pseudo-var-list-fix freevars)
                                           (tac-caselist-vars cases)))
                    (not (intersectp-equal (cmr::pseudo-var-list-fix freevars)
                                           (cmr::pseudo-var-list-fix eventvars)))
                    (no-duplicatesp-equal (cmr::pseudo-var-list-fix freevars))
                    (tac-caselist-typed cases ctx)
                    (consp freevars)
                    (event-vars-p freevars ctx)
                    (event-vars-p eventvars ctx))
               (implies (tac-ev-caselist results env)
                        (tac-ev-caselist cases env)))
      :hints ('(:expand (<call>
                         ;; (tac-ev-cube nil env)
                         (tac-ev-caselist nil env)
                         (event-vars-p freevars ctx)
                         (:Free (a b) (event-vars-p (cons a b) ctx))
                         (tac-ev-caselist cases env)
                         (:free (a b) (tac-ev-caselist (cons a b) env))
                         (cmr::pseudo-var-list-fix freevars)
                         (:free (a b c) (intersectp-equal (cons a b) c))
                         (tac-caselist-vars cases)
                         (tac-caselist-typed cases ctx)
                         (:free (a b) (tac-caselist-typed (cons a b) ctx))))
              (and stable-under-simplificationp
                   '(:use ((:instance eval-implies-orig-of-tac-fvi-rewrite-assums
                            (assums (tac-case->assums (car cases)))
                            (freevar (car freevars)))))))
      :fn iterative-rewrite-and-intro-cases
      :rule-classes nil))

  (fty::deffixequiv-mutual iterative-rewrite-and-intro))


(local
 (defthm assoc-equal-is-hons-assoc-equal
   (implies k
            (equal (assoc-equal k x)
                   (hons-assoc-equal k x)))))

(local (defthm pseudo-var-list-p-keys-of-ctx
         (implies (type-ctx-p x)
                  (cmr::pseudo-var-list-p (acl2::alist-keys x)))
         :hints(("Goal" :in-theory (enable acl2::alist-keys)))))

(local (defthm tac-typed-env-p-aux-of-cons
         (implies (tac-typed-env-p-aux keys env ctx)
                  (iff (tac-typed-env-p-aux keys (cons (cons key val) env) ctx)
                       (or (not (member-equal (pseudo-var-fix key)
                                              (cmr::pseudo-var-list-fix keys)))
                           (not (pseudo-var-p key))
                           (tac-typed-val-p val (cdr (hons-assoc-equal (pseudo-var-fix key)
                                                                       (type-ctx-fix ctx)))))))
         :hints(("Goal" :in-theory (enable tac-typed-env-p-aux
                                           cmr::pseudo-var-list-fix)))))

(local (defthmd member-keys-is-hons-assoc-equal
         (iff (member-equal k (acl2::alist-keys x))
              (hons-assoc-equal k x))
         :hints(("Goal" :in-theory (enable acl2::alist-keys)))))

(local (defthm tac-typed-env-p-of-cons
         (implies (tac-typed-env-p env ctx)
                  (iff (tac-typed-env-p (cons (cons key val) env) ctx)
                       (or (not (hons-assoc-equal (pseudo-var-fix key) (type-ctx-fix ctx)))
                           (not (pseudo-var-p key))
                           (tac-typed-val-p val (cdr (hons-assoc-equal (pseudo-var-fix key)
                                                                       (type-ctx-fix ctx)))))))
         :hints(("Goal" :in-theory (enable tac-typed-env-p
                                           member-keys-is-hons-assoc-equal)))))

(defines iterative-rewrite-and-intro-env
  (define iterative-rewrite-and-intro-env ((assums pseudo-term-listp)
                                           (substmap used-subst-map-p)
                                           (freevars cmr::pseudo-var-list-p)
                                           (eventvars cmr::pseudo-var-list-p)
                                           (env))
    :measure (acl2::nat-list-measure (list (len freevars) 0))
    :returns (new-env)
    :verify-guards nil
    (b* (((when (atom freevars)) env)
         (cases (rewrite-assums 1000 assums substmap eventvars)))
      (iterative-rewrite-and-intro-cases-env cases freevars eventvars env)))

  (define iterative-rewrite-and-intro-cases-env ((cases tac-caselist-p)
                                                 (freevars cmr::pseudo-var-list-p)
                                                 (eventvars cmr::pseudo-var-list-p)
                                                 (env))
    :guard (consp freevars)
    :measure (acl2::nat-list-measure (list (1- (len freevars)) (len cases)))
    :returns (new-env)
    (b* (((when (atom cases)) env) ;; not reachable
         ((tac-case case1) (car cases))
         ((unless (tac-ev-cube case1.assums  env))
          (iterative-rewrite-and-intro-cases-env (cdr cases) freevars eventvars env))
         ((mv ok new-case) (tac-fvi-rewrite-assums case1.assums (car freevars)))
         ((when ok)
          (iterative-rewrite-and-intro-env
           new-case case1.substmap (cdr freevars)
           (cons (pseudo-var-fix (car freevars)) eventvars)
           (cons (cons (pseudo-var-fix (car freevars))
                       (tac-ev (tac-fvi-rewrite-assums-witness case1.assums (car freevars))
                               env))
                 env))))
      env))
  ///
  
  (std::defret-mutual type-of-<fn>
    (defret type-of-<fn>
      (implies (and (tac-typed-env-p env ctx)
                    (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                    (not (member-equal 'tac-w (cmr::pseudo-var-list-fix freevars)))
                    (not (member-equal 'tac-w (cmr::pseudo-var-list-fix eventvars)))
                    (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                    (event-vars-p freevars ctx)
                    (event-vars-p eventvars ctx))
               (tac-typed-env-p new-env ctx))
      :hints ('(:expand (<call>)))
      :fn iterative-rewrite-and-intro-env)
    (defret type-of-<fn>
      (implies (and (tac-typed-env-p env ctx)
                    (not (member-equal 'tac-w (tac-caselist-vars cases)))
                    (not (member-equal 'tac-w (cmr::pseudo-var-list-fix freevars)))
                    (not (member-equal 'tac-w (cmr::pseudo-var-list-fix eventvars)))
                    (tac-caselist-typed cases ctx)
                    (event-vars-p freevars ctx)
                    (event-vars-p eventvars ctx)
                    (consp freevars))
               (tac-typed-env-p new-env ctx))
      :hints ('(:expand (<call>
                         (event-vars-p freevars ctx)
                         (:free (a b) (event-vars-p (cons a b) ctx))
                         (tac-caselist-vars cases)
                         (tac-caselist-typed cases ctx)
                         (:free (a b) (tac-caselist-typed (cons a b) ctx)))))
      :fn iterative-rewrite-and-intro-cases-env))
  
  (std::defret-mutual <fn>-correct
    (defret <fn>-correct
      (b* ((results (iterative-rewrite-and-intro assums substmap freevars eventvars)))
        (implies (and (tac-typed-env-p env ctx)
                      (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                      (not (member-equal 'tac-w (cmr::pseudo-var-list-fix freevars)))
                      (not (member-equal 'tac-w (cmr::pseudo-var-list-fix eventvars)))
                      (not (intersectp-equal (cmr::pseudo-var-list-fix freevars)
                                             (cmr::termlist-vars assums)))
                      (not (intersectp-equal (cmr::pseudo-var-list-fix freevars)
                                             (cmr::pseudo-var-list-fix eventvars)))
                      (no-duplicatesp-equal (cmr::pseudo-var-list-fix freevars))
                      (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                      (event-vars-p freevars ctx)
                      (event-vars-p eventvars ctx))
                 (implies (tac-ev-cube assums env)
                          (tac-ev-caselist results new-env))))
      :hints ('(:expand (<call>
                         (iterative-rewrite-and-intro assums substmap freevars eventvars))))
      :fn iterative-rewrite-and-intro-env
      :rule-classes nil)
    (defret <fn>-correct
      (b* ((results (iterative-rewrite-and-intro-cases cases freevars eventvars)))
        (implies (and (tac-typed-env-p env ctx)
                      (not (member-equal 'tac-w (tac-caselist-vars cases)))
                      (not (member-equal 'tac-w (cmr::pseudo-var-list-fix freevars)))
                      (not (member-equal 'tac-w (cmr::pseudo-var-list-fix eventvars)))
                      (not (intersectp-equal (cmr::pseudo-var-list-fix freevars)
                                             (tac-caselist-vars cases)))
                      (not (intersectp-equal (cmr::pseudo-var-list-fix freevars)
                                             (cmr::pseudo-var-list-fix eventvars)))
                      (no-duplicatesp-equal (cmr::pseudo-var-list-fix freevars))
                      (tac-caselist-typed cases ctx)
                      (consp freevars)
                      (event-vars-p freevars ctx)
                      (event-vars-p eventvars ctx))
                 (implies (tac-ev-caselist cases env)
                          (tac-ev-caselist results new-env))))
      :hints ('(:expand (<call>
                         (iterative-rewrite-and-intro-cases cases freevars eventvars)
                         ;; (tac-ev-cube nil env)
                         (tac-ev-caselist nil env)
                         (event-vars-p freevars ctx)
                         (:free (a b) (event-vars-p (cons a b) ctx))
                         (tac-ev-caselist cases env)
                         (:free (a b env) (tac-ev-caselist (cons a b) env))
                         (cmr::pseudo-var-list-fix freevars)
                         (:free (a b c) (intersectp-equal (cons a b) c))
                         (tac-caselist-vars cases)
                         (tac-caselist-typed cases ctx)
                         (:free (a b) (tac-caselist-typed (cons a b) ctx)))
                :do-not-induct t)
              (and stable-under-simplificationp
                   '(:use ((:instance tac-fvi-rewrite-assums-correct
                            (assums (tac-case->assums (car cases)))
                            (freevar (car freevars)))))))
      :fn iterative-rewrite-and-intro-cases-env
      :rule-classes nil))

  (fty::deffixequiv-mutual iterative-rewrite-and-intro-env))

(defun-sk tac-cube-satisfiable (x ctx)
  (exists env
          (and (tac-typed-env-p env ctx)
               (tac-ev-cube x env))))

(in-theory (disable tac-cube-satisfiable))

(defthm tac-cube-satisfiable-suff2
  (implies (and (tac-ev-cube x env)
                (tac-typed-env-p env ctx))
           (tac-cube-satisfiable x ctx)))

(define tac-caselist-satisfiable (x ctx)
  :verify-guards nil
  (if (atom x)
      nil
    (or (tac-cube-satisfiable (tac-case->assums (car x)) ctx)
        (tac-caselist-satisfiable (cdr x) ctx)))
  ///
  (defthm tac-caselist-satisfiable-suff
    (implies (and (tac-ev-caselist x env)
                  (tac-typed-env-p env ctx))
             (tac-caselist-satisfiable x ctx))
    :hints(("Goal" :in-theory (enable tac-ev-caselist)))))

(define tac-caselist-satisfiable-witness (x ctx)
  :verify-guards nil
  (if (atom x)
      nil
    (if (tac-cube-satisfiable (tac-case->assums (car x)) ctx)
        (tac-cube-satisfiable-witness (tac-case->assums (car x)) ctx)
      (tac-caselist-satisfiable-witness (cdr x) ctx)))
  ///
  (defthmd tac-caselist-satisfiable-by-witness
    (equal (tac-caselist-satisfiable x ctx)
           (and (tac-typed-env-p (tac-caselist-satisfiable-witness x ctx) ctx)
                (tac-ev-caselist x (tac-caselist-satisfiable-witness x ctx))))
    :hints(("Goal" :in-theory (enable tac-caselist-satisfiable
                                      tac-ev-caselist)
            :induct (tac-caselist-satisfiable x ctx)
            :expand ((tac-caselist-satisfiable x ctx)
                     (tac-caselist-satisfiable-witness x ctx)
                     (:free (env) (tac-ev-caselist x env))))
           (and stable-under-simplificationp
                '(:in-theory (enable tac-cube-satisfiable))))
    :rule-classes :definition))


(defret <fn>-equisatisfiable
  (implies (and (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                (not (member-equal 'tac-w (cmr::pseudo-var-list-fix freevars)))
                (not (member-equal 'tac-w (cmr::pseudo-var-list-fix eventvars)))
                (not (intersectp-equal (cmr::pseudo-var-list-fix freevars)
                                       (cmr::termlist-vars assums)))
                (not (intersectp-equal (cmr::pseudo-var-list-fix freevars)
                                       (cmr::pseudo-var-list-fix eventvars)))
                (no-duplicatesp-equal (cmr::pseudo-var-list-fix freevars))
                (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                (event-vars-p freevars ctx)
                (event-vars-p eventvars ctx))
           (iff (tac-caselist-satisfiable results ctx)
                (tac-cube-satisfiable assums ctx)))
  :hints ((acl2::use-termhint
           (b* ((results (iterative-rewrite-and-intro assums substmap freevars eventvars)))
             (if (tac-caselist-satisfiable results ctx)
                 `(:expand ((:with tac-caselist-satisfiable-by-witness
                             (tac-caselist-satisfiable ,(acl2::hq results) ctx)))
                   :use ((:instance eval-implies-orig-of-iterative-rewrite-and-intro
                          (env (tac-caselist-satisfiable-witness ,(acl2::hq results) ctx)))))
               `(:expand ((tac-cube-satisfiable assums ctx))
                 :use ((:instance iterative-rewrite-and-intro-env-correct
                        (env (tac-cube-satisfiable-witness assums ctx)))))))))
                 ;; :use ((:instance tac-caselist-satisfiable-suff
  :fn iterative-rewrite-and-intro)

(define add-event-ctx-bindings ((vars cmr::pseudo-var-list-p)
                        (ctx type-ctx-p))
  :returns (new-ctx type-ctx-p)
  (if (atom vars)
      (type-ctx-fix ctx)
    (cons (cons (pseudo-var-fix (car vars)) :event)
          (add-event-ctx-bindings (cdr vars) ctx)))
  ///
  (defret lookup-of-<fn>
    (equal (hons-assoc-equal v new-ctx)
           (if (member-equal v (cmr::pseudo-var-list-fix vars))
               (cons v :event)
             (hons-assoc-equal v (type-ctx-fix ctx)))))
  
  (defret event-vars-p-of-<fn>
    (event-vars-p vars new-ctx)
    :hints(("Goal" :in-theory (enable event-vars-p))))

  (defret tac-term-type-of-<fn>
    (implies (not (intersectp-equal (cmr::pseudo-var-list-fix vars)
                                    (cmr::term-vars x)))
             (equal (tac-term-type x new-ctx)
                    (tac-term-type x ctx)))
    :hints(("Goal" :in-theory (enable intersectp-equal
                                      cmr::pseudo-var-list-fix))))

  (defret tac-termlist-types-of-<fn>
    (implies (not (intersectp-equal (cmr::pseudo-var-list-fix vars)
                                    (cmr::termlist-vars x)))
             (equal (tac-termlist-types x new-ctx)
                    (tac-termlist-types x ctx)))
    :hints(("Goal" :in-theory (enable intersectp-equal
                                      cmr::pseudo-var-list-fix))))

  (defret alist-keys-of-<fn>
    (equal (acl2::alist-keys new-ctx)
           (append (cmr::pseudo-var-list-fix vars)
                   (acl2::alist-keys (type-ctx-fix ctx))))
    :hints(("Goal" :in-theory (enable acl2::alist-keys)))))



(local (defthm tac-typed-env-p-aux-of-append
         (iff (tac-typed-env-p-aux (append a b) env ctx)
              (and (tac-typed-env-p-aux a env ctx)
                   (tac-typed-env-p-aux b env ctx)))
         :hints(("Goal" :in-theory (enable tac-typed-env-p-aux)))))

(define add-event-env-bindings ((vars cmr::pseudo-var-list-p)
                                env)
  :returns (new-env)
  (if (atom vars)
      env
    (cons (cons (pseudo-var-fix (car vars)) (some-event))
          (add-event-env-bindings (cdr vars) env)))
  ///
  (defret lookup-of-<fn>
    (equal (hons-assoc-equal v new-env)
           (if (member-equal v (cmr::pseudo-var-list-fix vars))
               (cons v (some-event))
             (hons-assoc-equal v env))))

  (defret tac-ev-of-<fn>
    (implies (not (intersectp-equal (cmr::pseudo-var-list-fix vars)
                                    (cmr::term-vars x)))
             (equal (tac-ev x new-env)
                    (tac-ev x env)))
    :hints(("Goal" :in-theory (enable intersectp-equal
                                      cmr::pseudo-var-list-fix))))

  (defret tac-ev-cube-of-<fn>
    (implies (not (intersectp-equal (cmr::pseudo-var-list-fix vars)
                                    (cmr::termlist-vars x)))
             (equal (tac-ev-cube x new-env)
                    (tac-ev-cube x env)))
    :hints(("Goal" :in-theory (enable intersectp-equal
                                      cmr::pseudo-var-list-fix))))

  (local (defret tac-typed-env-p-aux-of-<fn>
           (implies (tac-typed-env-p-aux keys env ctx)
                    (tac-typed-env-p-aux keys new-env
                                         (add-event-ctx-bindings vars ctx)))
           :hints(("Goal" :in-theory (e/d (tac-typed-env-p-aux
                                           tac-typed-val-p)
                                          (<fn>))))))

  (local (defret tac-typed-env-p-aux-of-<fn>-2
           (tac-typed-env-p-aux vars new-env
                                (add-event-ctx-bindings vars ctx))
           :hints(("Goal" :in-theory (e/d (tac-typed-env-p-aux
                                           add-event-ctx-bindings
                                           tac-typed-val-p))))))

  
  (defret tac-typed-env-p-of-<fn>
    (implies (tac-typed-env-p env ctx)
             (tac-typed-env-p new-env
                              (add-event-ctx-bindings vars ctx)))
    :hints(("Goal" :in-theory (e/d (tac-typed-env-p)
                                   (<fn>))))))

(define tac-typed-val-default ((type tac-type-p))
  :returns (val (tac-typed-val-p val type)
                :hints(("Goal" :in-theory (enable tac-typed-val-p))))
  (case (tac-type-fix type)
    (:event (some-event))
    (:set nil)
    (:count 0)
    (:rel   nil)
    (:pred nil)
    (t nil)))

(define add-default-typed-env-bindings ((vars cmr::pseudo-var-list-p)
                                        (ctx type-ctx-p)
                                        (env))
  :returns (new-env)
  (if (atom vars)
      env
    (cons (cons (pseudo-var-fix (car vars))
                (tac-typed-val-default
                 (cdr (hons-assoc-equal (pseudo-var-fix (car vars))
                                        (type-ctx-fix ctx)))))
          (add-default-typed-env-bindings (cdr vars) ctx env)))
  ///
  (defret lookup-of-<fn>
    (equal (hons-assoc-equal v new-env)
           (if (member-equal v (cmr::pseudo-var-list-fix vars))
               (cons v (tac-typed-val-default
                        (cdr (hons-assoc-equal v (type-ctx-fix ctx)))))
             (hons-assoc-equal v env))))

  (local (defret tac-typed-env-p-aux-of-<fn>
           (implies (tac-typed-env-p-aux keys env (add-event-ctx-bindings vars ctx))
                    (tac-typed-env-p-aux keys new-env ctx))
           :hints(("Goal" :in-theory (enable tac-typed-env-p-aux)))))

  (defret tac-typed-env-p-of-<fn>
    (implies (tac-typed-env-p env (add-event-ctx-bindings vars ctx))
             (tac-typed-env-p new-env ctx))
    :hints(("Goal" :in-theory (enable tac-typed-env-p))))

  (defret tac-ev-cube-of-<fn>
    (implies (not (intersectp-equal (cmr::pseudo-var-list-fix vars)
                                    (cmr::termlist-vars x)))
             (equal (tac-ev-cube x new-env)
                    (tac-ev-cube x env)))
    :hints(("Goal" :in-theory (enable cmr::pseudo-var-list-fix
                                      intersectp-equal)))))



(defret tac-cube-satisfiable-of-add-event-ctx-bindings
  (implies (not (intersectp-equal (cmr::pseudo-var-list-fix vars)
                                  (cmr::termlist-vars x)))
           (iff (tac-cube-satisfiable x (add-event-ctx-bindings vars ctx))
                (tac-cube-satisfiable x ctx)))
  :hints ((acl2::use-termhint
           (if (tac-cube-satisfiable x ctx)
               `(:expand ((tac-cube-satisfiable x ctx))
                 :use ((:instance tac-cube-satisfiable-suff
                        (env (add-event-env-bindings vars (tac-cube-satisfiable-witness x ctx)))
                        (ctx (add-event-ctx-bindings vars ctx))))
                 :in-theory (disable tac-cube-satisfiable-suff
                                     tac-cube-satisfiable-suff2))
             `(:expand ((tac-cube-satisfiable x (add-event-ctx-bindings vars ctx)))
               :use ((:instance tac-cube-satisfiable-suff
                      (env (add-default-typed-env-bindings
                            vars ctx
                            (tac-cube-satisfiable-witness x (add-event-ctx-bindings vars ctx))))
                      (ctx ctx))))))))



(define iterative-rewrite-top ((nvars natp)
                               (assums pseudo-term-listp))
  :returns (results tac-caselist-p)
  (iterative-rewrite-and-intro assums nil
                               (anonymous-vars nvars)
                               (tac-termlist-event-vars assums))
  ///
  (defret vars-of-<fn>
    (implies (and (not (member-equal v (cmr::termlist-vars assums)))
                  (not (anonymous-var-p v)))
             (not (member-equal v (tac-caselist-vars results)))))

  (defret type-of-<fn>
    (implies (and (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  (not (has-anonymous-var (cmr::termlist-vars assums)))
                  (event-vars-p (anonymous-vars nvars) ctx))
             (tac-caselist-typed results ctx)))
  
  (defret type-of-<fn>-add-vars
    (implies (and (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  (not (has-anonymous-var (cmr::termlist-vars assums))))
             (tac-caselist-typed results (add-event-ctx-bindings (anonymous-vars nvars) ctx)))
    :hints (("goal" :use ((:instance type-of-iterative-rewrite-and-intro
                           (ctx (add-event-ctx-bindings (anonymous-vars nvars) ctx))
                           (substmap nil)
                           (freevars (anonymous-vars nvars))
                           (eventvars (tac-termlist-event-vars assums))))
             :in-theory (disable type-of-iterative-rewrite-and-intro))))

  (local (defthm intersectp-equal-of-tac-termlist-event-vars
           (implies (not (intersectp-equal x (cmr::termlist-vars assums)))
                    (not (intersectp-equal x (tac-termlist-event-vars assums))))
           :hints(("Goal" :in-theory (enable acl2::intersectp-witness-rw)))))

  (defret <fn>-equisatisfiable
    (implies (and (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                  (not (has-anonymous-var (cmr::termlist-vars assums)))
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred))
                  (event-vars-p (anonymous-vars nvars) ctx))
             (iff (tac-caselist-satisfiable results ctx)
                  (tac-cube-satisfiable assums ctx))))

  (defret <fn>-equisatisfiable-add-bindings
    (implies (and (not (member-equal 'tac-w (cmr::termlist-vars assums)))
                  (not (has-anonymous-var (cmr::termlist-vars assums)))
                  (subsetp-equal (tac-termlist-types assums ctx) '(:pred)))
             (iff (tac-caselist-satisfiable results (add-event-ctx-bindings
                                                     (anonymous-vars nvars) ctx))
                  (tac-cube-satisfiable assums ctx)))))
