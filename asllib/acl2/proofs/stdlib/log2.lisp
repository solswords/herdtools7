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

(in-package "ASL")

(include-book "../../openers")
(include-book "stdlib")
(include-book "utils")
(include-book "centaur/bitops/rational-exponent" :dir :system)
(local (include-book "ast-theory"))

(local (in-theory (disable (tau-system))))

(local (in-theory (disable floor mod
                           put-assoc-equal
                           hons-assoc-equal)))

(defsection log2-loop

  (defconst *log2-loop*
    (find-nth-form 0 :s_while (assoc-equal "Log2" (static_env_global->subprograms
                                                    (stdlib-static-env)))))

  (defconst *log2-loop-test*
    (s_while->test *log2-loop*))

  (defconst *log2-loop-body*
    (s_while->body *log2-loop*))

  ;; (local (defthm ratonal-exponent-of-equal-to-expt-2
  ;;          (implies (equal x (expt 2 n))
  ;;                   (equal (acl2::rational-exponent x)
  ;;                          (ifix n)))))


  (local (Defthmd rational-exponent-unique-of-nonneg
           (implies (and (<= (expt 2 r) a)
                         (< a (* 2 (expt 2 r)))
                         (integerp a)
                         (integerp r))
                    (equal (acl2::rational-exponent a) r))
           :hints (("goal" :use ((:instance acl2::rational-sign-significand-exponent-unique
                                  (sign 1) (significand (/ a (expt 2 r))) (exponent r)))))))
  
  (local (defthm rational-exponent-hack
           (implies (and (<= a (expt 2 r))
                         (< (expt 2 r) (* 2 a))
                         (integerp a)
                         (integerp r))
                    (equal r (if (equal a (expt 2 r))
                                 (acl2::rational-exponent a)
                               (+ 1 (acl2::rational-exponent a)))))
           :hints (("goal" :do-not-induct t
                    :expand ((:free (x) (hide x))))
                   (and stable-under-simplificationp
                        '(:use ((:instance rational-exponent-unique-of-nonneg
                                 (r (+ -1 r))))
                          :expand ((expt 2 r)))))
           :otf-flg t
           :rule-classes nil))
                         

  (local (defthm put-assoc-equal-identity-free
           (implies (and (equal v (cdr (hons-assoc-equal k x)))
                         (hons-assoc-equal k x)
                         (alistp x))
                    (equal (put-assoc-equal k v x) x))))

  ;; (local (defthmd equal-of-v_int->val
  ;;          (implies (val-case x :v_int)
  ;;                   (equal (equal (v_int->val x) y)
  ;;                          (and (integerp y)
  ;;                               (equal (val-fix x) (v_int y)))))))

                         
  
  (local (defthmd equal-when-v_int
           (implies (and (val-case x :v_int)
                         (val-case y :v_int)
                         (val-p x) (val-p y))
                    (equal (equal x y)
                           (equal (v_int->val x)
                                  (v_int->val y))))
           :hints (("goal" :use ((:instance val-fix-when-v_int (x x))
                                 (:instance val-fix-when-v_int (x y)))
                    :in-theory (disable v_int-of-fields
                                        equal-of-v_int)))))




  (local (defthmd powers-of-2-not-between-lemma1
           (implies (and (< (ifix ye) (ifix xe))
                         (<= (ifix ye) 0))
                    (<= (* 2 (expt 2 ye)) (expt 2 xe)))
           :hints (("goal" :induct (expt 2 ye)))
           :otf-flg t))
  (local (defthmd powers-of-2-not-between-lemma
           (implies (< (ifix ye) (ifix xe))
                    (<= (* 2 (expt 2 ye)) (expt 2 xe)))
           :hints (("goal" :cases ((<= 0 (ifix ye)))
                    :in-theory (enable powers-of-2-not-between-lemma1)))
           :otf-flg t))  

  (local (defthm powers-of-2-not-between
           (implies (< (expt 2 xe) (* 2 (expt 2 ye)))
                    (<= (expt 2 xe) (expt 2 ye)))
           :hints (("goal" :use ((:instance acl2::expt-is-increasing-for-base>1
                                  (r 2) (i (ifix xe)) (j (ifix ye)))
                                 (:instance acl2::expt-is-increasing-for-base>1
                                  (r 2) (i (ifix ye)) (j (ifix xe)))
                                 powers-of-2-not-between-lemma)
                    :in-theory (acl2::e/d* (acl2::arith-equiv-forwarding)
                                           (acl2::expt-is-increasing-for-base>1))))
           :rule-classes nil))
  
  ;; (local (defthmd equal-when-powers-of-2
  ;;          (implies (and (equal x (expt 2 xe))
  ;;                        (equal y (expt 2 ye))
  ;;                        (< x (* 2 y)))
  ;;                   (equal (< x y)
  ;;                          (not (equal x y))))
  ;;          :hints (("goal" :do-not-induct t
  ;;                   :use ((:instance ACL2::EXPT-IS-INCREASING-FOR-BASE>1
  ;;                          (r 2) (i (ifix ye)) (j (ifix xe)))
  ;;                         (:instance ACL2::EXPT-IS-INCREASING-FOR-BASE>1
  ;;                          (r 2) (i (ifix xe)) (j (ifix ye))))
  ;;                   :in-theory (acl2::e/d* (acl2::arith-equiv-forwarding)
  ;;                                          (acl2::expt-is-increasing-for-base>1))))
  ;;          :otf-flg t))

  (local (defthm v_int->val-rewrite-to-exponent
           (implies (equal (v_int->val x) (expt 2 y))
                    (equal (v_int->val x) (expt 2 y)))))
  
  (defthm log2-loop-correct
    (b* ((storage (local-env->storage
                   (env->local env)))
         (a-look (assoc-equal "__stdlib_local_a" storage))
         (a (cdr a-look))
         ((v_int a))
         (current-look (assoc-equal "__stdlib_local_current" storage))
         (current (cdr current-look))
         ((v_int current))
         (result-look (assoc-equal "__stdlib_local_result" storage))
         (result (cdr result-look))
         ((v_int result)))
      (implies (and a-look
                    (val-case a :v_int)
                    current-look
                    (val-case current :v_int)
                    result-look
                    (val-case result :v_int)
                    (<= 0 result.val)
                    (equal current.val (expt 2 result.val))
                    (< current.val (* 2 a.val))
                    (natp clk)
                    (< (- (+ 1 (acl2::rational-exponent a.val)) result.val) clk)
                    (integerp limit)
                    (< (- (+ 1 (acl2::rational-exponent a.val)) result.val) limit)
                    (no-duplicatesp-equal (acl2::alist-keys storage)))
               (b* (((mv (ev_normal res) &) (eval_loop env t limit *log2-loop-test* *log2-loop-body*))
                    ((continuing res.res))
                    (result-spec (let ((exp (acl2::rational-exponent a.val)))
                                   (if (equal a.val (expt 2 exp))
                                       exp
                                     (+ 1 exp))))
                    (current-spec (expt 2 result-spec))
                    ((env env))
                    ((local-env env.local)))
                 (and (equal (eval_result-kind res) :ev_normal)
                      (equal (control_flow_state-kind res.res) :continuing)
                      (equal res.res.env
                             (change-env env
                                         :local (change-local-env
                                                 env.local
                                                 :storage (put-assoc-equal "__stdlib_local_current"
                                                                           (v_int current-spec)
                                                                           (put-assoc-equal "__stdlib_local_result"
                                                                                            (v_int result-spec)
                                                                                            env.local.storage)))))))))
    :hints (("goal" :induct (loop-induct env clk *log2-loop-test* *log2-loop-body* t limit orac)
             :in-theory (enable check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                pop_scope
                                tick_loop_limit
                                v_to_bool)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((eval_loop env t limit *log2-loop-test* *log2-loop-body*))))
            (and stable-under-simplificationp
                 '(:use ((:instance rational-exponent-hack
                          (a (V_INT->VAL
                              (CDR (HONS-ASSOC-EQUAL "__stdlib_local_a"
                                                     (LOCAL-ENV->STORAGE (ENV->LOCAL ENV))))))
                          (r (V_INT->VAL
                              (CDR (HONS-ASSOC-EQUAL "__stdlib_local_result"
                                                     (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))))
                         (:instance powers-of-2-not-between
                          (xe (V_INT->VAL
                               (CDR (HONS-ASSOC-EQUAL "__stdlib_local_result"
                                                      (LOCAL-ENV->STORAGE (ENV->LOCAL ENV))))))
                          (ye (acl2::rational-exponent
                               (V_INT->VAL
                                (CDR (HONS-ASSOC-EQUAL "__stdlib_local_a"
                                                       (LOCAL-ENV->STORAGE (ENV->LOCAL ENV))))))))
                         (:instance rational-exponent-when-expt-less
                          (i (V_INT->VAL
                               (CDR (HONS-ASSOC-EQUAL "__stdlib_local_result"
                                                      (LOCAL-ENV->STORAGE (ENV->LOCAL ENV))))))
                          (x (V_INT->VAL
                              (CDR (HONS-ASSOC-EQUAL "__stdlib_local_a"
                                                     (LOCAL-ENV->STORAGE (ENV->LOCAL ENV))))))))
                   :in-theory (e/d (equal-when-v_int)
                                   (rational-exponent-when-expt-less))))
            ;; (and stable-under-simplificationp
            ;;      '(:in-theory (e/d (equal-when-v_int)
            ;;                        (rational-exponent-hack))))
            ;; (and stable-under-simplificationp
            ;;      '(:in-theory (e/d (equal-of-v_int->val)
            ;;                        (equal-of-v_int))))
            )))



(defsection log2-loop

  (defconst *log2-loop*
    (find-nth-form 0 :s_while (assoc-equal "Log2" (static_env_global->subprograms
                                                    (stdlib-static-env)))))

  (defconst *log2-loop-test*
    (s_while->test *log2-loop*))

  (defconst *log2-loop-body*
    (s_while->body *log2-loop*))

  ;; (local (defthm ratonal-exponent-of-equal-to-expt-2
  ;;          (implies (equal x (expt 2 n))
  ;;                   (equal (acl2::rational-exponent x)
  ;;                          (ifix n)))))


  (local (Defthmd rational-exponent-unique-of-nonneg
           (implies (and (<= (expt 2 r) a)
                         (< a (* 2 (expt 2 r)))
                         (integerp a)
                         (integerp r))
                    (equal (acl2::rational-exponent a) r))
           :hints (("goal" :use ((:instance acl2::rational-sign-significand-exponent-unique
                                  (sign 1) (significand (/ a (expt 2 r))) (exponent r)))))))
  
  (local (defthm rational-exponent-hack
           (implies (and (<= a (expt 2 r))
                         (< (expt 2 r) (* 2 a))
                         (integerp a)
                         (integerp r))
                    (equal r (if (equal a (expt 2 r))
                                 (acl2::rational-exponent a)
                               (+ 1 (acl2::rational-exponent a)))))
           :hints (("goal" :do-not-induct t
                    :expand ((:free (x) (hide x))))
                   (and stable-under-simplificationp
                        '(:use ((:instance rational-exponent-unique-of-nonneg
                                 (r (+ -1 r))))
                          :expand ((expt 2 r)))))
           :otf-flg t
           :rule-classes nil))
                         

  (local (defthm put-assoc-equal-identity-free
           (implies (and (equal v (cdr (hons-assoc-equal k x)))
                         (hons-assoc-equal k x)
                         (alistp x))
                    (equal (put-assoc-equal k v x) x))))
  (local (in-theory (disable acl2::put-assoc-equal-identity)))

  ;; (local (defthmd equal-of-v_int->val
  ;;          (implies (val-case x :v_int)
  ;;                   (equal (equal (v_int->val x) y)
  ;;                          (and (integerp y)
  ;;                               (equal (val-fix x) (v_int y)))))))

                         
  
  (local (defthmd equal-when-v_int
           (implies (and (syntaxp (and (not (case-match x (('val-kind$inline . &) t)))
                                       (not (case-match y (('val-kind$inline . &) t)))))
                         (val-case x :v_int)
                         (val-case y :v_int)
                         (val-p x) (val-p y))
                    (equal (equal x y)
                           (equal (v_int->val x)
                                  (v_int->val y))))
           :hints (("goal" :use ((:instance val-fix-when-v_int (x x))
                                 (:instance val-fix-when-v_int (x y)))
                    :in-theory (disable v_int-of-fields
                                        equal-of-v_int)))))

  (local (in-theory (disable equal-of-v_int)))


  (local (defthmd powers-of-2-not-between-lemma1
           (implies (and (< (ifix ye) (ifix xe))
                         (<= (ifix ye) 0))
                    (<= (* 2 (expt 2 ye)) (expt 2 xe)))
           :hints (("goal" :induct (expt 2 ye)))
           :otf-flg t))
  (local (defthmd powers-of-2-not-between-lemma
           (implies (< (ifix ye) (ifix xe))
                    (<= (* 2 (expt 2 ye)) (expt 2 xe)))
           :hints (("goal" :cases ((<= 0 (ifix ye)))
                    :in-theory (enable powers-of-2-not-between-lemma1)))
           :otf-flg t))  

  (local (defthm powers-of-2-not-between
           (implies (< (expt 2 xe) (* 2 (expt 2 ye)))
                    (<= (expt 2 xe) (expt 2 ye)))
           :hints (("goal" :use ((:instance acl2::expt-is-increasing-for-base>1
                                  (r 2) (i (ifix xe)) (j (ifix ye)))
                                 (:instance acl2::expt-is-increasing-for-base>1
                                  (r 2) (i (ifix ye)) (j (ifix xe)))
                                 powers-of-2-not-between-lemma)
                    :in-theory (acl2::e/d* (acl2::arith-equiv-forwarding)
                                           (acl2::expt-is-increasing-for-base>1))))
           :rule-classes nil))

  (local (defthm powers-of-2-not-between-rw
           (implies (and (equal y (expt 2 ye))
                         (> (expt 2 xe) (expt 2 ye)))
                    (>= (expt 2 xe) (* 2 y)))
           :hints (("goal" :use powers-of-2-not-between
                    :do-not-induct t))))
  
  ;; (local (defthmd equal-when-powers-of-2
  ;;          (implies (and (equal x (expt 2 xe))
  ;;                        (equal y (expt 2 ye))
  ;;                        (< x (* 2 y)))
  ;;                   (equal (< x y)
  ;;                          (not (equal x y))))
  ;;          :hints (("goal" :do-not-induct t
  ;;                   :use ((:instance ACL2::EXPT-IS-INCREASING-FOR-BASE>1
  ;;                          (r 2) (i (ifix ye)) (j (ifix xe)))
  ;;                         (:instance ACL2::EXPT-IS-INCREASING-FOR-BASE>1
  ;;                          (r 2) (i (ifix xe)) (j (ifix ye))))
  ;;                   :in-theory (acl2::e/d* (acl2::arith-equiv-forwarding)
  ;;                                          (acl2::expt-is-increasing-for-base>1))))
  ;;          :otf-flg t))

  (defund is-same-as (x y)
    (equal x y))
  
  (local (defthm rewrite-equal-of-current->val
           (b* ((current-look (hons-assoc-equal "__stdlib_local_current" storage))
                (current (cdr current-look))
                ((v_int current))
                (result-look (hons-assoc-equal "__stdlib_local_result" storage))
                (result (cdr result-look))
                ((v_int result)))
             (equal (equal current.val (expt 2 result.val))
                    (is-same-as current.val (expt 2 result.val))))
           :hints(("Goal" :in-theory (enable is-same-as)))))

  (local (defthm rewrite-current->val-when-same-as
           (b* ((current-look (hons-assoc-equal "__stdlib_local_current" storage))
                (current (cdr current-look))
                ((v_int current))
                (result-look (hons-assoc-equal "__stdlib_local_result" storage))
                (result (cdr result-look))
                ((v_int result)))
             (implies (is-same-as current.val (expt 2 result.val))
                      (equal current.val (expt 2 result.val))))
           :hints(("Goal" :in-theory (e/d (is-same-as)
                                          (rewrite-equal-of-current->val))))))

  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (acl2::use-trivial-ancestors-check))

  ;; (defthm rational-exponent-when-expt*2-less
  ;;   (implies (and (rationalp x)
  ;;                 (<= (* 2 (expt 2 i)) x)
  ;;                 (integerp i))
  ;;            (<= (+ 1 i) (acl2::rational-exponent x)))
  ;;   :hints (("goal" :use ((:instance rational-exponent-when-expt-less
  ;;                          (i (+ 1 i)) (x x)))
  ;;            :expand ((expt 2 (+ 1 i)))
  ;;            :in-theory (disable rational-exponent-when-expt-less)
  ;;            :do-not-induct t))
  ;;   :rule-classes :linear)

  (defthm rational-exponent-when-expt-strictly-less
    (implies (and (rationalp x)
                  (< (expt 2 i) x)
                  (integerp i))
             (<= i (acl2::rational-exponent x)))
    :hints (("goal" :use ((:instance rational-exponent-when-expt-less
                           (i i) (x x)))
             :in-theory (disable rational-exponent-when-expt-less)
             :do-not-induct t))
    :rule-classes :linear)
  
  (defthm log2-loop-correct
    (b* ((storage (local-env->storage
                   (env->local env)))
         (a-look (assoc-equal "__stdlib_local_a" storage))
         (a (cdr a-look))
         ((v_int a))
         (current-look (assoc-equal "__stdlib_local_current" storage))
         (current (cdr current-look))
         ((v_int current))
         (result-look (assoc-equal "__stdlib_local_result" storage))
         (result (cdr result-look))
         ((v_int result)))
      (implies (and a-look
                    (val-case a :v_int)
                    current-look
                    (val-case current :v_int)
                    result-look
                    (val-case result :v_int)
                    (<= 0 result.val)
                    (equal current.val (expt 2 result.val))
                    (< current.val (* 2 a.val))
                    (natp clk)
                    (< (- (+ 1 (acl2::rational-exponent a.val)) result.val) clk)
                    (integerp limit)
                    (< (- (+ 1 (acl2::rational-exponent a.val)) result.val) limit)
                    (no-duplicatesp-equal (acl2::alist-keys storage)))
               (b* (((mv (ev_normal res) &) (eval_loop env t limit *log2-loop-test* *log2-loop-body*))
                    ((continuing res.res))
                    (result-spec (let ((exp (acl2::rational-exponent a.val)))
                                   (if (equal a.val (expt 2 exp))
                                       exp
                                     (+ 1 exp))))
                    (current-spec (expt 2 result-spec))
                    ((env env))
                    ((local-env env.local)))
                 (and (equal (eval_result-kind res) :ev_normal)
                      (equal (control_flow_state-kind res.res) :continuing)
                      (equal res.res.env
                             (change-env env
                                         :local (change-local-env
                                                 env.local
                                                 :storage (put-assoc-equal "__stdlib_local_current"
                                                                           (v_int current-spec)
                                                                           (put-assoc-equal "__stdlib_local_result"
                                                                                            (v_int result-spec)
                                                                                            env.local.storage)))))))))
    :hints (("goal" :induct (loop-induct env clk *log2-loop-test* *log2-loop-body* t limit orac)
             :in-theory (enable check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                pop_scope
                                tick_loop_limit
                                v_to_bool)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((eval_loop env t limit *log2-loop-test* *log2-loop-body*))))
            (and stable-under-simplificationp
                 '(:use ((:instance rational-exponent-hack
                          (a (V_INT->VAL
                              (CDR (HONS-ASSOC-EQUAL "__stdlib_local_a"
                                                     (LOCAL-ENV->STORAGE (ENV->LOCAL ENV))))))
                          (r (V_INT->VAL
                              (CDR (HONS-ASSOC-EQUAL "__stdlib_local_result"
                                                     (LOCAL-ENV->STORAGE (ENV->LOCAL ENV))))))))
                   :in-theory (e/d (equal-when-v_int)
                                   (equal-of-v_int)
                                   ))))))


(defsection log2-correct

  (defthm log2-correct
    (implies (and (subprograms-match '("Log2")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (natp i)
                  (integerp clk)
                  (< (+ 1 i) clk)
                  (< (+ 1 i) (expt 2 128))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "Log2" nil (list (v_int (expt 2 i))) :clk clk))
                    (ev_normal (func_result (list (v_int i)) (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram  env "Log2" nil (list (v_int (expt 2 i))) :clk clk))
             :in-theory (enable check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack)
             :do-not-induct t))))



