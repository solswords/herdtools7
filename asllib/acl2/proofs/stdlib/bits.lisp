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
(include-book "misc")
(include-book "centaur/bitops/logrepeat" :dir :system) ;; for replicate
(include-book "centaur/bitops/trailing-0-count" :dir :system) ;; for lowestsetbit
(local (include-book "ast-theory"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))

(local (in-theory (disable (tau-system))))

(local (in-theory (disable floor mod expt
                           put-assoc-equal
                           hons-assoc-equal
                           unsigned-byte-p
                           logmask)))




;; Replicate
;; BitCount
;; LowestSetBit
;; LowestSetBitNZ
;; HighestSetBit
;; HighestSetBitNZ
;; SignExtend
;; Extend
;; CountLeadingZeroBits
;; CountLeadingSignBits



(local (defthm nfix-when-not-negp
         (implies (not (negp x))
                  (equal (nfix x) (ifix x)))
         :hints(("Goal" :in-theory (enable nfix ifix)))))


  
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

(defsection replicate-1-loop

  ;; (local (defthm v_int-elim
  ;;          (implies (val-case x :v_int)
  ;;                   (val-equiv (v_int (v_int->val x)) x))
  ;;          :rule-classes :elim))

  ;; (local (defthm v_bitvector-elim
  ;;          (implies (val-case x :v_bitvector)
  ;;                   (val-equiv (v_bitvector (v_bitvector->len x)
  ;;                                           (v_bitvector->val x))
  ;;                              x))
  ;;          :rule-classes :elim))

  (local (defthm cons-under-iff
           (iff (cons x y) t)))
  
  
  (defconst *replicate-1-loop*
    (find-nth-form 0 :s_for (assoc-equal "Replicate-1" (static_env_global->subprograms
                                                 (stdlib-static-env)))))

  (defconst *replicate-1-loop-body*
    (s_for->body *replicate-1-loop*))


  (local (defthm bound-lemma
           (implies (and (equal r (* x items))
                         (rationalp x)
                         (integerp i)
                         (integerp items)
                         (< i items)
                         (<= 0 x))
                    (>= r (+ x (* x i))))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (local (defthm bound-lemma2
           (implies (and (equal r (* x items))
                         (rationalp x)
                         (integerp i)
                         (integerp items)
                         (< i items)
                         (<= 0 x))
                    (>= r (* x i)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (local (defthm bound-lemma3
           (implies (and (equal r (* x items))
                         (rationalp x)
                         (integerp i)
                         (integerp items)
                         (< i items)
                         (<= 0 x))
                    (>= (+ r (- (* x i))) x))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (local (defthm expt-minus-1-to-logmask
           (implies (not (negp n))
                    (equal (+ -1 (expt 2 n))
                           (bitops::logmask n)))
           :hints(("Goal" :in-theory (enable bitops::logmask)))))


  (local (defun bits-ind1 (rl xl rv xv)
           (if (zp xl)
               (list rl rv xv)
             (bits-ind1 (1- rl) (1- xl) (logcdr rv) (logcdr xv)))))

  (local (defthm logand-loghead-neg1
           (equal (logand x (loghead n -1))
                  (loghead n x))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-inductions
                                                    bitops::ihsext-recursive-redefs)))))
  (local (defthm bits-lemma-lemma
           (implies (unsigned-byte-p xl xv)
                    (EQUAL (LOGIOR (LOGHEAD RL XV)
                                   (LOGAND RV (LOGHEAD RL (LOGNOT (LOGMASK XL)))))
                           (LOGHEAD RL (LOGAPP XL XV (LOGTAIL XL RV)))))
           :hints (("goal" :in-theory (acl2::e/d* (bitops::ihsext-recursive-redefs))
                    :induct (bits-ind1 rl xl rv xv)))))
  (local (defun bits-ind (rl sh rv xv)
           (if (zp sh)
               (list rl rv xv)
             (bits-ind (1- rl) (1- sh) (logcdr rv) xv))))
  (local (defthm bits-lemma
           (implies (and (not (negp sh))
                         (unsigned-byte-p xl xv))
                    (equal (logior (loghead rl (ash xv sh))
                                   (logand rv (loghead rl (lognot (ash (logmask xl) sh)))))
                           (loghead rl (logapp sh rv (logapp xl xv (logtail (+ (nfix sh) (nfix xl)) rv))))))
           :hints(("Goal" :in-theory (acl2::e/d* (bitops::ihsext-recursive-redefs))
                   :induct (bits-ind rl sh rv xv)))))

  
  (local (defthm logtail-of-logrepeat
           (implies (>= (nfix m) (* (nfix n) (nfix w)))
                    (equal (logtail m (logrepeat n w x))
                           0))
           :hints(("Goal" :in-theory (enable logrepeat
                                             bitops::logtail-of-logapp-split))
                  (and stable-under-simplificationp
                       '(:nonlinearp t)))))

  (local (defthm logtail-of-equal-logrepeat
           (implies (and (equal y (logrepeat n w x))
                         (>= (nfix m) (* (nfix n) (nfix w))))
                    (equal (logtail m y)
                           0))))

  ;; (local (defthm logapp-of-equal-logapp
  ;;          (implies (equal x (logapp w2 a b))
  ;;                   (equal (logapp w1 x c)
  ;;                          (let ((w1 (nfix w1))
  ;;                                (w2 (nfix w2)))
  ;;                            (logapp (min w1 w2)
  ;;                                    a
  ;;                                    (if (<= w1 w2) c (logapp (- w1 w2) b c))))))
  ;;          :hints(("Goal" :in-theory (enable bitops::logapp-right-assoc)))))

  (local (defthm logapp-of-logrepeat
           (implies (and (natp n) (natp w))
                    (equal (logapp (* n w) (logrepeat n w x) (logrepeat m w x))
                           (logrepeat (+ n (nfix m)) w x)))
           :hints (("goal" :induct (logrepeat n w x)
                    :in-theory (enable logrepeat bitops::logapp-right-assoc)))))

  ;; (local (defthm logrepeat-when-zp-w
  ;;          (implies (and (syntaxp (not (equal w ''0)))
  ;;                        (zp w))
  ;;                   (equal (logrepeat n w x)
  ;;                          0))
  ;;          :hints(("Goal" :in-theory (enable logrepeat)))))
           
  

  ;; (local (defthmd logrepeat-rev
  ;;          (equal (logrepeat n w x)
  ;;                 (if (zp n)
  ;;                     0
  ;;                   (logapp (* (1- n) (nfix w))
  ;;                           (logrepeat (1- n) w x)
  ;;                           (loghead w x))))
  ;;          :hints(("Goal" :use ((:instance logapp-of-logrepeat
  ;;                                (n (1- (nfix n))) (m 1) (w (nfix w))))
  ;;                  :expand ((logrepeat 1 w x)
  ;;                           (:free (w) (logrepeat 0 w x)))))))
  
  (local (defthm logapp-of-equal-to-logrepeat
           (implies (and (natp n) (natp w)
                         (equal y (logrepeat n w x))
                         (unsigned-byte-p w x))
                    (equal (logapp (* w n) y x)
                           (logrepeat (+ 1 n) w x)))
           :hints(("Goal" :use ((:instance logapp-of-logrepeat
                                 (n n) (m 1)))
                   :expand ((logrepeat 1 w x))))))
  
  (defthm replicate-1-loop-correct
    (b* ((storage (local-env->storage
                   (env->local env)))
         (i-look (assoc-equal "__stdlib_local_i" storage))
         (i (cdr i-look))
         ((v_int i))
         (m-look (assoc-equal "__stdlib_local_M" storage))
         (m (cdr m-look))
         ((v_int m))
         (items-look (assoc-equal "__stdlib_local_items" storage))
         (items (cdr items-look))
         ((v_int items))
         (result-look (assoc-equal "__stdlib_local_result" storage))
         (result (cdr result-look))
         ((v_bitvector result))
         (x-look (assoc-equal "__stdlib_local_x" storage))
         (x (cdr x-look))
         ((v_bitvector x)))
      (implies (and i-look
                    (val-case i :v_int)
                    (equal i.val start)
                    m-look
                    (val-case m :v_int)
                    items-look
                    (val-case items :v_int)
                    result-look
                    (val-case result :v_bitvector)
                    x-look
                    (val-case x :v_bitvector)
                    (equal x.len m.val)
                    (equal result.len (* items.val m.val))
                    (equal result.val (logrepeat start m.val x.val))
                    
                    (natp clk)
                    (natp start)
                    (integerp end)
                    (<= start (+ 1 end))
                    (equal end (+ -1 items.val))
                    (no-duplicatesp-equal (acl2::alist-keys storage)))
               (b* (((mv (ev_normal res) &) (eval_for env "__stdlib_local_i" nil start :up end *replicate-1-loop-body*))
                    ((continuing res.res))
                    (result-spec (logrepeat items.val m.val x.val))
                    ((env env))
                    ((local-env env.local)))
                 (and (equal res.res.env
                             (change-env env
                                         :local (change-local-env
                                                 env.local
                                                 :storage (put-assoc-equal "__stdlib_local_i"
                                                                           (v_int (+ 1 end))
                                                                           ;; (if (equal start (+ 1 end))
                                                                           ;;     env.local.storage
                                                                             (put-assoc-equal "__stdlib_local_result"
                                                                                              (v_bitvector
                                                                                               (* items.val m.val)
                                                                                               result-spec)
                                                                                              env.local.storage)))))
                      (equal (eval_result-kind res) :ev_normal)
                      (equal (control_flow_state-kind res.res) :continuing)))))
    :hints (("goal" :induct (for-induct env "__stdlib_local_i" start :up end *replicate-1-loop-body* clk nil orac)
             :in-theory (enable check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                eval_for_step
                                for_loop-step
                                FOR_LOOP-TEST
                                pop_scope
                                check-bad-slices
                                check_non_overlapping_slices
                                check_non_overlapping_slices-1
                                slices_sub
                                slices-width
                                write_to_bitvector
                                write_to_bitvector-aux
                                vbv-to-int)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((:free (end)
                             (eval_for env "__stdlib_local_i"
                                       nil
                                       (V_INT->VAL
                                        (CDR (HONS-ASSOC-EQUAL "__stdlib_local_i"
                                                               (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))
                                       :up end *replicate-1-loop-body*))
                            (:free (end)
                             (eval_for env "__stdlib_local_i" nil end :up end *replicate-1-loop-body*))
                            (:free (env end)
                             (eval_for env "__stdlib_local_i" nil (+ 1 end) :up end *replicate-1-loop-body*))
                            (:free (env end)
                             (eval_for env "__stdlib_local_i" nil end :up (+ -1 end) *replicate-1-loop-body*)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable equal-when-v_int)))
            )))



(defsection replicate-1-correct

  
  (local (defthm logrepeat-is-logmask
           (implies (equal (loghead 1 x) 1)
                    (equal (logrepeat n 1 x) (logmask n)))
           :hints(("Goal" :in-theory (enable bitops::loghead**
                                             logrepeat
                                             bitops::logapp**
                                             bitops::logmask**)))))

  (local (defthm logrepeat-is-zero
           (implies (equal (loghead 1 x) 0)
                    (equal (logrepeat n 1 x) 0))
           :hints(("Goal" :in-theory (enable bitops::loghead**
                                             logrepeat
                                             bitops::logapp**)))))

  (local (defthm logrepeat-0
           (equal (logrepeat 0 m x) 0)
           :hints(("Goal" :in-theory (enable logrepeat)))))
  
  (defthm replicate-1-correct
    (b* ((m (v_int->val mi))
         ((v_bitvector xv)))
      (implies (and (subprograms-match '("Replicate-1" "Zeros-1" "Ones-1")
                                       (global-env->static (env->global env))
                                       (stdlib-static-env))
                    (integerp n)
                    (integerp m)
                    (<= 0 n)
                    (<= 1 m)
                    (integerp (/ n m))
                    (<= 2 (nfix clk))
                    (val-case mi :v_int)
                    (val-case xv :v_bitvector)
                    (equal xv.len m)
                    (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                             (env->global env)))))
               (equal (mv-nth 0 (eval_subprogram env "Replicate-1"
                                                 (list (v_int n) mi)
                                                 (list xv) :clk clk))
                      (ev_normal (func_result (list (v_bitvector n (logrepeat (/ n m) m xv.val))) (env->global env))))))
    :hints (("goal" :expand ((eval_subprogram env "Replicate-1"
                                              (list (v_int n) mi)
                                              (list xv) :clk clk))
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int
                                slices_sub))
             :do-not-induct t))))


(defsection replicate-correct

  
  (defthm replicate-correct
    (implies (and (subprograms-match '("Replicate" "Replicate-1" "Zeros-1" "Ones-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (integerp n)
                  (integerp m)
                  (<= 0 n)
                  (<= 1 m)
                  (integerp (/ n m))
                  (<= 3 (nfix clk))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "Replicate"
                                               (list (v_int m) (v_int n))
                                               (list (v_bitvector m x) (v_int n)) :clk clk))
                    (ev_normal (func_result (list (v_bitvector (* n m) (logrepeat n m (nfix x)))) (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "Replicate"
                                              (list (v_int m) (v_int n))
                                               (list (v_bitvector m x) (v_int n)) :clk clk))
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int
                                slices_sub))
             :do-not-induct t))))




(local (defthm loghead-1-of-bit
         (implies (bitp x)
                  (equal (loghead 1 x) x))
         :hints(("Goal" :in-theory (enable bitops::loghead**)))))

(defsection BitCount-loop
  
  
  (defconst *BitCount-loop*
    (find-nth-form 0 :s_for (assoc-equal "BitCount" (static_env_global->subprograms
                                                 (stdlib-static-env)))))

  (defconst *BitCount-loop-body*
    (s_for->body *BitCount-loop*))

  (local (defthm logcount-loghead-when-logbitp
           (implies (and (logbitp n x)
                         (natp n))
                    (equal (logcount (loghead (+ 1 n) x))
                           (+ 1 (logcount (loghead n x)))))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-inductions
                                                    bitops::ihsext-recursive-redefs)))))

  (local (defthm logcount-loghead-when-not-logbitp
           (implies (and (not (logbitp n x))
                         (natp n))
                    (equal (logcount (loghead (+ 1 n) x))
                           (logcount (loghead n x))))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-inductions
                                                    bitops::ihsext-recursive-redefs)))))

  (defthm BitCount-loop-correct
    (b* ((storage (local-env->storage
                   (env->local env)))
         (i-look (assoc-equal "__stdlib_local_i" storage))
         (i (cdr i-look))
         ((v_int i))
         (result-look (assoc-equal "__stdlib_local_result" storage))
         (result (cdr result-look))
         ((v_int result))
         (x-look (assoc-equal "__stdlib_local_x" storage))
         (x (cdr x-look))
         ((v_bitvector x)))
      (implies (and i-look
                    (val-case i :v_int)
                    (equal i.val start)
                    result-look
                    (val-case result :v_int)
                    x-look
                    (val-case x :v_bitvector)
                    (equal result.val (logcount (loghead start x.val)))
                    
                    (natp clk)
                    (natp start)
                    (integerp end)
                    (<= start (+ 1 end))
                    (equal end (+ -1 x.len))
                    (no-duplicatesp-equal (acl2::alist-keys storage)))
               (b* (((mv (ev_normal res) &) (eval_for env "__stdlib_local_i" nil start :up end *BitCount-loop-body*))
                    ((continuing res.res))
                    (result-spec (v_int (logcount (loghead x.len x.val))))
                    ((env env))
                    ((local-env env.local)))
                 (and (equal res.res.env
                             (change-env env
                                         :local (change-local-env
                                                 env.local
                                                 :storage (put-assoc-equal "__stdlib_local_i"
                                                                           (v_int (+ 1 end))
                                                                           ;; (if (equal start (+ 1 end))
                                                                           ;;     env.local.storage
                                                                             (put-assoc-equal "__stdlib_local_result"
                                                                                              result-spec
                                                                                              env.local.storage)))))
                      (equal (eval_result-kind res) :ev_normal)
                      (equal (control_flow_state-kind res.res) :continuing)))))
    :hints (("goal" :induct (for-induct env "__stdlib_local_i" start :up end *BitCount-loop-body* clk nil orac)
             :in-theory (enable check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                eval_for_step
                                for_loop-step
                                FOR_LOOP-TEST
                                pop_scope
                                check-bad-slices
                                check_non_overlapping_slices
                                check_non_overlapping_slices-1
                                slices_sub
                                slices-width
                                write_to_bitvector
                                write_to_bitvector-aux
                                vbv-to-int)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((:free (end)
                             (eval_for env "__stdlib_local_i"
                                       nil
                                       (V_INT->VAL
                                        (CDR (HONS-ASSOC-EQUAL "__stdlib_local_i"
                                                               (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))
                                       :up end *BitCount-loop-body*))
                            (:free (end)
                             (eval_for env "__stdlib_local_i" nil end :up end *BitCount-loop-body*))
                            (:free (env end)
                             (eval_for env "__stdlib_local_i" nil (+ 1 end) :up end *BitCount-loop-body*))
                            (:free (env end)
                             (eval_for env "__stdlib_local_i" nil end :up (+ -1 end) *BitCount-loop-body*)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable equal-when-v_int)))
            )))


(defsection BitCount-correct

  (local (defthm logcount-loghead-bound
           (<= (logcount (loghead n x)) (nfix n))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-inductions
                                                    bitops::ihsext-recursive-redefs)))
           :rule-classes :linear))
  
  (defthm BitCount-correct
    (implies (and (subprograms-match '("BitCount")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (not (negp n))
                  (natp clk)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "BitCount"
                                               (list (v_int n))
                                               (list (v_bitvector n x)) :clk clk))
                    (ev_normal (func_result (list (v_int (logcount (loghead n (nfix x)))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "BitCount"
                                               (list (v_int n))
                                               (list (v_bitvector n x)) :clk clk))
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int
                                slices_sub))
             :do-not-induct t))))



(defsection LowestSetBit-loop
  
  (defconst *LowestSetBit-loop*
    (find-nth-form 0 :s_for (assoc-equal "LowestSetBit" (static_env_global->subprograms
                                                         (stdlib-static-env)))))

  (defconst *LowestSetBit-loop-body*
    (s_for->body *LowestSetBit-loop*))

  (local (defthm loghead-equal-0-when-not-logbitp
           (implies (and (not (logbitp n x))
                         (not (negp n)))
                    (equal (equal (loghead (+ 1 n) x) 0)
                           (equal (loghead n x) 0)))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-recursive-redefs
                                                    bitops::ihsext-inductions)))))

  (local (defthm trailing-0-count-when-logbitp
           (implies (and (logbitp n x)
                         (equal (loghead n x) 0))
                    (equal (bitops::trailing-0-count x) (nfix n)))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-recursive-redefs
                                                    bitops::trailing-0-count
                                                    bitops::ihsext-inductions)))))
  (defthm LowestSetBit-loop-correct
    (b* ((storage (local-env->storage
                   (env->local env)))
         (i-look (assoc-equal "__stdlib_local_i" storage))
         (i (cdr i-look))
         ((v_int i))
         (x-look (assoc-equal "__stdlib_local_x" storage))
         (x (cdr x-look))
         ((v_bitvector x))
         (n-look (assoc-equal "__stdlib_local_N" storage))
         (n (cdr n-look))
         ((v_int n)))
      (implies (and i-look
                    (val-case i :v_int)
                    (equal i.val start)
                    x-look
                    (val-case x :v_bitvector)
                    (equal (loghead i.val x.val) 0)
                    n-look
                    (val-case n :v_int)
                    (equal n.val x.len)
                    
                    (natp clk)
                    (natp start)
                    (integerp end)
                    (<= start (+ 1 end))
                    (equal end (+ -1 x.len))
                    (no-duplicatesp-equal (acl2::alist-keys storage)))
               (b* (((mv (ev_normal res) &) (eval_for env "__stdlib_local_i" nil start :up end *LowestSetBit-loop-body*))
                    ((env env))
                    ((local-env env.local)))
                 (and (equal (eval_result-kind res) :ev_normal)
                      (implies (equal 0 x.val)
                               (and (equal (control_flow_state-kind res.res) :continuing)
                                    (b* (((continuing res.res)))
                                      (equal res.res.env
                                             (change-env env
                                                         :local (change-local-env
                                                                 env.local
                                                                 :storage (put-assoc-equal "__stdlib_local_i"
                                                                                           (v_int (+ 1 end))
                                                                                           env.local.storage)))))))
                      (implies (not (equal 0 x.val))
                               (and (equal (control_flow_state-kind res.res) :returning)
                                    (b* (((returning res.res))
                                         (result-spec (v_int (bitops::trailing-0-count x.val))))
                                      (and (equal res.res.vals (list result-spec))
                                           (equal res.res.env env.global)))))))))
    :hints (("goal" :induct (for-induct env "__stdlib_local_i" start :up end *LowestSetBit-loop-body* clk nil orac)
             :in-theory (enable check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                eval_for_step
                                for_loop-step
                                FOR_LOOP-TEST
                                pop_scope
                                check-bad-slices
                                check_non_overlapping_slices
                                check_non_overlapping_slices-1
                                slices_sub
                                slices-width
                                write_to_bitvector
                                write_to_bitvector-aux
                                vbv-to-int)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((:free (end)
                             (eval_for env "__stdlib_local_i"
                                       nil
                                       (V_INT->VAL
                                        (CDR (HONS-ASSOC-EQUAL "__stdlib_local_i"
                                                               (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))
                                       :up end *LowestSetBit-loop-body*))
                            (:free (end)
                             (eval_for env "__stdlib_local_i" nil end :up end *LowestSetBit-loop-body*))
                            (:free (env end)
                             (eval_for env "__stdlib_local_i" nil (+ 1 end) :up end *LowestSetBit-loop-body*))
                            (:free (env end)
                             (eval_for env "__stdlib_local_i" nil end :up (+ -1 end) *LowestSetBit-loop-body*)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable equal-when-v_int)))
            )))




(defsection LowestSetBit-correct

  (local (defthm loghead-of-ifix-n
           (equal (loghead (ifix n) x)
                  (loghead n x))
           :hints(("Goal" :in-theory (enable ifix)))))

  (local (defthm trailing-0-count-of-loghead
           (implies (not (equal (loghead n x) 0))
                    (Equal (bitops::trailing-0-count (loghead n x))
                           (bitops::trailing-0-count x)))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-recursive-redefs
                                                    bitops::trailing-0-count
                                                    bitops::ihsext-inductions)))))

  
  (defthm LowestSetBit-correct
    (implies (and (subprograms-match '("LowestSetBit")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (not (negp n))
                  (natp clk)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "LowestSetBit"
                                               (list (v_int n))
                                               (list (v_bitvector n x)) :clk clk))
                    (ev_normal (func_result (list (v_int (if (eql (loghead n (nfix x)) 0)
                                                             (nfix n)
                                                           (bitops::trailing-0-count (nfix x)))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "LowestSetBit"
                                               (list (v_int n))
                                               (list (v_bitvector n x)) :clk clk))
             :rw-cache-state nil
             :cases ((eql (loghead n (nfix x)) 0))
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int
                                slices_sub))
             :do-not-induct t))))

(defsection LowestSetBitNZ-correct
  

  (local (defthm trailing-0-count-bound
           (implies (not (equal (loghead n x) 0))
                    (< (bitops::trailing-0-count x) (nfix n)))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-recursive-redefs
                                                    bitops::trailing-0-count
                                                    bitops::ihsext-inductions)))
           :rule-classes :linear))
  
  (defthm LowestSetBitNZ-correct
    (implies (and (subprograms-match '("LowestSetBitNZ" "LowestSetBit" "IsZero" "Zeros-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (natp n)
                  (<= 2 (nfix clk))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (let ((res (mv-nth 0 (eval_subprogram env "LowestSetBitNZ"
                                                   (list (v_int n))
                                                   (list (v_bitvector n x)) :clk clk))))
               (and (implies (equal (loghead n (nfix x)) 0)
                             (equal (eval_result-kind res) :ev_error))
                    (implies (not (equal (loghead n (nfix x)) 0))
                             (equal res
                                    (ev_normal (func_result (list (v_int (bitops::trailing-0-count (nfix x))))
                                                            (env->global env))))))))
    :hints (("goal" :expand ((eval_subprogram env "LowestSetBitNZ"
                                               (list (v_int n))
                                               (list (v_bitvector n x)) :clk clk))
             :rw-cache-state nil
             :cases ((eql (loghead n (nfix x)) 0))
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int
                                slices_sub))
             :do-not-induct t))))



(defsection HighestSetBit-loop
  
  (defconst *HighestSetBit-loop*
    (find-nth-form 0 :s_for (assoc-equal "HighestSetBit" (static_env_global->subprograms
                                                         (stdlib-static-env)))))

  (defconst *HighestSetBit-loop-body*
    (s_for->body *HighestSetBit-loop*))


  (local (defthm logtail-n-in-terms-of-logbitp
           (implies (equal (logtail (+ 1 n) x) 0)
                    (equal (equal (logtail n x) 0)
                           (not (logbitp n x))))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-inductions
                                                    bitops::ihsext-recursive-redefs)))))

  (local (defthm integer-length-when-logtail-logbitp
           (implies (and (equal (logtail (+ 1 n) x) 0)
                         (logbitp n x)
                         (natp n))
                    (equal (integer-length x) (+ 1 n)))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-inductions
                                                    bitops::ihsext-recursive-redefs)))))
           

  (defthm HighestSetBit-loop-correct
    (b* ((storage (local-env->storage
                   (env->local env)))
         (i-look (assoc-equal "__stdlib_local_i" storage))
         (i (cdr i-look))
         ((v_int i))
         (x-look (assoc-equal "__stdlib_local_x" storage))
         (x (cdr x-look))
         ((v_bitvector x))
         (n-look (assoc-equal "__stdlib_local_N" storage))
         (n (cdr n-look))
         ((v_int n)))
      (implies (and i-look
                    (val-case i :v_int)
                    (equal i.val start)
                    x-look
                    (val-case x :v_bitvector)
                    (equal (logtail (+ 1 i.val) x.val) 0)
                    n-look
                    (val-case n :v_int)
                    (equal n.val x.len)
                    
                    (natp clk)
                    (integerp start)
                    (equal end 0)
                    (>= start (+ -1 end))
                    (< start n.val)
                    (no-duplicatesp-equal (acl2::alist-keys storage)))
               (b* (((mv (ev_normal res) &) (eval_for env "__stdlib_local_i" nil start :down end *HighestSetBit-loop-body*))
                    ((env env))
                    ((local-env env.local)))
                 (and (equal (eval_result-kind res) :ev_normal)
                      (implies (equal 0 x.val)
                               (and (equal (control_flow_state-kind res.res) :continuing)
                                    (b* (((continuing res.res)))
                                      (equal res.res.env
                                             (change-env env
                                                         :local (change-local-env
                                                                 env.local
                                                                 :storage (put-assoc-equal "__stdlib_local_i"
                                                                                           (v_int (+ -1 end))
                                                                                           env.local.storage)))))))
                      (implies (not (equal 0 x.val))
                               (and (equal (control_flow_state-kind res.res) :returning)
                                    (b* (((returning res.res))
                                         (result-spec (v_int (1- (integer-length x.val)))))
                                      (and (equal res.res.vals (list result-spec))
                                           (equal res.res.env env.global)))))))))
    :hints (("goal" :induct (for-induct env "__stdlib_local_i" start :down end *HighestSetBit-loop-body* clk nil orac)
             :in-theory (enable check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                eval_for_step
                                for_loop-step
                                FOR_LOOP-TEST
                                pop_scope
                                check-bad-slices
                                check_non_overlapping_slices
                                check_non_overlapping_slices-1
                                slices_sub
                                slices-width
                                write_to_bitvector
                                write_to_bitvector-aux
                                vbv-to-int)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((:free (end)
                             (eval_for env "__stdlib_local_i"
                                       nil
                                       (V_INT->VAL
                                        (CDR (HONS-ASSOC-EQUAL "__stdlib_local_i"
                                                               (LOCAL-ENV->STORAGE (ENV->LOCAL ENV)))))
                                       :down 0 *HighestSetBit-loop-body*)) 
                            (:free (env end)
                             (eval_for env "__stdlib_local_i" nil -1 :down 0 *HighestSetBit-loop-body*)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable equal-when-v_int)))
            )))


(defsection HighestSetBit-correct


  (local (defthm loghead-of-ifix-n
           (equal (loghead (ifix n) x)
                  (loghead n x))
           :hints(("Goal" :in-theory (enable ifix)))))
  
  (defthm HighestSetBit-correct
    (implies (and (subprograms-match '("HighestSetBit")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (not (negp n))
                  (natp clk)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "HighestSetBit"
                                               (list (v_int n))
                                               (list (v_bitvector n x)) :clk clk))
                    (ev_normal (func_result (list (v_int (+ -1 (integer-length (loghead n (nfix x))))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "HighestSetBit"
                                               (list (v_int n))
                                               (list (v_bitvector n x)) :clk clk))
             :rw-cache-state nil
             :cases ((eql (loghead n (nfix x)) 0))
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int
                                slices_sub))
             :do-not-induct t))))


(defsection HighestSetBitNZ-correct

  (local (defthm integer-length-equal-0
           (implies (natp x)
                    (equal (equal (integer-length x) 0)
                           (equal x 0)))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-recursive-redefs
                                                    bitops::ihsext-inductions)))))
  
  (defthm HighestSetBitNZ-correct
    (implies (and (subprograms-match '("HighestSetBitNZ" "HighestSetBit" "IsZero" "Zeros-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (natp n)
                  (<= 2 (nfix clk))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (let ((res (mv-nth 0 (eval_subprogram env "HighestSetBitNZ"
                                                   (list (v_int n))
                                                   (list (v_bitvector n x)) :clk clk))))
               (and (implies (equal (loghead n (nfix x)) 0)
                             (equal (eval_result-kind res) :ev_error))
                    (implies (not (equal (loghead n (nfix x)) 0))
                             (equal res
                                    (ev_normal (func_result (list (v_int (1- (integer-length (loghead n (nfix x))))))
                                                            (env->global env))))))))
    :hints (("goal" :expand ((eval_subprogram env "HighestSetBitNZ"
                                               (list (v_int n))
                                               (list (v_bitvector n x)) :clk clk))
             :rw-cache-state nil
             :cases ((eql (loghead n (nfix x)) 0))
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int
                                slices_sub))
             :do-not-induct t))))


(defsection SignExtend-1-correct

  (local (defthm integer-length-equal-0
           (implies (natp x)
                    (equal (equal (integer-length x) 0)
                           (equal x 0)))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-recursive-redefs
                                                    bitops::ihsext-inductions)))))

  (local (defthm logrepeat-1
           (equal (logrepeat n 1 1)
                  (loghead n -1))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-recursive-redefs
                                                    bitops::ihsext-inductions
                                                    logrepeat)))))

  (local (defthm logapp-when-logbitp
           (implies (and (logbitp m x)
                         (natp m)
                         (posp n))
                    (equal (logapp m x (loghead n -1))
                           (logapp (+ 1 m) x (loghead (+ -1 n) -1))))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-recursive-redefs
                                                    bitops::ihsext-inductions)))))

  (local (defthm logrepeat-0
           (equal (logrepeat m n 0) 0)
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-recursive-redefs
                                                    bitops::ihsext-inductions
                                                    logrepeat)))))

  (local (defthm loghead-when-not-logbitp
           (implies (and (not (logbitp (+ -1 m) x))
                         (natp m))
                    (equal (loghead (+ -1 m) x)
                           (loghead m x)))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-recursive-redefs
                                                    bitops::ihsext-inductions)))))
           
  
  (defthm SignExtend-1-correct
    (implies (and (subprograms-match '("SignExtend-1" "Replicate-1" "Zeros-1" "Ones-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (posp m)
                  (integerp n)
                  (<= m n)
                  (<= 3 (nfix clk))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "SignExtend-1"
                                               (list (v_int n) (v_int m))
                                               (list (v_bitvector m x)) :clk clk))
                    (ev_normal (func_result (list (v_bitvector n (loghead n (logext m (nfix x)))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "SignExtend-1"
                                                   (list (v_int n) (v_int m))
                                                   (list (v_bitvector m x)) :clk clk))
             :rw-cache-state nil
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int
                                slices_sub
                                check-bad-slices
                                logext))
             :do-not-induct t))))


(defsection SignExtend-correct
           
  
  (defthm SignExtend-correct
    (implies (and (subprograms-match '("SignExtend" "SignExtend-1" "Replicate-1" "Zeros-1" "Ones-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (posp m)
                  (integerp n)
                  (<= m n)
                  (<= 4 (nfix clk))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "SignExtend"
                                               (list (v_int n) (v_int m))
                                               (list (v_bitvector m x) (v_int n)) :clk clk))
                    (ev_normal (func_result (list (v_bitvector n (loghead n (logext m (nfix x)))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "SignExtend"
                                                   (list (v_int n) (v_int m))
                                                   (list (v_bitvector m x) (v_int n))
                                                   :clk clk))
             :rw-cache-state nil
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int
                                slices_sub
                                check-bad-slices
                                logext))
             :do-not-induct t))))


(defsection Extend-1-correct
           
  
  (defthm Extend-1-correct
    (implies (and (subprograms-match '("Extend-1" "SignExtend-1" "ZeroExtend-1" "Replicate-1" "Zeros-1" "Ones-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (posp m)
                  (integerp n)
                  (<= m n)
                  (<= 5 (nfix clk))
                  (val-case ub :v_bool)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "Extend-1"
                                               (list (v_int n) (v_int m))
                                               (list (v_bitvector m x) ub) :clk clk))
                    (ev_normal (func_result (list (v_bitvector n
                                                               (if (v_bool->val ub)
                                                                   (loghead m (nfix x))
                                                                 (loghead n (logext m (nfix x))))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "Extend-1"
                                                   (list (v_int n) (v_int m))
                                                   (list (v_bitvector m x) ub)
                                                   :clk clk))
             :rw-cache-state nil
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int
                                slices_sub
                                check-bad-slices
                                logext))
             :do-not-induct t))))


(defsection Extend-correct
           
  
  (defthm Extend-correct
    (implies (and (subprograms-match '("Extend" "Extend-1" "SignExtend-1" "ZeroExtend-1" "Replicate-1" "Zeros-1" "Ones-1")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (posp m)
                  (integerp n)
                  (<= m n)
                  (<= 6 (nfix clk))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "Extend"
                                               (list (v_int n) (v_int m))
                                               (list (v_bitvector m x) (v_int n) (v_bool unsigned)) :clk clk))
                    (ev_normal (func_result (list (v_bitvector n
                                                               (if unsigned
                                                                   (loghead m (nfix x))
                                                                 (loghead n (logext m (nfix x))))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "Extend"
                                                   (list (v_int n) (v_int m))
                                                   (list (v_bitvector m x) (v_int n) (v_bool unsigned))
                                                   :clk clk))
             :rw-cache-state nil
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int
                                slices_sub
                                check-bad-slices
                                logext))
             :do-not-induct t))))







(defsection CountLeadingZeroBits-correct
  
  (defthm CountLeadingZeroBits-correct
    (implies (and (subprograms-match '("CountLeadingZeroBits" "HighestSetBit")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (not (negp n))
                  (posp clk)
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "CountLeadingZeroBits"
                                               (list (v_int n))
                                               (list (v_bitvector n x)) :clk clk))
                    (ev_normal (func_result (list (v_int (- (ifix n) (integer-length (loghead n (nfix x))))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "CountLeadingZeroBits"
                                               (list (v_int n))
                                               (list (v_bitvector n x)) :clk clk))
             :rw-cache-state nil
             :cases ((eql (loghead n (nfix x)) 0))
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int
                                slices_sub))
             :do-not-induct t))))


;; NOTE: This seems intentional, but note the difference between the specs of
;; CountLeadingZeroBits and CountLeadingSignBits: the former counts all the
;; zeros leading up to the most significant 1 bit, whereas the latter counts
;; the leading 0s/1s except for the sign bit.
(defsection CountLeadingSignBits-correct

  (local (defthm integer-length-equal-0
           (implies (natp x)
                    (equal (equal (integer-length x) 0)
                           (equal x 0)))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-recursive-redefs
                                                    bitops::ihsext-inductions)))))


  (local (defthm integer-length-logxor
           (implies (posp n)
                    (equal (integer-length (logxor (loghead (+ -1 n) x)
                                                   (loghead (+ -1 n) (logtail 1 x))))
                           (integer-length (logext n x))))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-inductions
                                                    bitops::ihsext-recursive-redefs)))))

  (local (defthm logext-when-loghead-0
           (implies (and (equal (loghead n x) 0)
                         (posp n))
                    (Equal (logext n x) 0))
           :hints(("Goal" :in-theory (acl2::enable* bitops::ihsext-inductions
                                                    bitops::ihsext-recursive-redefs)))))
  
  (defthm CountLeadingSignBits-correct
    (implies (and (subprograms-match '("CountLeadingSignBits" "CountLeadingZeroBits" "HighestSetBit")
                                     (global-env->static (env->global env))
                                     (stdlib-static-env))
                  (posp n)
                  (<= 2 (nfix clk))
                  (no-duplicatesp-equal (acl2::alist-keys (global-env->stack_size
                                                           (env->global env)))))
             (equal (mv-nth 0 (eval_subprogram env "CountLeadingSignBits"
                                               (list (v_int n))
                                               (list (v_bitvector n x)) :clk clk))
                    (ev_normal (func_result (list (v_int (- (ifix n) (+ 1 (integer-length (logext n (nfix x)))))))
                                            (env->global env)))))
    :hints (("goal" :expand ((eval_subprogram env "CountLeadingSignBits"
                                               (list (v_int n))
                                               (list (v_bitvector n x)) :clk clk))
             :rw-cache-state nil
             :cases ((eql (loghead n (nfix x)) 0))
             :in-theory (e/d (check_recurse_limit
                                declare_local_identifiers
                                declare_local_identifier
                                remove_local_identifier
                                env-find
                                env-assign
                                env-assign-local
                                env-assign-global
                                env-push-stack
                                env-pop-stack
                                v_to_int
                                slices_sub
                                check-bad-slices))
             :do-not-induct t))))

