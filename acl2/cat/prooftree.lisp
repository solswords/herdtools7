
(in-package "CAT")


(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)

(local (table fty::deftagsum-defaults :short-names t))
(local (std::add-default-post-define-hook :fix))
(deftypes set-rel
  (deftagsum setex
    (:emptyset ())
    (:univset  ())
    (:setvar   ((name symbolp)))
    (:singleton ((e symbolp)))
    (:setunion ((s1 setex)
                (s2 setex)))
    (:setintersect ((s1 setex)
                    (s2 setex)))
    (:setimage     ((s setex)
                    (r relex)))
    (:setpreimage  ((r relex)
                    (s setex))))
  (deftagsum relex
    (:relvar   ((name symbolp)))
    (:relsetid ((s setex)))
    (:relunion ((r1 relex)
                (r2 relex)))
    (:relintersect ((r1 relex)
                    (r2 relex)))
    (:relcompose ((r1 relex)
                  (r2 relex)))
    (:relstar  ((r relex)))
    (:relinverse ((r relex)))
    (:relprod ((s1 setex)
               (s2 setex)))))

(encapsulate
  (((univ) => * :guard t :formals nil))

  (local (defun univ ()
           (declare (xargs :guard t))
           '(t)))

  (defthm setp-of-univ
    (setp (univ)))

  (defthm not-emptyp-of-univ
    (not (emptyp (univ)))))

(define evt-p (x)
  (in x (univ)))

(define evt-default ()
  :returns (evt evt-p)
  :prepwork ((local (in-theory (enable evt-p))))
  (head (univ))
  ///
  (in-theory (disable (evt-default))))

(define evt-fix ((x evt-p))
  :returns (fix evt-p)
  (mbe :logic 
       (if (evt-p x) x (evt-default))
       :exec x)
  ///
  (defret evt-fix-when-evt-p
    (implies (evt-p x)
             (equal (evt-fix x) x)))

  (fty::deffixtype evt :pred evt-p :fix evt-fix
    :equiv evt-equiv :define t :forward t)

  (in-theory (disable (evt-fix))))


(include-book "kestrel/fty/set" :dir :system)
(include-book "kestrel/fty/map" :dir :system)

(fty::defset evtset :elt-type evt
  ///
  (local (defthmd evtset-p-redef
           (iff (evtset-p x)
                (and (setp x)
                     (if (emptyp x)
                         t
                       (and (evt-p (head x))
                            (evtset-p (tail x))))))
           :hints(("Goal" :in-theory (enable evtset-p setp emptyp head tail)))
           :rule-classes ((:definition :controller-alist ((evtset-p t))))))
  (local (defthm evtset-p-of-univ-lemma
           (implies (and (setp x)
                         (subset x (univ)))
                    (evtset-p x))
           :hints(("Goal" :in-theory (enable evtset-p-redef evt-p subset)))))
  (defthm evtset-p-of-univ
    (evtset-p (univ)))
  (defthm subset-of-univ
    (implies (evtset-p x)
             (subset x (univ)))
    :hints(("Goal" :in-theory (enable evtset-p-redef subset evt-p)))))

(defprod pair ((from evt) (to evt)) :layout :list)
(fty::deflist pairlist :elt-type pair :true-listp t)
(fty::defset evtrel :elt-type pair)

(fty::defmap evt-env :key-type symbolp :val-type evt :true-listp t)

(fty::defmap set-env :key-type symbolp :val-type evtset :true-listp t)
(fty::defmap rel-env :key-type symbolp :val-type evtrel :true-listp t)

(fty::defprod env
  ((evts evt-env)
   (sets set-env)
   (rels rel-env)))

(define evt-lookup ((name symbolp) (env env-p))
  :returns (lookup evt-p)
  (b* (((env env))
       (look (hons-assoc-equal (mbe :logic (acl2::symbol-fix name) :exec name)
                               env.evts)))
    (if look
        (cdr look)
      (evt-default))))

;; (define in-set ((e evt-p) (s evtset-p))
;;   (in (evt-fix e) (evtset-fix s)))

;; (define in-rel ((e1 evt-p) (e2 evt-p) (r evtrel-p))
;;   (in (pair e1 e2) (evtrel-fix r)))

(define image ((s evtset-p) (r evtrel-p))
  :returns (im evtset-p)
  :prepwork ((local (in-theory (enable evtset-p))))
  :measure (acl2-count (evtrel-fix r))
  :verify-guards nil
  (b* ((r (evtrel-fix r)))
    (b* (((when (emptyp r)) nil)
         ((pair x) (head r))
         (rest (image s (tail r))))
      (if (in x.from (evtset-fix s))
          (insert x.to rest)
        rest)))
  ///
  (verify-guards image)
  (defret in-of-image-suff
    (implies (and (in (pair w v) (evtrel-fix r))
                  (in w (evtset-fix s))
                  (evt-p v))
             (in v im)))

  (defret in-of-image-suff2
    (implies (and (in w (evtset-fix s))
                  (in (pair w v) (evtrel-fix r))
                  (evt-p v))
             (in v im))))

(define image-witness ((v evt-p) (s evtset-p) (r evtrel-p))
  :returns (w (implies w (evt-p w)))
  :measure (acl2-count (evtrel-fix r))
  :verify-guards nil
  (b* ((r (evtrel-fix r)))
    (b* (((when (emptyp r)) nil)
         ((pair x) (head r))
         ((when (and (equal x.to (evt-fix v))
                     (in x.from (evtset-fix s))))
          x.from))
      (image-witness v s (tail r))))
  ///
  (verify-guards image-witness)
  
  (defret image-witness-when-in-image
    (implies (in v (image s r))
             (and (in w (evtset-fix s))
                  (in (pair w v) (evtrel-fix r))))
    :hints(("Goal" :in-theory (enable image))))

  (defret evt-p-image-witness-when-in-image
    (implies (in v (image s r))
             (evt-p w))
    :hints(("Goal" :in-theory (enable image))))

  (defretd in-of-image-rw
    (implies (and (acl2::rewriting-negative-literal `(in ,v (image ,s ,r))))
             (iff (in v (image s r))
                  (and (evt-p v)
                       (in w (evtset-fix s))
                       (in (pair w v) (evtrel-fix r)))))
    :hints(("Goal" :in-theory (e/d ()
                                   (image-witness))))))

(define preimage ((s evtset-p) (r evtrel-p))
  :returns (im evtset-p)
  :prepwork ((local (in-theory (enable evtset-p))))
  :measure (acl2-count (evtrel-fix r))
  :verify-guards nil
  (b* ((r (evtrel-fix r)))
    (b* (((when (emptyp r)) nil)
         ((pair x) (head r))
         (rest (preimage s (tail r))))
      (if (in x.to (evtset-fix s))
          (insert x.from rest)
        rest)))
  ///
  (verify-guards preimage)
  
  (defret in-of-preimage-suff
    (implies (and (in (pair v w) (evtrel-fix r))
                  (in w (evtset-fix s))
                  (evt-p v))
             (in v im)))
  
  (defret in-of-preimage-suff2
    (implies (and (in w (evtset-fix s))
                  (in (pair v w) (evtrel-fix r))
                  (evt-p v))
             (in v im))))

(define preimage-witness ((v evt-p) (s evtset-p) (r evtrel-p))
  :returns (w (implies w (evt-p w)))
  :measure (acl2-count (evtrel-fix r))
  :verify-guards nil
  (b* ((r (evtrel-fix r)))
    (b* (((when (emptyp r)) nil)
         ((pair x) (head r))
         ((when (and (equal x.from (evt-fix v))
                     (in x.to (evtset-fix s))))
          x.to))
      (preimage-witness v s (tail r))))
  ///
  (verify-guards preimage-witness)
  
  (defret preimage-witness-when-in-preimage
    (implies (in v (preimage s r))
             (and (in w (evtset-fix s))
                  (in (pair v w) (evtrel-fix r))))
    :hints(("Goal" :in-theory (enable preimage))))

  (defret evt-p-preimage-witness-when-in-preimage
    (implies (in v (preimage s r))
             (evt-p w))
    :hints(("Goal" :in-theory (enable preimage))))

  (defretd in-of-preimage-rw
    (implies (and (acl2::rewriting-negative-literal `(in ,v (preimage ,s ,r))))
             (iff (in v (preimage s r))
                  (and (evt-p v)
                       (in w (evtset-fix s))
                       (in (pair v w) (evtrel-fix r)))))
    :hints(("Goal" :in-theory (e/d ()
                                   (preimage-witness))))))

(define to-id ((s evtset-p))
  :returns (id evtrel-p)
  :verify-guards nil
  :measure (acl2-count (evtset-fix s))
  (b* ((s (evtset-fix s)))
    (if (emptyp s)
        nil
      (insert (pair (head s) (head s))
              (to-id (tail s)))))
  ///
  (verify-guards to-id)
  
  (defret in-of-to-id
    (iff (in pair (to-id s))
         (and (pair-p pair)
              (equal (pair->from pair) (pair->to pair))
              (in (pair->from pair) (evtset-fix s))))))


;; For any pair (dst, dst2) in x, includes (src, dst2) in result.
(define compose1 ((src evt-p)
                  (dst evt-p)
                  (x evtrel-p))
  :returns (compose pairlist-p)
  :measure (acl2-count (evtrel-fix x))
  (b* ((x (evtrel-fix x)))
    (if (emptyp x)
        nil
      (if (equal (evt-fix dst) (pair->from (head x)))
          (cons (pair src (pair->to (head x)))
                (compose1 src dst (tail x)))
        (compose1 src dst (tail x)))))
  ///
  (defretd member-of-<fn>
    (iff (member-equal pair compose)
         (and (pair-p pair)
              (equal (pair->from pair) (evt-fix src))
              (in (pair dst (pair->to pair))
                  (evtrel-fix x))))
    :hints(("Goal" :in-theory (enable in)))))

(defthm evtrel-p-of-sort-pairlist
  (implies (pairlist-p x)
           (evtrel-p (mergesort x)))
  :hints(("Goal" :in-theory (enable mergesort))))

(define compose ((x evtrel-p)
                 (y evtrel-p))
  :returns (compose evtrel-p)
  :measure (acl2-count (evtrel-fix x))
  :verify-guards nil
  (b* ((x (evtrel-fix x)))
    (if (emptyp x)
      nil
      (union (mergesort (compose1 (pair->from (head x))
                                  (pair->to (head x))
                                  y))
             (compose (tail x) y))))
  ///
  (verify-guards compose)
  (defretd in-of-compose-suff
    (implies (and (pair-p pair)
                  (in (pair (pair->from pair) mid) (evtrel-fix x))
                  (in (pair mid (pair->to pair)) (evtrel-fix y)))
             (in pair compose))
    :hints(("Goal" :in-theory (enable member-of-compose1))))

  (defretd in-of-compose-suff-rw
    (implies (and (in (pair src mid) (evtrel-fix x))
                  (in (pair mid dst) (evtrel-fix y)))
             (in (pair src dst) compose))
    :hints(("Goal" :in-theory (enable member-of-compose1))))

  (defretd in-of-compose-suff-rw2
    (implies (and (in (pair mid dst) (evtrel-fix y))
                  (in (pair src mid) (evtrel-fix x)))
             (in (pair src dst) compose))
    :hints(("Goal" :in-theory (enable in-of-compose-suff-rw)))))

(local (defthm member-equal-when-evtrel-p
         (implies (evtrel-p x)
                  (iff (member-equal k x)
                       (in k x)))
         :hints(("Goal" :in-theory (enable set::in-to-member)))))

(local (include-book "std/util/termhints" :dir :system))

(define compose-midpoint ((src evt-p)
                          (dst evt-p)
                          (x evtrel-p)
                          (y evtrel-p))
  :returns (mid (implies mid (evt-p mid)))
  :measure (acl2-count (evtrel-fix x))
  ;; Witness for compose membership. If (src . dst) are in the composition of x
  ;; and y, then (compose-midpoint src dst x y) produces mid such that (src
  ;; . mid) is in x and (mid . dst) is in y.
  (b* ((x (evtrel-fix x)))
    (if (emptyp x)
        nil
      (if (and (equal (evt-fix src) (pair->from (head x)))
               (in (pair (pair->to (head x)) dst)
                   (evtrel-fix y)))
          (evt-fix (pair->to (head x)))
        (compose-midpoint src dst (tail x) y))))
  ///
  ;; (local (defthm member-cons-evtrel
  ;;          (implies (And (evtrel-p y)
  ;;                        (not (and (evt-p dst)
  ;;                                  (evt-p src))))
  ;;                   (not (member-equal (cons src dst) y)))))

  ;; (local (defthm member-evtrel-not-consp
  ;;          (implies (And (evtrel-p y)
  ;;                        (not (pair-p pair)))
  ;;                   (not (member-equal pair y)))))

  (defret compose-midpoint-when-in-compose
    (implies (in (pair src dst) (compose x y))
             (and (in (pair src mid) (evtrel-fix x))
                  (in (pair mid dst) (evtrel-fix y))))
    :hints(("Goal" :in-theory (enable compose
                                      member-of-compose1)
            :induct <call>
            :expand (<call>
                     (compose x y)
                     (:Free (pair) (in pair (evtrel-fix x)))))))

  (defret evt-p-of-<fn>-when-in-compose
    (implies (in (pair src dst) (compose x y))
             (evt-p mid))
    :hints(("Goal" :in-theory (enable compose
                                      member-of-compose1)
            :induct <call>
            :expand (<call>
                     (compose x y)))))
  
  (defret compose-midpoint-witnesses
    (implies (and (in (pair src mid1) (evtrel-fix x))
                  (in (pair mid1 dst) (evtrel-fix y)))
             (and (in (pair src mid) (evtrel-fix x))
                  (in (pair mid dst) (evtrel-fix y))))
    :hints (("goal" :use ((:instance in-of-compose-suff
                           (pair (pair src dst)) (mid mid1)))
             :in-theory (disable in-of-compose-suff)))
    :otf-flg t)

  (defretd in-of-compose-necc
    :pre-bind ((src (pair->from pair))
               (dst (pair->to pair)))
    (implies (not (and (in (pair (pair->from pair) mid) (evtrel-fix x))
                       (in (pair mid (pair->to pair)) (evtrel-fix y))))
             (not (in pair (compose x y))))
    :hints(("Goal" :in-theory (enable compose
                                      in
                                      in-of-compose-suff
                                      member-of-compose1)
            :cases ((and (evt-p (pair->from pair)) (evt-p (pair->to pair))))))
    :otf-flg t)

  (fty::deffixequiv compose-midpoint)
  
  (defretd in-of-compose-implies-fix
    :pre-bind ((pair (pair src dst)))
    (implies (and (in pair (compose x y)))
             (and (in (pair src mid) (evtrel-fix x))
                  (in (pair mid dst) (evtrel-fix y))))
    :hints(("Goal" :use ((:instance in-of-compose-necc
                          (pair (pair src dst)))))))
  
  (defretd in-of-compose-implies
    :pre-bind ((pair (pair src dst)))
    (implies (and (in pair (compose x y)))
             (and (implies (evtrel-p x)
                           (in (pair src mid) x))
                  (implies (evtrel-p y)
                           (in (pair mid dst) y))))
    :hints(("Goal" :use ((:instance in-of-compose-necc
                          (pair (pair src dst)))))))
                         
  (defretd in-of-compose
    :pre-bind ((src (pair->from pair))
               (dst (pair->to pair)))
    (iff (in pair (compose x y))
         (and (pair-p pair)
              (in (pair (pair->from pair) mid) (evtrel-fix x))
              (in (pair mid (pair->to pair)) (evtrel-fix y))))
    :hints(("Goal" :in-theory (enable in-of-compose-necc
                                      in-of-compose-suff))))

  (defretd in-of-compose-rw
    :pre-bind ((src (pair->from pair))
               (dst (pair->to pair)))
    (implies (acl2::rewriting-negative-literal `(in ,pair (compose ,x ,y)))
             (iff (in pair (compose x y))
                  (and (pair-p pair)
                       (in (pair (pair->from pair) mid) (evtrel-fix x))
                       (in (pair mid (pair->to pair)) (evtrel-fix y)))))
    :hints(("Goal" :in-theory (enable in-of-compose))))


  (defthm compose-associative
    (equal (compose (compose x y) z)
           (compose x (compose y z)))
    :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                      set::double-containment-no-backchain-limit))
           (SET::PICK-A-POINT-SUBSET-HINT ID acl2::CLAUSE
                                          WORLD STABLE-UNDER-SIMPLIFICATIONP)
           (and stable-under-simplificationp
                (acl2::use-termhint
                 (b* ((elem set::arbitrary-element)
                      ((pair elem)))
                   (if (in elem (compose (compose x y) z))
                       (b* ((step2 (compose-midpoint elem.from elem.to (compose x y) z))
                            (step1 (compose-midpoint elem.from step2 x y))
                            (pair1 (pair step1 elem.to)))
                         `(:use ((:instance acl2::mark-clause-is-true (x '(in elem (compose (compose x y) z))))
                                 (:instance in-of-compose-suff
                                  (x x) (y (compose y z))
                                  (pair ,(acl2::hq elem))
                                  (mid ,(acl2::hq step1)))
                                 (:instance in-of-compose-suff
                                  (x y) (y z)
                                  (pair ,(acl2::hq pair1))
                                  (mid ,(acl2::hq step2))))
                           :in-theory (enable in-of-compose-rw)))
                     (b* ((step1 (compose-midpoint elem.from elem.to x (compose y z)))
                          (step2 (compose-midpoint step1 elem.to y z))
                          (pair2 (pair elem.from step2)))
                       `(:use ((:instance acl2::mark-clause-is-true (x '(in elem (compose x (compose y z)))))
                               (:instance in-of-compose-suff
                                (x (compose x y)) (y z)
                                (pair ,(acl2::hq elem))
                                (mid ,(acl2::hq step2)))
                               (:instance in-of-compose-suff
                                (x x) (y y)
                                (pair ,(acl2::hq pair2))
                                (mid ,(acl2::hq step1))))
                         :in-theory (enable in-of-compose-rw))))))))))



(define cartesian1 ((x evt-p)
                    (y evtset-p))
  :returns (pairs evtrel-p)
  :measure (acl2-count (evtset-fix y))
  :verify-guards nil
  (b* ((y (evtset-fix y)))
    (if (emptyp y)
        nil
      (insert (pair x (head y))
              (cartesian1 x (tail y)))))
  ///
  (verify-guards cartesian1)
  
  (defretd in-of-<fn>
    (iff (in pair pairs)
         (and (pair-p pair)
              (Equal (pair->from pair) (evt-fix x))
              (in (pair->to pair) (evtset-fix y))))))

(define cartesian ((x evtset-p)
                   (y evtset-p))
  :returns (rel evtrel-p)
  :measure (acl2-count (evtset-fix x))
  :verify-guards nil
  (b* ((x (evtset-fix x)))
    (if (emptyp x)
        nil
      (union (cartesian1 (head x) y)
             (cartesian (tail x) y))))
  ///
  (verify-guards cartesian)
  (defretd in-of-<fn>
    (iff (in pair rel)
         (and (pair-p pair)
              (in (pair->from pair) (evtset-fix x))
              (in (pair->to pair) (evtset-fix y))))
    :hints(("Goal" :in-theory (enable in-of-cartesian1)))))


(define domain ((x evtrel-p))
  :returns (dom evtset-p)
  :measure (acl2-count (evtrel-fix x))
  :verify-guards nil
  (b* ((x (evtrel-fix x)))
    (if (emptyp x)
        nil
      (insert (pair->from (head x))
              (domain (tail x)))))
  ///
  (verify-guards domain)
  (defretd in-of-domain-suff
    (implies (and (in (pair src dst) (evtrel-fix x))
                  (evt-p src))
             (in src (domain x)))
    :hints(("Goal" :in-theory (enable in))))

  (defretd in-of-domain-suff-free
    (implies (and (in (pair src dst) some-rel)
                  (in (pair src dst) (evtrel-fix x))
                  (evt-p src))
             (in src (domain x)))
    :hints(("Goal" :in-theory (enable in-of-domain-suff))))

  (defret in-from-of-domain
    (implies (in pair (evtrel-fix x))
             (in (pair->from pair) dom))
    :hints(("Goal" :in-theory (enable in)))))

(define domain-witness ((src evt-p) (x evtrel-p))
  :returns (dst (implies dst (evt-p dst)))
  :measure (acl2-count (evtrel-fix x))
  (b* ((x (evtrel-fix x)))
    (if (emptyp x)
        nil
      (if (equal (evt-fix src) (pair->from (head x)))
          (pair->to (head x))
        (domain-witness src (tail x)))))
  ///

  (defret domain-witness-witnesses
    (implies (in (pair src dst1) (evtrel-fix x))
             (in (pair src dst) (evtrel-fix x)))
    :hints(("Goal" :in-theory (enable in))))
  
  (defretd in-of-domain-necc
    (implies (not (in (pair src dst) (evtrel-fix x)))
             (not (in src (domain x))))
    :hints(("Goal" :in-theory (enable domain in))))

  (defretd in-of-domain
    (iff (in src (domain x))
         (and (evt-p src)
              (in (pair src dst) (evtrel-fix x))))
    :hints(("Goal" :in-theory (enable in-of-domain-necc
                                      in-of-domain-suff
                                      domain)))
    :otf-flg t)

  (defretd in-of-domain-rw
    (implies (acl2::rewriting-negative-literal `(in ,src (domain ,x)))
             (iff (in src (domain x))
                  (and (evt-p src)
                       (in (pair src dst) (evtrel-fix x)))))
    :hints(("Goal" :in-theory (enable in-of-domain))))

  (defthm domain-of-union
    (implies (and (evtrel-p x)
                  (evtrel-p y))
             (equal (domain (union x y))
                    (union (domain x) (domain y))))
    :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                      pick-a-point-subset-strategy
                                      in-of-domain-rw
                                      in-of-domain-suff-free)))))


(define range ((x evtrel-p))
  :returns (range evtset-p)
  :measure (acl2-count (evtrel-fix x))
  :verify-guards nil
  (b* ((x (evtrel-fix x)))
    (if (emptyp x)
        nil
      (insert (pair->to (head x))
              (range (tail x)))))
  ///
  (verify-guards range)
  (defretd in-of-range-suff
    (implies (and (in (pair src dst) (evtrel-fix x))
                  (evt-p dst))
             (in dst (range x)))
    :hints(("Goal" :in-theory (enable in))))

  (defretd in-of-range-suff-free
    (implies (and (in (pair src dst) some-rel)
                  (in (pair src dst) (evtrel-fix x))
                  (evt-p dst))
             (in dst (range x)))
    :hints(("Goal" :in-theory (enable in-of-range-suff))))

  (defret in-to-of-range
    (implies (in pair (evtrel-fix x))
             (in (pair->to pair) range))
    :hints(("Goal" :in-theory (enable in)))))

(define range-witness ((dst evt-p) (x evtrel-p))
  :returns (src (implies src (evt-p src)))
  :measure (acl2-count (evtrel-fix x))
  (b* ((x (evtrel-fix x)))
    (if (emptyp x)
        nil
      (if (equal (evt-fix dst) (pair->to (head x)))
          (pair->from (head x))
        (range-witness dst (tail x)))))
  ///

  (defret range-witness-witnesses
    (implies (in (pair src1 dst) (evtrel-fix x))
             (in (pair src dst) (evtrel-fix x)))
    :hints(("Goal" :in-theory (enable in))))
  
  (defretd in-of-range-necc
    (implies (not (in (pair src dst) (evtrel-fix x)))
             (not (in dst (range x))))
    :hints(("Goal" :in-theory (enable range in))))

  (defretd in-of-range
    (iff (in dst (range x))
         (and (evt-p dst)
              (in (pair src dst) (evtrel-fix x))))
    :hints(("Goal" :in-theory (enable in-of-range-necc
                                      in-of-range-suff
                                      range)))
    :otf-flg t)

  (defretd in-of-range-rw
    (implies (acl2::rewriting-negative-literal `(in ,dst (range ,x)))
             (iff (in dst (range x))
                  (and (evt-p dst)
                       (in (pair src dst) (evtrel-fix x)))))
    :hints(("Goal" :in-theory (enable in-of-range))))

  (defthm range-of-union
    (implies (and (evtrel-p x)
                  (evtrel-p y))
             (equal (range (union x y))
                    (union (range x) (range y))))
    :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                      pick-a-point-subset-strategy
                                      in-of-range-rw
                                      in-of-range-suff-free)))))


(local
 (defsection transitive-closure-termination-argument

   (local (in-theory (enable pick-a-point-subset-strategy
                             set::double-containment-no-backchain-limit)))

   (defthm domain-of-compose
     (subset (domain (compose x y))
             (domain x))
     :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                       in-of-compose
                                       in-of-domain-rw
                                       in-of-domain-suff))))

   (defthm range-of-compose
     (subset (range (compose x y))
             (range y))
     :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                       in-of-compose
                                       in-of-range-rw
                                       in-of-range-suff))))

   (defthm subset-of-cartesian
     (implies (evtrel-p x)
              (subset x (cartesian (union (domain x) (range x))
                                   (union (domain x) (range x)))))
     :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                       in-of-cartesian))))

   (defthm cardinality-limited-by-cartesian
     (<= (cardinality (evtrel-fix x))
         (cardinality (cartesian (union (domain x) (range x))
                                 (union (domain x) (range x)))))
     :hints (("goal" :use ((:instance subset-of-cartesian
                            (x (evtrel-fix x))))
              :in-theory (disable subset-of-cartesian)))
     :rule-classes :linear)

   (defthm cardinality-of-union-increasing
     (implies (not (subset y x))
              (< (cardinality x)
                 (cardinality (union x y))))
     :hints (("goal" :use ((:instance set::proper-subset-cardinality
                            (x x) (y (union x y))))
              :in-theory (e/d (set::subset-in)
                              (set::proper-subset-cardinality))))
     :rule-classes :linear)

   (defthm union-of-subset
     (implies (subset x y)
              (equal (union y x) (sfix y)))
     :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                       set::subset-in
                                       set::double-containment-no-backchain-limit))))


   
   ;; (in-theory (disable acl2::commutativity-2-of-append-under-set-equiv
   ;;                     acl2::commutativity-of-append-under-set-equiv
   ;;                     set::expand-cardinality-of-union))
  
   ;; (defthm append-under-set-equiv-when-subsetp
   ;;   (implies (subsetp-equal y x)
   ;;            (acl2::set-equiv (append x y) x)))

   ;; (defthm append-under-set-equiv-when-subsetp-2
   ;;   (implies (subsetp-equal y x)
   ;;            (acl2::set-equiv (append x y z) (append x z)))
   ;;   :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw))))
   ))



(define transitive-closure ((x evtrel-p))
  :measure (- (cardinality (cartesian (union (domain x) (range x))
                                      (union (domain x) (range x))))
              (cardinality (evtrel-fix x)))
  :hints(("Goal" :in-theory (disable set::expand-cardinality-of-union)))
  :returns (closure evtrel-p)
  (b* ((comp (compose x x))
       (x (evtrel-fix x))
       ((when (subset comp x))
        x))
    (transitive-closure (union x comp)))
  ///

  (defret transitive-closure-is-superset
    (subset (evtrel-fix x) (transitive-closure x))
    :hints(("Goal" :in-theory (enable set::subset-transitive))))

  (defret transitive-closure-is-closed
    (subset (compose closure closure) closure)))


(fty::deflist evtlist :elt-type evt :true-listp t)

(define evtrel-path-p ((path evtlist-p)
                       (x evtrel-p))
  (if (atom (cdr path))
      nil
    (and (in (pair (car path) (cadr path))
             (evtrel-fix x))
         (or (atom (cddr path))
             (evtrel-path-p (cdr path) x))))
  ///
  (defthm evtrel-path-p-of-compose
    (implies (and (evtrel-path-p a x)
                  (evtrel-path-p b x)
                  (equal (evt-fix (car b))
                         (evt-fix (car (last a)))))
             (evtrel-path-p (append a (cdr b)) x)))

  (defthmd evtrel-path-p-when-subset
    (implies (and (subset (evtrel-fix x)
                          (evtrel-fix y))
                  (evtrel-path-p path x))
             (evtrel-path-p path y))
    :hints(("Goal" :in-theory (enable evtrel-path-p
                                      set::subset-in))))
  
  (local (in-theory (enable evtlist-fix))))



(define transitive-path-aux ((path evtlist-p)
                             (x evtrel-p))
  :guard (evtrel-path-p path (union (evtrel-fix x) (compose x x)))
  :guard-hints (("goal" :in-theory (enable evtrel-path-p)))
  :returns (new-path evtlist-p)
  :verify-guards nil
  :ruler-extenders :lambdas
  ;; If path is a path in (union (evtrel-fix x) (compose x x)),
  ;; we derive a path in x.
  (b* ((first (evt-fix (car path)))
       (second (evt-fix (cadr path)))
       (rest (if (consp (cddr path))
                 (transitive-path-aux (cdr path) x)
               (list second)))
       ((when (in (pair first second) (evtrel-fix x)))
        (cons first rest)))
    (cons first
          (cons (evt-fix (compose-midpoint first second x x))
                rest)))
  ///
  (defret first-of-<fn>
    (equal (car new-path)
           (evt-fix (car path))))

  (defret last-of-<fn>
    (implies (evtrel-path-p path (union (evtrel-fix x) (compose x x)))
             (equal (car (last new-path))
                    (evt-fix (car (last path)))))
    :hints(("Goal" :in-theory (disable (:d transitive-path-aux))
            :induct <call>
            :expand (<call>
                     (:free (y) (evtrel-path-p path y))))))

  (defret evtrel-path-p-of-<fn>
    (implies (evtrel-path-p path (union (evtrel-fix x) (compose x x)))
             (evtrel-path-p new-path x))
    :hints(("Goal" :in-theory (disable (:d transitive-path-aux))
            :induct <call>
            :expand (<call>
                     (:free (y) (evtrel-path-p path y))
                     (:free (a b) (evtrel-path-p (cons a b) x))))
           (and stable-under-simplificationp
                '(:in-theory (enable in-of-compose-rw)))))

  (defret len-of-<fn>
    (<= 2 (len new-path))
    :rule-classes :linear)

  (verify-guards transitive-path-aux)
  (local (in-theory (enable evtlist-fix))))
       


(define transitive-path ((src evt-p)
                         (dst evt-p)
                         (x evtrel-p))
  :guard (in (pair src dst) (transitive-closure x))
  :returns (path evtlist-p)
  :measure (- (cardinality (cartesian
                            (union (domain x) (range x))
                            (union (domain x) (range x))))
              (cardinality (evtrel-fix x)))
  :hints(("Goal" :in-theory (disable set::expand-cardinality-of-union)))
  :verify-guards nil
  (b* ((comp (compose x x))
       (x (evtrel-fix x))
       ((when (subset comp x))
        (list (evt-fix src) (evt-fix dst))))
    (transitive-path-aux (transitive-path src dst (union x comp)) x))
  ///
  (defret first-of-<fn>
    (equal (car path)
           (evt-fix src)))

  (defret transitive-path-correct
    ;; This (along with the first- and last- properties of transitive-path)
    ;; form half of the correctness statement for transitive-closure: If (src,
    ;; dst) are in (transitive-closure x), then there is a path in x from src
    ;; to dst.
    (implies (in (pair src dst) (transitive-closure x))
             (evtrel-path-p path x))
    :hints(("Goal" :in-theory (enable transitive-closure
                                      evtrel-path-p))))
  
  (defret last-of-<fn>
    (implies (in (pair src dst) (transitive-closure x))
             (equal (car (last path))
                    (evt-fix dst)))
    :hints(("Goal" :in-theory (enable transitive-closure))))
  
  (verify-guards transitive-path
    :hints (("goal" :expand ((transitive-closure x)))))

  (defret len-of-<fn>
    (<= 2 (len path))
    :rule-classes :linear))
  


(defthmd transitive-when-closed-under-self-composition
  (implies (and (evtrel-path-p path x)
                (subset (compose x x) (evtrel-fix x)))
           (in (pair (car path)
                        (car (last path)))
               (evtrel-fix x)))
  :hints(("Goal" :induct (evtrel-path-p path x)
          :in-theory (enable evtrel-path-p
                             set::subset-in))
         (and stable-under-simplificationp
              '(:use ((:instance in-of-compose-suff
                       (x x) (y x)
                       (pair (pair (car path) (caddr path)))
                       (mid (cadr path)))
                      (:instance in-of-compose-suff
                       (x x) (y x)
                       (pair (pair (car path) (car (last (cdr path)))))
                       (mid (cadr path))))))))

(defthm in-transitive-closure-when-path
  ;; The other half of the correctness of transitive-closure: If there is a
  ;; path from a to b in x, then (a, b) are in the transitive closure of x.
  (implies (evtrel-path-p path x)
           (in (pair (car path) (car (last path)))
               (transitive-closure x)))
  :hints(("Goal" :use ((:instance transitive-when-closed-under-self-composition
                        (x (transitive-closure x)))
                       (:instance evtrel-path-p-when-subset
                        (x x) (y (transitive-closure x))))
          :in-theory (e/d (transitive-closure-is-superset)
                          (evtrel-path-p-when-subset)))))
                
             
(defsection transitive-closure-correctnes
  (defun-sk exists-path (src dst x)
    (exists path
            (and (evtrel-path-p path x)
                 (equal src (car path))
                 (equal dst (car (last path))))))

  (in-theory (Disable exists-path))

  (defthmd transitive-closure-correct
    (iff (in pair (transitive-closure x))
         (and (pair-p pair)
              (exists-path (pair->from pair)
                           (pair->to pair)
                           x)))
    :hints ((acl2::use-termhint
             (b* (((pair pair)))
               (if (in pair (transitive-closure x))
                   `(:use ((:instance exists-path-suff
                            (path ,(acl2::hq (transitive-path pair.from pair.to
                                                              x)))
                            (src ,(acl2::hq pair.from)) (dst ,(acl2::hq pair.to))))
                     :in-theory (disable exists-path-suff))
                 `(:in-theory (e/d (exists-path)
                                   (in-transitive-closure-when-path))
                   :use ((:instance in-transitive-closure-when-path
                          (path (exists-path-witness
                                 (pair->from pair)
                                 (pair->to pair) x))))))))))

  (fty::deffixequiv exists-path :args ((src evt-p))
    :hints(("Goal" :in-theory (disable exists-path
                                       exists-path-suff)
            :cases ((exists-path src dst x)))
           (and stable-under-simplificationp
                (let* ((lit (assoc 'exists-path clause))
                       (src (cadr lit))
                       (other (if (eq src 'src) '(evt-fix src) 'src)))
                  `(:expand ((exists-path ,other dst x)
                             (:free (a b) (evtrel-path-p (cons a b) x))
                             (:free (src) (evtrel-path-p (exists-path-witness src dst x) x)))
                    :use ((:instance exists-path-suff
                           (src ,src)
                           (path (cons ,src (cdr (exists-path-witness ,other dst x)))))))))))

  (local (defun replace-last (last x)
           (if (atom (cdr x))
               (list last)
             (cons (car x) (replace-last last (cdr x))))))

  (local (defthm evtrel-path-p-of-replace-last
           (implies (and (evtrel-path-p path x)
                         (evt-equiv (car (last path)) last))
                    (evtrel-path-p (replace-last last path) x))
           :hints(("Goal" :in-theory (enable evtrel-path-p replace-last)))))

  (local (defthm last-of-replace-last
           (equal (car (last (replace-last last x)))
                  last)))

  (local (defthm car-of-replace-last
           (implies (consp (cdr x))
                    (equal (car (replace-last last x))
                           (car x)))))
  
  (local (in-theory (disable replace-last)))
  
  (fty::deffixequiv exists-path :args ((dst evt-p))
    :hints(("Goal" :in-theory (disable exists-path
                                       exists-path-suff)
            :cases ((exists-path src dst x)))
           (and stable-under-simplificationp
                (let* ((lit (assoc 'exists-path clause))
                       (dst (caddr lit))
                       (other (if (eq dst 'dst) '(evt-fix dst) 'dst)))
                  `(:expand ((exists-path src ,other x)
                             (:free (dst) (evtrel-path-p (exists-path-witness src dst x) x)))
                    :use ((:instance exists-path-suff
                           (dst ,dst)
                           (path (replace-last ,dst (exists-path-witness src ,other x))))))))))
  
  (defthm transitive-path-when-exists-path
    (implies (exists-path src dst x)
             (let ((path (transitive-path src dst x)))
               (evtrel-path-p path x)))
    :hints(("Goal" :in-theory (enable transitive-closure-correct)))))



(define reflexive-transitive-closure ((x evtrel-p))
  :returns (closure evtrel-p)
  (union (to-id (univ))
         (transitive-closure x)))
  
(define inverse ((x evtrel-p))
  :returns (inv evtrel-p)
  :measure (acl2-count (evtrel-fix x))
  :verify-guards nil
  (b* ((x (evtrel-fix x)))
    (if (emptyp x)
        nil
      (insert (b* (((pair x1) (head x)))
                (pair x1.to x1.from))
              (inverse (tail x)))))
  ///
  (verify-guards inverse)

  (defret in-of-inverse
    (iff (in pair inv)
         (and (pair-p pair)
              (in (pair (pair->to pair) (pair->from pair)) (evtrel-fix x))))))

(include-book "tools/easy-simplify" :dir :system)

(defines eval-set-rel
  (define eval-setex ((x setex-p) (env env-p))
    :returns (val evtset-p)
    :measure (setex-count x)
    :verify-guards nil
    (setex-case x
      :emptyset nil
      :univset (univ)
      :setvar (cdr (hons-assoc-equal x.name (env->sets env)))
      :singleton (insert (evt-lookup x.e env) nil)
      :setunion (union (eval-setex x.s1 env) (eval-setex x.s2 env))
      :setintersect (intersect (eval-setex x.s1 env) (eval-setex x.s2 env))
      :setimage (b* ((s (eval-setex x.s env))
                     (r (eval-relex x.r env)))
                  (image s r))
      :setpreimage (b* ((s (eval-setex x.s env))
                        (r (eval-relex x.r env)))
                     (preimage s r))))

  (define eval-relex ((x relex-p) (env env-p))
    :returns (val evtrel-p)
    :measure (relex-count x)
    (relex-case x
      :relvar (cdr (hons-assoc-equal x.name (env->rels env)))
      :relsetid (to-id (eval-setex x.s env))
      :relunion (union (eval-relex x.r1 env)
                       (eval-relex x.r2 env))
      :relintersect (intersect (eval-relex x.r1 env)
                               (eval-relex x.r2 env))
      :relcompose (compose (eval-relex x.r1 env)
                           (eval-relex x.r2 env))
      :relstar (reflexive-transitive-closure (eval-relex x.r env))
      :relinverse (inverse (eval-relex x.r env))
      :relprod (cartesian (eval-setex x.s1 env)
                          (eval-setex x.s2 env))))
  ///
  (verify-guards eval-setex)
  (fty::deffixequiv-mutual eval-set-rel)

  (acl2::defopen eval-setex-when-emptyset
    (eval-setex x env)
    :hyp (setex-case x :emptyset)
    :hint (:expand ((eval-setex x env))))

  (acl2::defopen eval-setex-when-univset
    (eval-setex x env)
    :hyp (setex-case x :univset)
    :hint (:expand ((eval-setex x env))))

  (acl2::defopen eval-setex-when-setvar
    (eval-setex x env)
    :hyp (setex-case x :setvar)
    :hint (:expand ((eval-setex x env))))

  (acl2::defopen eval-setex-when-singleton
    (eval-setex x env)
    :hyp (setex-case x :singleton)
    :hint (:expand ((eval-setex x env))))

  (acl2::defopen eval-setex-when-setunion
    (eval-setex x env)
    :hyp (setex-case x :setunion)
    :hint (:expand ((eval-setex x env))))
  
  (acl2::defopen eval-setex-when-setintersect
    (eval-setex x env)
    :hyp (setex-case x :setintersect)
    :hint (:expand ((eval-setex x env))))
  
  (acl2::defopen eval-setex-when-setimage
    (eval-setex x env)
    :hyp (setex-case x :setimage)
    :hint (:expand ((eval-setex x env))))

  (acl2::defopen eval-setex-when-setpreimage
    (eval-setex x env)
    :hyp (setex-case x :setpreimage)
    :hint (:expand ((eval-setex x env))))

  (acl2::defopen eval-relex-when-relvar
    (eval-relex x env)
    :hyp (relex-case x :relvar)
    :hint (:expand ((eval-relex x env))))

  (acl2::defopen eval-relex-when-relsetid
    (eval-relex x env)
    :hyp (relex-case x :relsetid)
    :hint (:expand ((eval-relex x env))))

  (acl2::defopen eval-relex-when-relunion
    (eval-relex x env)
    :hyp (relex-case x :relunion)
    :hint (:expand ((eval-relex x env))))

  (acl2::defopen eval-relex-when-relintersect
    (eval-relex x env)
    :hyp (relex-case x :relintersect)
    :hint (:expand ((eval-relex x env))))

  (acl2::defopen eval-relex-when-relcompose
    (eval-relex x env)
    :hyp (relex-case x :relcompose)
    :hint (:expand ((eval-relex x env))))

  (acl2::defopen eval-relex-when-relstar
    (eval-relex x env)
    :hyp (relex-case x :relstar)
    :hint (:expand ((eval-relex x env))))

  (acl2::defopen eval-relex-when-relinverse
    (eval-relex x env)
    :hyp (relex-case x :relinverse)
    :hint (:expand ((eval-relex x env))))

  (acl2::defopen eval-relex-when-relprod
    (eval-relex x env)
    :hyp (relex-case x :relprod)
    :hint (:expand ((eval-relex x env)))))


(deftagsum pred
  (:pred-false ())
  (:pred-nonempty ((s setex)))
  (:pred-equal ((e1 symbolp) (e2 symbolp)))
  (:pred-in-set ((e symbolp) (s symbolp)))
  (:pred-in-rel ((e1 symbolp) (e2 symbolp) (r symbolp))))

(define eval-pred ((x pred-p) (env env-p))
  (pred-case x
    :pred-false nil
    :pred-nonempty (not (emptyp (eval-setex x.s env)))
    :pred-equal (equal (evt-lookup x.e1 env)
                       (evt-lookup x.e2 env))
    :pred-in-set (in (evt-lookup x.e env)
                     (cdr (hons-assoc-equal x.s (env->sets env))))
    :pred-in-rel (in (pair (evt-lookup x.e1 env)
                           (evt-lookup x.e2 env))
                     (cdr (hons-assoc-equal x.r (env->rels env))))))

(deflist predlist :elt-type pred :true-listp t)

(define eval-predlist ((x predlist-p) (env env-p))
  (if (atom x)
      t
    (and (eval-pred (car x) env)
         (eval-predlist (cdr x) env))))

(include-book "tools/pattern-match" :dir :system)

(acl2::def-pattern-match-constructor
  emptyset (lambda (x) (setex-case x :emptyset)) nil)

(acl2::def-pattern-match-constructor
  univset (lambda (x) (setex-case x :univset)) nil)

(acl2::def-pattern-match-constructor
  setvar (lambda (x) (setex-case x :setvar)) (setvar->name))

(acl2::def-pattern-match-constructor
  singleton (lambda (x) (setex-case x :singleton)) (singleton->e))

(acl2::def-pattern-match-constructor
  setunion (lambda (x) (setex-case x :setunion)) (setunion->s1 setunion->s2))

(acl2::def-pattern-match-constructor
  setintersect (lambda (x) (setex-case x :setintersect)) (setintersect->s1 setintersect->s2))

(acl2::def-pattern-match-constructor
  setimage (lambda (x) (setex-case x :setimage)) (setimage->s setimage->r))

(acl2::def-pattern-match-constructor
  setpreimage (lambda (x) (setex-case x :setpreimage)) (setpreimage->r setpreimage->s))

(acl2::def-pattern-match-constructor
  relvar (lambda (x) (relex-case x :relvar)) (relvar->name))

(acl2::def-pattern-match-constructor
  relsetid (lambda (x) (relex-case x :relsetid)) (relsetid->s))

(acl2::def-pattern-match-constructor
  relunion (lambda (x) (relex-case x :relunion)) (relunion->r1 relunion->r2))

(acl2::def-pattern-match-constructor
  relintersect (lambda (x) (relex-case x :relintersect)) (relintersect->r1 relintersect->r2))

(acl2::def-pattern-match-constructor
  relcompose (lambda (x) (relex-case x :relcompose)) (relcompose->r1 relcompose->r2))

(acl2::def-pattern-match-constructor
  relstar (lambda (x) (relex-case x :relstar)) (relstar->r))

(acl2::def-pattern-match-constructor
  relinverse (lambda (x) (relex-case x :relinverse)) (relinverse->r))

(acl2::def-pattern-match-constructor
  relprod (lambda (x) (relex-case x :relprod)) (relprod->s1 relprod->s2))

(acl2::def-pattern-match-constructor
  pred-false (lambda (x) (pred-case x :pred-false)) nil)

(acl2::def-pattern-match-constructor
  pred-nonempty (lambda (x) (pred-case x :pred-nonempty)) (pred-nonempty->r))

(acl2::def-pattern-match-constructor
  pred-equal (lambda (x) (pred-case x :pred-equal)) (pred-equal->e1 pred-equal->e2))

(acl2::def-pattern-match-constructor
  pred-in-set (lambda (x) (pred-case x :pred-in-set)) (pred-in-set->e pred-in-set->s))

(acl2::def-pattern-match-constructor
  pred-in-rel (lambda (x) (pred-case x :pred-in-rel)) (pred-in-rel->e pred-in-rel->r))



(fty::defmap set-subst :key-type symbolp :val-type setex  :true-listp t)
(fty::defmap rel-subst :key-type symbolp :val-type relex  :true-listp t)

(fty::defprod sigma
  ((sets set-subst)
   (rels rel-subst)))

(define eval-set-subst ((x set-subst-p) (env env-p))
  :returns (new-x set-env-p)
  (if (atom x)
      nil
    (if (mbt (And (consp (car x))
                  (symbolp (caar x))))
        (cons (cons (caar x) (eval-setex (cdar x) env))
              (eval-set-subst (cdr x) env))
      (eval-set-subst (cdr x) env)))
  ///
  (defret lookup-in-eval-set-subst
    (equal (hons-assoc-equal k new-x)
           (and (symbolp k)
                (let ((look (hons-assoc-equal k x)))
                  (and look
                       (cons k (eval-setex (cdr look) env)))))))
  (local (in-theory (enable set-subst-fix))))

(define eval-rel-subst ((x rel-subst-p) (env env-p))
  :returns (new-x rel-env-p)
  (if (atom x)
      nil
    (if (mbt (And (consp (car x))
                  (symbolp (caar x))))
        (cons (cons (caar x) (eval-relex (cdar x) env))
              (eval-rel-subst (cdr x) env))
      (eval-rel-subst (cdr x) env)))
  ///
  (defret lookup-in-eval-rel-subst
    (equal (hons-assoc-equal k new-x)
           (and (symbolp k)
                (let ((look (hons-assoc-equal k x)))
                  (and look
                       (cons k (eval-relex (cdr look) env)))))))
  (local (in-theory (enable rel-subst-fix))))

(define eval-sigma ((x sigma-p) (env env-p))
  :returns (new-x env-p)
  (env (env->evts env)
       (eval-set-subst (sigma->sets x) env)
       (eval-rel-subst (sigma->rels x) env)))                    

(defines subst-set-rel
  (define subst-setex ((x setex-p) (s sigma-p))
    :returns (new-x setex-p)
    :measure (setex-count x)
    :verify-guards nil
    (setex-case x
      :setvar (let ((look (hons-assoc-equal x.name (sigma->sets s))))
                (if look (cdr look) (emptyset)))
      :setunion (setunion (subst-setex x.s1 s)
                          (subst-setex x.s2 s))
      :setintersect (setintersect (subst-setex x.s1 s)
                                  (subst-setex x.s2 s))
      :setimage (setimage (subst-setex x.s s)
                          (subst-relex x.r s))
      :setpreimage (setpreimage (subst-relex x.r s)
                                (subst-setex x.s s))
      :otherwise (setex-fix x)))
  (define subst-relex ((x relex-p) (s sigma-p))
    :returns (new-x relex-p)
    :measure (relex-count x)
    (relex-case x
      :relvar (let ((look (hons-assoc-equal x.name (sigma->rels s))))
                (if look (cdr look) (relsetid (emptyset))))
      :relsetid (relsetid (subst-setex x.s s))
      :relunion (relunion (subst-relex x.r1 s)
                          (subst-relex x.r2 s))
      :relintersect (relintersect (subst-relex x.r1 s)
                                  (subst-relex x.r2 s))
      :relcompose (relcompose (subst-relex x.r1 s)
                              (subst-relex x.r2 s))
      :relstar (relstar (subst-relex x.r s))
      :relinverse (relinverse (subst-relex x.r s))
      :relprod (relprod (subst-setex x.s1 s)
                        (subst-setex x.s2 s))))
  ///
  (std::defret-mutual eval-of-subst
    (defret eval-of-subst-setex
      (equal (eval-setex new-x env)
             (eval-setex x (eval-sigma s env)))
      :hints ('(:expand (<call>
                         (:free (env) (eval-setex x env))))
              (and stable-under-simplificationp
                   '(:in-theory (enable eval-sigma
                                        evt-lookup))))
      :fn subst-setex)
    (defret eval-of-subst-relex
      (equal (eval-relex new-x env)
             (eval-relex x (eval-sigma s env)))
      :hints ('(:expand (<call>
                         (:Free (env) (eval-relex x env))))
              (and stable-under-simplificationp
                   '(:in-theory (enable eval-sigma))))
      :fn subst-relex))

  (verify-guards subst-setex))









(defun dotted-args (sym args pkg)
  (if (atom args)
      nil
    (cons (intern-in-package-of-symbol
           (concatenate 'string (symbol-name sym) "." (symbol-name (car args)))
           pkg)
          (dotted-args sym (cdr args) pkg))))

(mutual-recursion
 (defun collect-fnnames (x)
   (if (atom x)
       nil
     (if (symbolp (car x))
         (cons (car x)
               (collect-fnnames-list (cdr x)))
       (collect-fnnames-list (cdr x)))))
 (defun collect-fnnames-list (x)
   (if (atom x)
       nil
     (append (collect-fnnames (car x))
             (collect-fnnames-list (cdr x))))))

(defun concat-fnnames-aux (x)
  (if (atom (cdr x))
      (symbol-name (car x))
    (concatenate 'string (symbol-name (car x)) "-" (concat-fnnames-aux (cdr x)))))

(defun concat-fnnames (x)
  (concat-fnnames-aux (collect-fnnames x)))

(defun omit-dontcares (pattern x)
  (if (atom pattern)
      nil
    (if (eq (car pattern) '&)
        (omit-dontcares (cdr pattern) (cdr x))
      (cons (car x) (omit-dontcares (cdr pattern) (cdr x))))))

(define generate-matcher-fn (prefix ty ;; fixtype
                                    sum ;; flexsum
                                    idx pattern result w)
  :mode :program
  (b* (((fty::fixtype ty))
       ((fty::flexsum sum))
       (ctor (car pattern))
       (args (acl2::formals ctor w))
       (x-dot-args (omit-dontcares (cdr pattern) (dotted-args 'x args ctor)))
       (pattern-args (remove '& (cdr pattern)))
       (kind (intern-in-package-of-symbol (symbol-name ctor) :keyword-pkg))
       (eval (intern-in-package-of-symbol
              (concatenate 'string "EVAL-" (symbol-name sum.name)) sum.name))
       (name (intern-in-package-of-symbol
              (concatenate 'string
                           (symbol-name prefix) "-"
                           (concat-fnnames pattern) "-"
                           (coerce (explode-atom idx 10) 'string))
              sum.name)))
  `(define ,name ((x ,ty.pred))
     :guard (,sum.case x ,kind)
     :returns (mv success (new-x ,ty.pred))
     (b* (((,ctor x)))
       (acl2::pattern-match-list
        ,x-dot-args
        (,pattern-args (mv t ,result))
        (& (mv nil (,ty.fix x)))))
     ///
     (defret <fn>-correct
       (implies (,sum.case x ,kind)
                (equal (,eval new-x env)
                       (,eval x env)))))))

(define generate-matchers (prefix ty sum idx pattern/results w)
  :mode :program
  (if (atom pattern/results)
      nil
    (cons (generate-matcher-fn prefix ty sum idx (caar pattern/results) (cadar pattern/results) w)
          (generate-matchers prefix ty sum (+ 1 idx) (cdr pattern/results) w))))

(define collect-ctor-patterns (ctor pattern/results)
  :mode :program
  (if (atom pattern/results)
      nil
    (if (eq (caaar pattern/results) ctor)
        (cons (car pattern/results)
              (collect-ctor-patterns ctor (cdr pattern/results)))
      (collect-ctor-patterns ctor (cdr pattern/results)))))

(define generate-ctor-matcher-cases (matchers)
  (if (atom matchers)
      nil
    `(((mv ok new-x) (,(car matchers) x))
      ((when ok) (mv ok new-x))
      . ,(generate-ctor-matcher-cases (cdr matchers)))))

(define generate-ctor-matchers (prefix ty sum ctor pattern/results w)
  :mode :program
  (b* ((pattern/results (collect-ctor-patterns ctor pattern/results))
       ((fty::fixtype ty))
       ((fty::flexsum sum))
       (kind (intern-in-package-of-symbol (symbol-name ctor) :keyword-pkg))
       (eval (intern-in-package-of-symbol
              (concatenate 'string "EVAL-" (symbol-name sum.name)) sum.name))
       (matcher-defines (generate-matchers prefix ty sum 0 pattern/results w))
       (matcher-names (acl2::strip-cadrs matcher-defines))
       (name (intern-in-package-of-symbol
              (concatenate 'string (symbol-name prefix) "-" (symbol-name ctor))
              sum.name)))
    `(progn
       ,@matcher-defines
       (define ,name ((x ,ty.pred))
         :guard (,sum.case x ,kind)
         :returns (mv success (new-x ,ty.pred))
         (b* ,(generate-ctor-matcher-cases matcher-names)
           (mv nil (,ty.fix x)))
         ///
         (defret <fn>-correct
           (implies (,sum.case x ,kind)
                    (equal (,eval new-x env)
                           (,eval x env))))))))

(define collect-ctor-matchers (prefix ty sum prods pattern/results w)
  :mode :program
  (if (atom prods)
      nil
    (cons (b* (((fty::flexprod prod1) (car prods)))
            (generate-ctor-matchers prefix ty sum prod1.ctor-name pattern/results w))
          (collect-ctor-matchers prefix ty sum (cdr prods) pattern/results w))))

(define matcher-cases-for-prods (prefix type prods)
  :mode :program
  (if (atom prods)
      nil
    (b* (((fty::flexprod prod1) (car prods)))
      `(,prod1.kind (,(intern-in-package-of-symbol
                       (concatenate 'string (symbol-name prefix) "-" (symbol-name prod1.ctor-name))
                       type)
                     x)
                    . ,(matcher-cases-for-prods prefix type (cdr prods))))))

(define generate-rewriter (prefix type pattern/results w)
  :mode :program
  (b* ((fixtype (fty::find-fixtype type (fty::get-fixtypes-alist w)))
       ((unless fixtype) (raise "no fixtype found: ~x0" type))
       ((fty::fixtype ty) fixtype)
       ((mv & flextype) (fty::search-deftypes-table type (fty::get-flextypes w)))
       ((unless flextype)
        (raise "no type info found for ~x0" type))
       ((unless (eq (fty::tag flextype) :sum))
        (raise "not a sum type: ~x0" type))
       ((fty::flexsum sum) flextype)
       (ctor-matchers (collect-ctor-matchers prefix ty sum sum.prods pattern/results w))
       (name (intern-in-package-of-symbol
              (concatenate 'string (symbol-name prefix) "-" (symbol-name type))
              type))
       (eval (intern-in-package-of-symbol
              (concatenate 'string "EVAL-" (symbol-name sum.name)) sum.name)))
    `(progn
       ,@ctor-matchers
       (define ,name ((x ,ty.pred))
         :returns (mv success (new-x ,ty.pred))
         (,sum.case x
           . ,(matcher-cases-for-prods prefix sum.name sum.prods))
         ///
         (defret <fn>-correct
           (equal (,eval new-x env)
                  (,eval x env)))))))



(defthm union-of-subset2
  (implies (subset y x)
           (equal (union y x) (sfix x)))
  :hints(("Goal" :in-theory (enable set::union-with-subset-left))))

(defthm intersect-with-subset
  (implies (subset y x)
           (equal (intersect y x) (sfix y)))
  :hints(("Goal" :in-theory (enable set::intersect-with-subset-left))))

(defthm intersect-with-subset2
  (implies (subset y x)
           (equal (intersect x y) (sfix y)))
  :hints(("Goal" :in-theory (enable set::intersect-with-subset-right))))

(defthm image-of-nil
  (equal (image nil x)
         nil)
  :hints(("Goal" :in-theory (enable image))))

(defthm image-of-to-id
  (equal (image x (to-id y))
         (intersect (evtset-fix x) (evtset-fix y)))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-image-rw
                                    in-of-image-suff)))
  :otf-flg t)

(defthm image-of-union
  (implies (and (evtset-p x) (evtset-p y))
           (equal (image (union x y) z)
                  (union (image x z) (image y z))))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-image-rw
                                    in-of-image-suff)))
  :otf-flg t)

(defthm preimage-of-nil
  (equal (preimage nil x)
         nil)
  :hints(("Goal" :in-theory (enable preimage))))

(defthm preimage-of-to-id
  (equal (preimage x (to-id y))
         (intersect (evtset-fix y) (evtset-fix x)))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-preimage-rw
                                    in-of-preimage-suff)))
  :otf-flg t)

(defthm preimage-of-union
  (implies (and (evtset-p x) (evtset-p y))
           (equal (preimage (union x y) z)
                  (union (preimage x z) (preimage y z))))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-preimage-rw
                                    in-of-preimage-suff)))
  :otf-flg t)

;; (defthm image-of-intersect
;;   (implies (and (evtset-p x) (evtset-p y))
;;            (equal (image (intersect x y) z)
;;                   (intersect (image x z) (image y z))))
;;   :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
;;                                     pick-a-point-subset-strategy
;;                                     in-of-image-rw
;;                                     in-of-image-suff
;;                                     in-of-image-suff2)))
;;   :otf-flg t)


(make-event
 (generate-rewriter 'normalize1 'setex
                    '(((setunion (emptyset) s)
                       s)
                      ((setunion s (emptyset))
                       s)
                      ((setunion & (univset)) (univset))
                      ((setunion (univset) &) (univset))
                      ((setintersect (emptyset) &) (emptyset))
                      ((setintersect & (emptyset)) (emptyset))
                      ((setintersect (univset) s) s)
                      ((setintersect s (univset)) s)
                      ((setimage (emptyset) &) (emptyset))
                      ((setimage s1 (relsetid s2)) (setintersect s1 s2))
                      ((setpreimage & (emptyset)) (emptyset))
                      ((setpreimage (relsetid s1) s2) (setintersect s1 s2))
                      ;; Move unions up over pre/postimages or vice versa?
                      ((setimage (setunion s1 s2) r) (setunion (setimage s1 r) (setimage s2 r)))
                      ;; ((setimage (setintersect s1 s2) r) (setintersect (setimage s1 r) (setimage s2 r)))
                      ((setpreimage r (setunion s1 s2)) (setunion (setpreimage r s1) (setpreimage r s2)))
                      ;; ((setpreimage r (setintersect s1 s2)) (setintersect (setpreimage r s1) (setpreimage r s2)))
                      )
                    (w state)))


(defthm to-id-of-union
  (implies (and (evtset-p x) (evtset-p y))
           (equal (to-id (union x y))
                  (union (to-id x) (to-id y))))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-to-id))))

(defthm to-id-of-intersect
  (implies (and (evtset-p x) (evtset-p y))
           (equal (to-id (intersect x y))
                  (intersect (to-id x) (to-id y))))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-to-id))))

(defthm inverse-of-union
  (implies (and (evtrel-p x) (evtrel-p y))
           (equal (inverse (union x y))
                  (union (inverse x) (inverse y))))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-inverse))))

(defthm inverse-of-intersect
  (implies (and (evtrel-p x) (evtrel-p y))
           (equal (inverse (intersect x y))
                  (intersect (inverse x) (inverse y))))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    set::double-containment-no-backchain-limit
                                    in-of-inverse))))


(defthm in-univ-when-evt-p
  (implies (evt-p x)
           (in x (univ)))
  :hints(("Goal" :in-theory (enable evt-p))))

(defthm subset-of-univ-rel
  (implies (evtrel-p x)
           (subset x (cartesian (univ) (univ))))
  :hints(("Goal" :in-theory (enable pick-a-point-subset-strategy
                                    in-of-cartesian)))
  :otf-flg t)


(defthm compose-of-nil
  (equal (compose nil x) nil)
  :hints(("Goal" :in-theory (enable compose))))

(defthm compose-of-nil-2
  (equal (compose x nil) nil)
  :hints(("Goal" :in-theory (enable compose compose1))))

(defthm relation-path-p-of-to-id
  (implies (not (equal (evt-fix (car path))
                       (evt-fix (car (last path)))))
           (not (evtrel-path-p path (to-id x))))
  :hints(("Goal" :in-theory (enable evtrel-path-p))))

(defthm exists-path-of-to-id
  (implies (not (equal (evt-fix src) (evt-fix dst)))
           (not (exists-path src dst (to-id x))))
  :hints(("Goal" :in-theory (enable exists-path))))

(defthm reflexive-transitive-closure-of-to-id
  (equal (reflexive-transitive-closure (to-id r))
         (to-id (univ)))
  :hints(("Goal" :in-theory (enable reflexive-transitive-closure
                                    set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    transitive-closure-correct))))

(defthm exists-path-of-univ-rel
  (exists-path src dst (cartesian (univ) (univ)))
  :hints (("goal" :use ((:instance exists-path-suff
                         (path (list src dst))
                         (x (cartesian (univ) (univ)))))
           :in-theory (enable evtrel-path-p
                              in-of-cartesian))))

(defthm reflexive-transitive-closure-of-univ-rel
  (equal (reflexive-transitive-closure (cartesian (univ) (univ)))
         (cartesian (univ) (univ)))
  :hints(("Goal" :in-theory (enable reflexive-transitive-closure
                                    set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    transitive-closure-correct))))

(defthm inverse-of-to-id
  (equal (inverse (to-id r))
         (to-id r))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-inverse))))

(defthm inverse-of-cartesian
  (equal (inverse (cartesian d r))
         (cartesian r d))
  :hints(("Goal" :in-theory (enable set::double-containment-no-backchain-limit
                                    pick-a-point-subset-strategy
                                    in-of-inverse
                                    in-of-cartesian))))


(defthm cartesian-of-nil
  (equal (cartesian nil r) nil)
  :hints(("Goal" :in-theory (enable cartesian))))

(defthm cartesian-of-nil-2
  (equal (cartesian r nil) nil)
  :hints(("Goal" :in-theory (enable cartesian
                                    cartesian1))))

(make-event
 (generate-rewriter 'normalize1 'relex
                    '(((relunion (relsetid s1) (relsetid s2))
                       (relsetid (setunion s1 s2))) ;; or backward?
                      ((relintersect (relsetid s1) (relsetid s2))
                       (relsetid (setintersect s1 s2))) ;; or backward?
                      ((relunion (relsetid (emptyset)) r) r)
                      ((relunion r (relsetid (emptyset))) r)
                      ((relunion (relprod (univset) (univset)) &)
                       (relprod (univset) (univset)))
                      ((relunion & (relprod (univset) (univset)))
                       (relprod (univset) (univset)))
                      ((relunion (relinverse x) (relinverse y))
                       (relinverse (relunion x y))) ;; or backward?
                      ((relintersect (relinverse x) (relinverse y))
                       (relinverse (relintersect x y))) ;; or backward?
                      ((relintersect (relsetid (emptyset)) &) (relsetid (emptyset)))
                      ((relintersect & (relsetid (emptyset))) (relsetid (emptyset)))
                      ((relintersect (relprod (univset) (univset)) r) r)
                      ((relintersect r (relprod (univset) (univset))) r)
                      ((relprod (emptyset) &) (relsetid (emptyset)))
                      ((relprod & (emptyset)) (relsetid (emptyset)))
                      ((relcompose (relsetid (emptyset)) &) (relsetid (emptyset)))
                      ((relcompose & (relsetid (emptyset))) (relsetid (emptyset)))
                      ((relstar (relsetid &)) (relsetid (univset)))
                      ((relstar (relprod (univset) (univset))) (relprod (univset) (univset)))
                      ((relinverse (relsetid r)) (relsetid r))
                      ((relinverse (relprod s1 s2)) (relprod s2 s1)))
                    (w state)))

      



(define normalize-positive-nonempty-rel ((x relex-p))
  :returns (new-x relex-p)
  (pattern-match x
    ((relcompose (relsetid s1) (relsetid s2))
     (relsetid (setintersect s1 s2)))
    
    ;; ((relcompose (relsetid (singleton e)) (relsetid (univset)))
      ;;  (relsetid (singleton e))) ;; idL
    ;; ((relcompose (relsetid (univset)) (relsetid (singleton e)))
    ;;  (relsetid (singleton e))) ;; idR
    ;; ((relcompose (relsetid (singleton e)) (relsetid (emptyset)))
    ;;  (relsetid (emptyset))) ;; bot2L
    ;; ((relcompose (relsetid (emptyset)) (relsetid (singleton e)))
    ;;  (relsetid (emptyset))) ;; bot2R
    ((relcompose (relsetid s1) (relprod (univset) s2))
     (relprod s1 s2))
    ((relcompose (relprod s1 (univset)) (relsetid s2))
     (relprod s1 s2))
    ((relcompose (relsetid (singleton e)) (relcompose r1 r2))
     (relcompose (relcompose (relsetid (singleton e)) r1) r2)) ;; .2,2L
    ((relcompose (relcompose r1 r2) (relsetid (singleton e)))
     (relcompose r1 (relcompose r2 (relsetid (singleton e))))) ;; .2,2L

))

(deflist predlistlist :elt-type predlist :true-listp t)




(define normalize-positive-nonempty-set ((x setex-p))
  :returns (branches predlistlist-p)
  (pattern-match x
    ((emptyset) nil)
    ((univset)  (list nil))
    ((singleton &) (list nil))
    ((setunion s1 s2) (list (list (pred-nonempty s1))
                            (list (pred-nonempty s2))))
    ((setimage (singleton e) (relsetid (univset)))
     
      
      
     
