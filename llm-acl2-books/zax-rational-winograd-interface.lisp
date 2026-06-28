; Rational-only interface for direct, Winograd, and ADP-built DFTs.
;
; Inputs are ACL2 rationals.  A complex coefficient or output is represented
; by a cons pair of ACL2 rationals.  No ACL2 real, Lisp complex value, or
; ACL2(r) object occurs in this theory.

(in-package "ACL2")
(include-book "zau-adp-winograd3-equivalence")
(include-book "zav-winograd-direct-equivalence")

; Historical qcx-realify is only the embedding x |-> (x . 0).
(defun qcx-lift-rational-inputs (xs)
  (qcx-realify xs))

(defthm qcx-lift-rational-inputs-is-qcx-realify
  (equal (qcx-lift-rational-inputs xs)
         (qcx-realify xs)))

(defthm qcx-vectorp-of-lift-rational-inputs
  (implies (and (rational-listp xs)
                (equal (len xs) (nfix n)))
           (qcx-vectorp n (qcx-lift-rational-inputs xs)))
  :hints (("Goal"
           :use ((:instance qcx-vectorp-of-realify))
           :in-theory (enable qcx-lift-rational-inputs))))

(defun rwd-rational-input-run
  (p input-indices kernel-indices small-terms small-posts xs table)
  (rwd-run p input-indices kernel-indices small-terms small-posts
           (qcx-realify xs) table))

(defun qwb-rational-input-run
  (p input-indices kernel-indices small-terms small-posts xs table)
  (qwb-rwd-run p input-indices kernel-indices small-terms small-posts
               (qcx-realify xs) table))

(defthm rwd-direct-output-table-error-bound-lifted
  (implies
   (and (posp p)
        (rational-listp xs)
        (equal (len xs) (nfix p))
        (qcx-vectorp p a)
        (qcx-vectorp p b)
        (qcx-table-closep eps a b)
        (rationalp eps)
        (<= 0 eps))
   (<=
    (qcx-dist
     (rwd-direct-output p output-index (qcx-realify xs) a)
     (rwd-direct-output p output-index (qcx-realify xs) b))
    (* eps (rational-list-l1 xs))))
  :hints (("Goal"
           :use ((:instance rwd-direct-output-inherits-table-error-bound))
           :in-theory nil))
  :rule-classes nil)

(defun rwd-output-list-induct (outputs)
  (if (endp outputs)
      nil
    (rwd-output-list-induct (cdr outputs))))

(defun rwd-direct-outputs-closep (bound outputs p xs a b)
  (if (endp outputs)
      t
    (and (<= (qcx-dist
              (rwd-direct-output p (car outputs) xs a)
              (rwd-direct-output p (car outputs) xs b))
             bound)
         (rwd-direct-outputs-closep
          bound (cdr outputs) p xs a b))))

(defthm rwd-direct-outputs-closep-of-nil
  (equal (rwd-direct-outputs-closep bound nil p xs a b) t)
  :hints (("Goal"
           :expand ((rwd-direct-outputs-closep bound nil p xs a b))
           :in-theory nil)))

(defthm rwd-direct-outputs-closep-of-cons
  (equal
   (rwd-direct-outputs-closep bound (cons output outputs) p xs a b)
   (and (<= (qcx-dist
             (rwd-direct-output p output xs a)
             (rwd-direct-output p output xs b))
            bound)
        (rwd-direct-outputs-closep bound outputs p xs a b)))
  :hints (("Goal"
           :expand ((rwd-direct-outputs-closep
                     bound (cons output outputs) p xs a b))
           :in-theory '(car-cons cdr-cons))))

(defthm rwd-direct-outputs-closep-from-one-output
  (implies
   (and (posp p)
        (rational-listp xs)
        (equal (len xs) (nfix p))
        (qcx-vectorp p a)
        (qcx-vectorp p b)
        (qcx-table-closep eps a b)
        (rationalp eps)
        (<= 0 eps))
   (rwd-direct-outputs-closep
    (* eps (rational-list-l1 xs)) outputs p
    (qcx-realify xs) a b))
  :hints (("Goal"
           :induct (len outputs)
           :in-theory '(len))
          ("Subgoal *1/1"
           :expand ((rwd-direct-outputs-closep
                     (* eps (rational-list-l1 xs)) outputs p
                     (qcx-realify xs) a b))
           :use ((:instance rwd-direct-output-table-error-bound-lifted
                            (output-index (car outputs))))
           :in-theory '(endp))
          ("Subgoal *1/2"
           :expand ((rwd-direct-outputs-closep
                     (* eps (rational-list-l1 xs)) outputs p
                     (qcx-realify xs) a b))
           :in-theory '(endp))))

(defthm rwd-direct-outputs-closep-is-dft-output-closep
  (equal
   (rwd-direct-outputs-closep bound outputs p xs a b)
   (dft-output-closep
    bound
    (rwd-direct-outputs outputs p xs a)
    (rwd-direct-outputs outputs p xs b)))
  :hints (("Goal"
           :induct (rwd-output-list-induct outputs)
           :in-theory
           (e/d (rwd-output-list-induct
                 rwd-direct-outputs-closep
                 rwd-direct-outputs
                 dft-output-closep)
                (rwd-direct-output qcx-dist qcx-sub qcx-vectorp)))))

(defthm rwd-direct-outputs-table-error-bound
  (implies
   (and (posp p)
        (rational-listp xs)
        (equal (len xs) (nfix p))
        (qcx-vectorp p a)
        (qcx-vectorp p b)
        (qcx-table-closep eps a b)
        (rationalp eps)
        (<= 0 eps))
   (dft-output-closep
    (* eps (rational-list-l1 xs))
    (rwd-direct-outputs outputs p (qcx-realify xs) a)
    (rwd-direct-outputs outputs p (qcx-realify xs) b)))
  :hints (("Goal"
           :use ((:instance rwd-direct-outputs-closep-from-one-output)
                 (:instance rwd-direct-outputs-closep-is-dft-output-closep
                            (bound (* eps (rational-list-l1 xs)))
                            (xs (qcx-realify xs))))
           :in-theory nil)))

(defthm rwd-rational-input-run-correct
  (implies
   (and (rwd-compiled-certifiesp
         p input-indices kernel-indices output-indices
         small-terms small-posts)
        (posp p)
        (rational-listp xs)
        (equal (len xs) (nfix p))
        (qcx-vectorp p table))
   (equal
    (rwd-rational-input-run
     p input-indices kernel-indices small-terms small-posts xs table)
    (rwd-direct-outputs
     (rwd-compile-outputs output-indices)
     p (qcx-realify xs) table)))
  :hints (("Goal"
           :use ((:instance qcx-vectorp-of-realify
                            (n p))
                 (:instance rwd-compiled-transform-correct
                            (xs (qcx-realify xs))))
           :in-theory '(rwd-rational-input-run))))

(defthm rwd-rational-input-run-table-stability
  (implies
   (and (rwd-compiled-certifiesp
         p input-indices kernel-indices output-indices
         small-terms small-posts)
        (posp p)
        (rational-listp xs)
        (equal (len xs) (nfix p))
        (qcx-vectorp p a)
        (qcx-vectorp p b)
        (qcx-table-closep eps a b)
        (rationalp eps)
        (<= 0 eps))
   (dft-output-closep
    (* eps (rational-list-l1 xs))
    (rwd-rational-input-run
     p input-indices kernel-indices small-terms small-posts xs a)
    (rwd-rational-input-run
     p input-indices kernel-indices small-terms small-posts xs b)))
  :hints (("Goal"
           :use ((:instance rwd-rational-input-run-correct
                            (table a))
                 (:instance rwd-rational-input-run-correct
                            (table b))
                 (:instance rwd-direct-outputs-table-error-bound
                            (outputs (rwd-compile-outputs output-indices))))
           :in-theory nil)))

(defthm qwb-rational-input-run-equals-rwd-rational-input-run
  (implies
   (and (wbc-terms-validp
         p (rwd-compile-terms p input-indices kernel-indices small-terms))
        (qwb-posts-rationalp (rwd-compile-posts small-terms small-posts))
        (posp p)
        (rational-listp xs)
        (equal (len xs) (nfix p))
        (qcx-vectorp p table))
   (equal
    (qwb-rational-input-run
     p input-indices kernel-indices small-terms small-posts xs table)
    (rwd-rational-input-run
     p input-indices kernel-indices small-terms small-posts xs table)))
  :hints (("Goal"
           :use ((:instance qcx-vectorp-of-realify
                            (n p))
                 (:instance qwb-rwd-run-equals-rwd-run
                            (xs (qcx-realify xs))))
           :in-theory '(qwb-rational-input-run
                        rwd-rational-input-run))))

(defthm qwb-rational-input-run-correct
  (implies
   (and (rwd-compiled-certifiesp
         p input-indices kernel-indices output-indices
         small-terms small-posts)
        (wbc-terms-validp
         p (rwd-compile-terms p input-indices kernel-indices small-terms))
        (qwb-posts-rationalp (rwd-compile-posts small-terms small-posts))
        (posp p)
        (rational-listp xs)
        (equal (len xs) (nfix p))
        (qcx-vectorp p table))
   (equal
    (qwb-rational-input-run
     p input-indices kernel-indices small-terms small-posts xs table)
    (rwd-direct-outputs
     (rwd-compile-outputs output-indices)
     p (qcx-realify xs) table)))
  :hints (("Goal"
           :use ((:instance qwb-rational-input-run-equals-rwd-rational-input-run)
                 (:instance rwd-rational-input-run-correct))
           :in-theory nil)))

(defthm qwb-rational-input-run-table-stability
  (implies
   (and (rwd-compiled-certifiesp
         p input-indices kernel-indices output-indices
         small-terms small-posts)
        (wbc-terms-validp
         p (rwd-compile-terms p input-indices kernel-indices small-terms))
        (qwb-posts-rationalp (rwd-compile-posts small-terms small-posts))
        (posp p)
        (rational-listp xs)
        (equal (len xs) (nfix p))
        (qcx-vectorp p a)
        (qcx-vectorp p b)
        (qcx-table-closep eps a b)
        (rationalp eps)
        (<= 0 eps))
   (dft-output-closep
    (* eps (rational-list-l1 xs))
    (qwb-rational-input-run
     p input-indices kernel-indices small-terms small-posts xs a)
    (qwb-rational-input-run
     p input-indices kernel-indices small-terms small-posts xs b)))
  :hints (("Goal"
           :use ((:instance qwb-rational-input-run-equals-rwd-rational-input-run
                            (table a))
                 (:instance qwb-rational-input-run-equals-rwd-rational-input-run
                            (table b))
                 (:instance rwd-rational-input-run-table-stability))
           :in-theory nil)))

; A requested rational output tolerance can be pushed backwards to a
; sufficient pointwise tolerance for the rational twiddle table.  The extra
; 1 avoids a special case for the all-zero input and is deliberately
; conservative.
(defun rw-table-epsilon-for-output (output-eps xs)
  (/ output-eps (+ 1 (rational-list-l1 xs))))

(defthm rationalp-of-rational-list-l1-for-winograd
  (implies (rational-listp xs)
           (rationalp (rational-list-l1 xs)))
  :hints (("Goal"
           :induct (rational-listp xs)
           :in-theory (enable rational-listp rational-list-l1))))

(defthm one-plus-rational-list-l1-positive
  (< 0 (+ 1 (rational-list-l1 xs)))
  :hints (("Goal"
           :use ((:instance rational-list-l1-nonnegative))
           :in-theory nil))
  :rule-classes :linear)

(defthm rationalp-of-rw-table-epsilon-for-output
  (implies (and (rationalp output-eps)
                (rational-listp xs))
           (rationalp (rw-table-epsilon-for-output output-eps xs)))
  :hints (("Goal"
           :use ((:instance rationalp-of-rational-list-l1-for-winograd)
                 (:instance one-plus-rational-list-l1-positive))
           :in-theory (enable rw-table-epsilon-for-output))))

(defthm reciprocal-one-plus-rational-list-l1-positive
  (implies (rational-listp xs)
           (< 0 (/ (+ 1 (rational-list-l1 xs)))))
  :hints (("Goal"
           :use ((:instance rationalp-of-rational-list-l1-for-winograd)
                 (:instance one-plus-rational-list-l1-positive))
           :in-theory '(|(< 0 (/ x))|)))
  :rule-classes :linear)

(defthm rw-table-epsilon-for-output-nonnegative
  (implies (and (rationalp output-eps)
                (<= 0 output-eps)
                (rational-listp xs))
           (<= 0 (rw-table-epsilon-for-output output-eps xs)))
  :hints (("Goal"
           :use ((:instance reciprocal-one-plus-rational-list-l1-positive))
           :in-theory (enable rw-table-epsilon-for-output)))
  :rule-classes :linear)

(defthm nonnegative-over-one-plus-bound
  (implies (and (rationalp x)
                (<= 0 x))
           (<= (* x (/ (+ 1 x))) 1))
  :hints (("Goal" :nonlinearp t)))

(defthm rw-table-epsilon-budget-suffices
  (implies (and (rationalp output-eps)
                (<= 0 output-eps)
                (rational-listp xs))
           (<= (* (rw-table-epsilon-for-output output-eps xs)
                  (rational-list-l1 xs))
               output-eps))
  :hints (("Goal"
           :use ((:instance rational-list-l1-nonnegative)
                 (:instance rationalp-of-rational-list-l1-for-winograd)
                 (:instance nonnegative-over-one-plus-bound
                            (x (rational-list-l1 xs))))
           :in-theory (enable rw-table-epsilon-for-output)))
  :rule-classes :linear)

(defthm rationalp-of-rw-table-epsilon-times-l1
  (implies (and (rationalp output-eps)
                (rational-listp xs))
           (rationalp
            (* (rw-table-epsilon-for-output output-eps xs)
               (rational-list-l1 xs))))
  :hints (("Goal"
           :use ((:instance rationalp-of-rw-table-epsilon-for-output)
                 (:instance rationalp-of-rational-list-l1-for-winograd))
           :in-theory nil)))

(defthm dft-output-closep-monotone
  (implies (and (dft-output-closep small xs ys)
                (rationalp small)
                (rationalp large)
                (<= small large))
           (dft-output-closep large xs ys))
  :hints (("Goal"
           :induct (dft-output-closep small xs ys)
           :in-theory (enable dft-output-closep))))

(defthm rwd-rational-input-run-requested-output-tolerance
  (implies
   (and (rwd-compiled-certifiesp
         p input-indices kernel-indices output-indices
         small-terms small-posts)
        (posp p)
        (rational-listp xs)
        (equal (len xs) (nfix p))
        (qcx-vectorp p a)
        (qcx-vectorp p b)
        (rationalp output-eps)
        (<= 0 output-eps)
        (qcx-table-closep
         (rw-table-epsilon-for-output output-eps xs) a b))
   (dft-output-closep
    output-eps
    (rwd-rational-input-run
     p input-indices kernel-indices small-terms small-posts xs a)
    (rwd-rational-input-run
     p input-indices kernel-indices small-terms small-posts xs b)))
  :hints (("Goal"
           :use ((:instance rwd-rational-input-run-table-stability
                            (eps (rw-table-epsilon-for-output output-eps xs)))
                 (:instance rw-table-epsilon-budget-suffices)
                 (:instance rationalp-of-rw-table-epsilon-times-l1)
                 (:instance rationalp-of-rw-table-epsilon-for-output)
                 (:instance rw-table-epsilon-for-output-nonnegative)
                 (:instance dft-output-closep-monotone
                            (small (* (rw-table-epsilon-for-output
                                       output-eps xs)
                                      (rational-list-l1 xs)))
                            (large output-eps)
                            (xs (rwd-rational-input-run
                                 p input-indices kernel-indices
                                 small-terms small-posts xs a))
                            (ys (rwd-rational-input-run
                                 p input-indices kernel-indices
                                 small-terms small-posts xs b))))
           :in-theory nil)))

(defthm qwb-rational-input-run-requested-output-tolerance
  (implies
   (and (rwd-compiled-certifiesp
         p input-indices kernel-indices output-indices
         small-terms small-posts)
        (wbc-terms-validp
         p (rwd-compile-terms p input-indices kernel-indices small-terms))
        (qwb-posts-rationalp (rwd-compile-posts small-terms small-posts))
        (posp p)
        (rational-listp xs)
        (equal (len xs) (nfix p))
        (qcx-vectorp p a)
        (qcx-vectorp p b)
        (rationalp output-eps)
        (<= 0 output-eps)
        (qcx-table-closep
         (rw-table-epsilon-for-output output-eps xs) a b))
   (dft-output-closep
    output-eps
    (qwb-rational-input-run
     p input-indices kernel-indices small-terms small-posts xs a)
    (qwb-rational-input-run
     p input-indices kernel-indices small-terms small-posts xs b)))
  :hints (("Goal"
           :use ((:instance qwb-rational-input-run-table-stability
                            (eps (rw-table-epsilon-for-output output-eps xs)))
                 (:instance rw-table-epsilon-budget-suffices)
                 (:instance rationalp-of-rw-table-epsilon-times-l1)
                 (:instance rationalp-of-rw-table-epsilon-for-output)
                 (:instance rw-table-epsilon-for-output-nonnegative)
                 (:instance dft-output-closep-monotone
                            (small (* (rw-table-epsilon-for-output
                                       output-eps xs)
                                      (rational-list-l1 xs)))
                            (large output-eps)
                            (xs (qwb-rational-input-run
                                 p input-indices kernel-indices
                                 small-terms small-posts xs a))
                            (ys (qwb-rational-input-run
                                 p input-indices kernel-indices
                                 small-terms small-posts xs b))))
           :in-theory nil)))
