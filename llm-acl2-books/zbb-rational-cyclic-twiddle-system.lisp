; Rational cyclic twiddle construction by a linear multiplication orbit.
(in-package "ACL2")

(include-book "zax-rational-winograd-interface")

(defun qcx-norm-square (z)
  (+ (* (qcx-re z) (qcx-re z))
     (* (qcx-im z) (qcx-im z))))

(defthm qcx-norm-square-of-mul
  (implies (and (qcx-rationalp x)
                (qcx-rationalp y))
           (equal (qcx-norm-square (qcx-mul x y))
                  (* (qcx-norm-square x)
                     (qcx-norm-square y))))
  :hints (("Goal"
           :in-theory (enable qcx-norm-square qcx-mul qcx qcx-re qcx-im
                              qcx-rationalp)
           :nonlinearp t)))

(defthm qcx-norm-square-of-scale
  (implies (and (rationalp a)
                (qcx-rationalp z))
           (equal (qcx-norm-square (qcx-scale a z))
                  (* a a (qcx-norm-square z))))
  :hints (("Goal"
           :in-theory (enable qcx-norm-square qcx-scale qcx qcx-re qcx-im
                              qcx-rationalp)
           :nonlinearp t)))


(defthm rct-square-nonnegative
  (implies (rationalp x)
           (<= 0 (* x x)))
  :hints (("Goal"
           :in-theory (disable normalize-factors-gather-exponents)))
  :rule-classes :linear)

(defun rct-unit-denominator (tangent)
  (+ 1 (* tangent tangent)))

(defun rct-rational-unit (other-chart tangent)
  (let ((denominator (rct-unit-denominator tangent)))
    (qcx-scale
     (/ denominator)
     (qcx (if other-chart
              (- (* tangent tangent) 1)
            (- 1 (* tangent tangent)))
          (* 2 tangent)))))

(defthm rct-unit-denominator-positive
  (implies (rationalp tangent)
           (< 0 (rct-unit-denominator tangent)))
  :hints (("Goal"
           :use ((:instance rct-square-nonnegative (x tangent)))
           :in-theory (enable rct-unit-denominator)))
  :rule-classes :linear)

(defthm rct-stereographic-numerator-identity
  (implies (rationalp tangent)
           (equal (+ (* (- 1 (* tangent tangent))
                        (- 1 (* tangent tangent)))
                     (* (* 2 tangent) (* 2 tangent)))
                  (* (rct-unit-denominator tangent)
                     (rct-unit-denominator tangent))))
  :hints (("Goal"
           :in-theory (enable rct-unit-denominator)
           :nonlinearp t)))

(defthm rct-inverse-square-cancel
  (implies (and (rationalp d)
                (not (equal d 0)))
           (equal (* (/ d) (/ d) d d) 1)))

(defthm qcx-rationalp-of-rct-rational-unit
  (implies (rationalp tangent)
           (qcx-rationalp
            (rct-rational-unit other-chart tangent)))
  :hints (("Goal"
           :use ((:instance rct-unit-denominator-positive)
                 (:instance qcx-rationalp-of-scale
                            (a (/ (rct-unit-denominator tangent)))
                            (z (qcx (if other-chart
                                        (- (* tangent tangent) 1)
                                      (- 1 (* tangent tangent)))
                                    (* 2 tangent)))))
           :in-theory (enable rct-rational-unit
                              rct-unit-denominator
                              qcx-rationalp qcx))))

(defthm qcx-norm-square-of-rct-rational-unit
  (implies (rationalp tangent)
           (equal (qcx-norm-square
                   (rct-rational-unit other-chart tangent))
                  1))
  :hints (("Goal"
           :use ((:instance rct-unit-denominator-positive)
                 (:instance rct-stereographic-numerator-identity)
                 (:instance rct-inverse-square-cancel
                            (d (rct-unit-denominator tangent)))
                 (:instance qcx-norm-square-of-scale
                            (a (/ (rct-unit-denominator tangent)))
                            (z (qcx (if other-chart
                                        (- (* tangent tangent) 1)
                                      (- 1 (* tangent tangent)))
                                    (* 2 tangent)))))
           :in-theory (enable rct-rational-unit
                              qcx-norm-square qcx qcx-re qcx-im))))

(defun rct-advance (steps current seed)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      current
    (rct-advance (1- steps) (qcx-mul current seed) seed)))

(defun rct-power-table-aux (count current seed)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons current
          (rct-power-table-aux (1- count)
                               (qcx-mul current seed)
                               seed))))

(defun rct-power-table (n seed)
  (rct-power-table-aux n (qcx-one) seed))

(defthm len-of-rct-power-table-aux
  (equal (len (rct-power-table-aux count current seed))
         (nfix count))
  :hints (("Goal"
           :induct (rct-power-table-aux count current seed)
           :in-theory (enable rct-power-table-aux))))

(defthm len-of-rct-power-table
  (equal (len (rct-power-table n seed))
         (nfix n))
  :hints (("Goal"
           :in-theory (enable rct-power-table))))

(defthm consp-of-rct-power-table-aux
  (equal (consp (rct-power-table-aux count current seed))
         (not (zp count)))
  :hints (("Goal"
           :induct (rct-power-table-aux count current seed)
           :in-theory (enable rct-power-table-aux))))

(defthm car-of-rct-power-table-aux
  (implies (not (zp count))
           (equal (car (rct-power-table-aux count current seed))
                  current))
  :hints (("Goal"
           :in-theory (enable rct-power-table-aux))))

(defthm cdr-of-rct-power-table-aux
  (implies (not (zp count))
           (equal (cdr (rct-power-table-aux count current seed))
                  (rct-power-table-aux
                   (1- count) (qcx-mul current seed) seed)))
  :hints (("Goal"
           :in-theory (enable rct-power-table-aux))))

(defthm qcx-rationalp-of-rct-advance
  (implies (and (qcx-rationalp current)
                (qcx-rationalp seed))
           (qcx-rationalp (rct-advance steps current seed)))
  :hints (("Goal"
           :induct (rct-advance steps current seed)
           :in-theory (enable rct-advance qcx-rationalp-of-mul))))

(defthm qcx-list-rationalp-of-rct-power-table-aux
  (implies (and (qcx-rationalp current)
                (qcx-rationalp seed))
           (qcx-list-rationalp
            (rct-power-table-aux count current seed)))
  :hints (("Goal"
           :induct (rct-power-table-aux count current seed)
           :in-theory (enable rct-power-table-aux
                              qcx-list-rationalp
                              qcx-rationalp-of-mul))))

(defthm qcx-vectorp-of-rct-power-table
  (implies (qcx-rationalp seed)
           (qcx-vectorp n (rct-power-table n seed)))
  :hints (("Goal"
           :use ((:instance qcx-list-rationalp-of-rct-power-table-aux
                            (count n)
                            (current (qcx-one))))
           :in-theory (enable rct-power-table qcx-vectorp
                              qcx-one qcx qcx-rationalp))))

(defthm qcx-norm-square-of-rct-advance
  (implies (and (qcx-rationalp current)
                (qcx-rationalp seed)
                (equal (qcx-norm-square current) 1)
                (equal (qcx-norm-square seed) 1))
           (equal (qcx-norm-square
                   (rct-advance steps current seed))
                  1))
  :hints (("Goal"
           :induct (rct-advance steps current seed)
           :in-theory (e/d (rct-advance
                            qcx-rationalp-of-mul
                            qcx-norm-square-of-mul)
                           (qcx-norm-square qcx-mul)))))

(defun rct-unit-tablep (table)
  (if (endp table)
      t
    (and (equal (qcx-norm-square (car table)) 1)
         (rct-unit-tablep (cdr table)))))

(defthm rct-unit-tablep-of-power-table-aux
  (implies (and (qcx-rationalp current)
                (qcx-rationalp seed)
                (equal (qcx-norm-square current) 1)
                (equal (qcx-norm-square seed) 1))
           (rct-unit-tablep
            (rct-power-table-aux count current seed)))
  :hints (("Goal"
           :induct (rct-power-table-aux count current seed)
           :in-theory (e/d (rct-power-table-aux
                            rct-unit-tablep
                            qcx-rationalp-of-mul
                            qcx-norm-square-of-mul)
                           (qcx-norm-square qcx-mul)))))

(defthm rct-unit-tablep-of-power-table
  (implies (and (qcx-rationalp seed)
                (equal (qcx-norm-square seed) 1))
           (rct-unit-tablep (rct-power-table n seed)))
  :hints (("Goal"
           :use ((:instance rct-unit-tablep-of-power-table-aux
                            (count n)
                            (current (qcx-one))))
           :in-theory (enable rct-power-table qcx-one qcx
                              qcx-norm-square))))

(defun rct-power-chain-tailp (seed previous tail)
  (if (endp tail)
      t
    (and (equal (car tail) (qcx-mul previous seed))
         (rct-power-chain-tailp seed (car tail) (cdr tail)))))

(defun rct-power-chainp (seed table)
  (and (consp table)
       (equal (car table) (qcx-one))
       (rct-power-chain-tailp seed (car table) (cdr table))))

(defthm rct-power-chain-tailp-of-power-table-aux
  (rct-power-chain-tailp
   seed current
   (rct-power-table-aux count (qcx-mul current seed) seed))
  :hints (("Goal"
           :induct (rct-power-table-aux count current seed)
           :in-theory (e/d (rct-power-table-aux
                            rct-power-chain-tailp)
                           (consp-of-rct-power-table-aux
                            car-of-rct-power-table-aux
                            cdr-of-rct-power-table-aux)))))

(defthm rct-power-chainp-of-power-table
  (implies (and (posp n)
                (qcx-rationalp seed))
           (rct-power-chainp seed (rct-power-table n seed)))
  :hints (("Goal"
           :use ((:instance rct-power-chain-tailp-of-power-table-aux
                            (count (1- n))
                            (current (qcx-one)))
                 (:instance qcx-mul-left-identity (x seed)))
           :in-theory (e/d (rct-power-table
                            rct-power-table-aux
                            rct-power-chainp)
                           (rct-power-chain-tailp-of-power-table-aux
                            qcx-mul-left-identity
                            qcx-mul)))))

(defun rct-separated-orbitp (count current seed separation)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and (< separation (qcx-dist current (qcx-one)))
         (rct-separated-orbitp
          (1- count) (qcx-mul current seed) seed separation))))

(defun rct-table-separated-from-one-p (separation table)
  (if (endp table)
      t
    (and (< separation (qcx-dist (car table) (qcx-one)))
         (rct-table-separated-from-one-p separation (cdr table)))))

(defthm rct-separated-table-of-orbit
  (implies (rct-separated-orbitp count current seed separation)
           (rct-table-separated-from-one-p
            separation
            (rct-power-table-aux count current seed)))
  :hints (("Goal"
           :induct (rct-power-table-aux count current seed)
           :in-theory (enable rct-separated-orbitp
                              rct-table-separated-from-one-p
                              rct-power-table-aux))))

(defun rct-seed-certificatep (n epsilon separation seed)
  (and (posp n)
       (rationalp epsilon)
       (<= 0 epsilon)
       (rationalp separation)
       (< 0 separation)
       (qcx-rationalp seed)
       (equal (qcx-norm-square seed) 1)
       (<= (qcx-dist (rct-advance n (qcx-one) seed)
                     (qcx-one))
           epsilon)
       (rct-separated-orbitp (1- n) seed seed separation)))

(defun rct-twiddle-systemp (n epsilon separation seed table)
  (and (rct-seed-certificatep n epsilon separation seed)
       (qcx-vectorp n table)
       (rct-unit-tablep table)
       (rct-power-chainp seed table)
       (rct-table-separated-from-one-p separation (cdr table))))

(defthm rct-power-table-builder-correct
  (implies (rct-seed-certificatep n epsilon separation seed)
           (rct-twiddle-systemp
            n epsilon separation seed (rct-power-table n seed)))
  :hints (("Goal"
           :use ((:instance qcx-vectorp-of-rct-power-table)
                 (:instance rct-unit-tablep-of-power-table)
                 (:instance rct-power-chainp-of-power-table)
                 (:instance rct-separated-table-of-orbit
                            (count (1- n))
                            (current seed)))
           :in-theory (enable rct-seed-certificatep
                              rct-twiddle-systemp
                              rct-power-table
                              rct-power-table-aux))))

(defun rct-parameter-certificatep
  (n epsilon separation other-chart tangent)
  (and (rationalp tangent)
       (rct-seed-certificatep
        n epsilon separation
        (rct-rational-unit other-chart tangent))))

(defun rct-twiddle-table (n other-chart tangent)
  (rct-power-table n (rct-rational-unit other-chart tangent)))

(defthm qcx-vectorp-of-rct-twiddle-table
  (implies (rationalp tangent)
           (qcx-vectorp n
                        (rct-twiddle-table n other-chart tangent)))
  :hints (("Goal"
           :use ((:instance qcx-vectorp-of-rct-power-table
                            (seed (rct-rational-unit
                                   other-chart tangent)))
                 (:instance qcx-rationalp-of-rct-rational-unit))
           :in-theory (enable rct-twiddle-table))))

(defthm rct-rational-parameter-builder-correct
  (implies
   (rct-parameter-certificatep
    n epsilon separation other-chart tangent)
   (rct-twiddle-systemp
    n epsilon separation
    (rct-rational-unit other-chart tangent)
    (rct-twiddle-table n other-chart tangent)))
  :hints (("Goal"
           :use ((:instance rct-power-table-builder-correct
                            (seed (rct-rational-unit
                                   other-chart tangent))))
           :in-theory
           (union-theories
            '(rct-parameter-certificatep rct-twiddle-table)
            (theory 'minimal-theory)))))

(defthm rct-rational-parameter-is-unit
  (implies (rationalp tangent)
           (rct-unit-tablep
            (rct-twiddle-table n other-chart tangent)))
  :hints (("Goal"
           :use ((:instance rct-unit-tablep-of-power-table
                            (seed (rct-rational-unit
                                   other-chart tangent)))
                 (:instance qcx-norm-square-of-rct-rational-unit))
           :in-theory (enable rct-twiddle-table))))

(defthm rct-rwd-generated-table-correct
  (implies
   (and (rwd-compiled-certifiesp
         p input-indices kernel-indices output-indices
         small-terms small-posts)
        (posp p)
        (rational-listp xs)
        (equal (len xs) (nfix p))
        (rationalp tangent))
   (equal
    (rwd-rational-input-run
     p input-indices kernel-indices small-terms small-posts xs
     (rct-twiddle-table p other-chart tangent))
    (rwd-direct-outputs
     (rwd-compile-outputs output-indices)
     p (qcx-realify xs)
     (rct-twiddle-table p other-chart tangent))))
  :hints (("Goal"
           :use ((:instance rwd-rational-input-run-correct
                            (table (rct-twiddle-table
                                    p other-chart tangent)))
                 (:instance qcx-vectorp-of-rct-twiddle-table
                            (n p)))
           :in-theory nil))
  :rule-classes nil)

(defthm rct-qwb-generated-table-correct
  (implies
   (and (rwd-compiled-certifiesp
         p input-indices kernel-indices output-indices
         small-terms small-posts)
        (wbc-terms-validp
         p (rwd-compile-terms p input-indices kernel-indices small-terms))
        (qwb-posts-rationalp
         (rwd-compile-posts small-terms small-posts))
        (posp p)
        (rational-listp xs)
        (equal (len xs) (nfix p))
        (rationalp tangent))
   (equal
    (qwb-rational-input-run
     p input-indices kernel-indices small-terms small-posts xs
     (rct-twiddle-table p other-chart tangent))
    (rwd-direct-outputs
     (rwd-compile-outputs output-indices)
     p (qcx-realify xs)
     (rct-twiddle-table p other-chart tangent))))
  :hints (("Goal"
           :use ((:instance qwb-rational-input-run-correct
                            (table (rct-twiddle-table
                                    p other-chart tangent)))
                 (:instance qcx-vectorp-of-rct-twiddle-table
                            (n p)))
           :in-theory nil))
  :rule-classes nil)
