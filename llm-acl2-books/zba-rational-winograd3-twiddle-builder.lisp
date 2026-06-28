; Certified rational twiddle construction for the three-point Winograd DFT.
;
; This is ordinary ACL2.  The irrational quantity sqrt(3)/2 is not added to
; the ACL2 universe.  Instead, ZAZ-RATIONAL-UNIT-SQUARE-ROOT constructs a
; shrinking rational interval [lo,hi] whose squared endpoints bracket 3/4.
; From these endpoints this book builds rational conjugate twiddle tables,
; proves their certificate and width, and connects that width to the existing
; three-point Winograd output-error theorem.

(in-package "ACL2")

(include-book "zay-rational-winograd3-client")
(include-book "zaz-rational-unit-square-root")

(defun rw3-sine-interval (precision)
  (rusqrt-build precision 3/4))

(defun rw3-sine-lo (precision)
  (rusqrt-lo (rw3-sine-interval precision)))

(defun rw3-sine-hi (precision)
  (rusqrt-hi (rw3-sine-interval precision)))

(defun rw3-sine-mid (precision)
  (/ (+ (rw3-sine-lo precision)
        (rw3-sine-hi precision))
     2))

(defun rw3-sine-certificatep (lo hi)
  (and (rationalp lo)
       (rationalp hi)
       (<= 0 lo)
       (<= lo hi)
       (<= (* lo lo) 3/4)
       (<= 3/4 (* hi hi))))

(defthm rw3-sine-builder-certificate
  (rw3-sine-certificatep (rw3-sine-lo precision)
                          (rw3-sine-hi precision))
  :hints (("Goal"
           :use ((:instance rationalp-of-rusqrt-build-lo (a 3/4))
                 (:instance rationalp-of-rusqrt-build-hi (a 3/4))
                 (:instance rusqrt-build-lo-nonnegative (a 3/4))
                 (:instance rusqrt-build-lo-at-most-hi (a 3/4))
                 (:instance rusqrt-build-lower-square-bound (a 3/4))
                 (:instance rusqrt-build-upper-square-bound (a 3/4)))
           :in-theory (enable rw3-sine-certificatep
                              rw3-sine-lo rw3-sine-hi
                              rw3-sine-interval))))

(defthm rationalp-of-rw3-sine-lo
  (rationalp (rw3-sine-lo precision))
  :hints (("Goal"
           :use ((:instance rw3-sine-builder-certificate))
           :in-theory (enable rw3-sine-certificatep)))
  :rule-classes :type-prescription)

(defthm rationalp-of-rw3-sine-hi
  (rationalp (rw3-sine-hi precision))
  :hints (("Goal"
           :use ((:instance rw3-sine-builder-certificate))
           :in-theory (enable rw3-sine-certificatep)))
  :rule-classes :type-prescription)

(defthm rationalp-of-rw3-sine-mid
  (rationalp (rw3-sine-mid precision))
  :hints (("Goal"
           :use ((:instance rationalp-of-rw3-sine-lo)
                 (:instance rationalp-of-rw3-sine-hi))
           :in-theory (enable rw3-sine-mid)))
  :rule-classes :type-prescription)

(defthm rw3-sine-lo-nonnegative
  (<= 0 (rw3-sine-lo precision))
  :hints (("Goal"
           :use ((:instance rw3-sine-builder-certificate))
           :in-theory (enable rw3-sine-certificatep)))
  :rule-classes :linear)

(defthm rw3-sine-lo-at-most-hi
  (<= (rw3-sine-lo precision)
      (rw3-sine-hi precision))
  :hints (("Goal"
           :use ((:instance rw3-sine-builder-certificate))
           :in-theory (enable rw3-sine-certificatep)))
  :rule-classes :linear)

(defthm rw3-sine-interval-width
  (equal (rusqrt-width (rw3-sine-interval precision))
         (rusqrt-dyadic-width precision))
  :hints (("Goal"
           :use ((:instance rusqrt-build-width
                            (a 3/4)))
           :in-theory '(rw3-sine-interval))))

(defthm rw3-sine-width
  (equal (- (rw3-sine-hi precision)
            (rw3-sine-lo precision))
         (rusqrt-dyadic-width precision))
  :hints (("Goal"
           :use ((:instance rw3-sine-interval-width))
           :in-theory '(rw3-sine-hi rw3-sine-lo rusqrt-width))))


; A simple total precision selector.  For positive rational eps, its
; denominator is a conservative bisection count.  The proof uses
; 2^n >= n+1 in the equivalent dyadic-width form, and the fact that the
; numerator of a positive rational is at least one.
(defthm rusqrt-dyadic-width-upper-bound
  (implies (natp n)
           (<= (rusqrt-dyadic-width n)
               (/ (+ 1 n))))
  :hints (("Goal"
           :induct (rusqrt-dyadic-width n)
           :in-theory (enable rusqrt-dyadic-width)
           :nonlinearp t))
  :rule-classes :linear)

(defthm reciprocal-one-plus-denominator-below-positive-rational
  (implies (and (rationalp eps)
                (< 0 eps))
           (<= (/ (+ 1 (denominator eps))) eps))
  :hints (("Goal"
           :use ((:instance rational-implies2 (x eps))
                 (:instance numerator-positive (x eps)))
           :nonlinearp t))
  :rule-classes :linear)

(defun rw3-precision-fuel-bound (eps)
  (if (and (rationalp eps)
           (< 0 eps))
      (denominator eps)
    0))

(defthm natp-of-rw3-precision-fuel-bound
  (natp (rw3-precision-fuel-bound eps))
  :hints (("Goal"
           :in-theory (enable rw3-precision-fuel-bound))))

(defthm rw3-precision-fuel-bound-suffices
  (implies (and (rationalp eps)
                (< 0 eps))
           (<= (rusqrt-dyadic-width
                (rw3-precision-fuel-bound eps))
               eps))
  :hints (("Goal"
           :use ((:instance rusqrt-dyadic-width-upper-bound
                            (n (denominator eps)))
                 (:instance reciprocal-one-plus-denominator-below-positive-rational))
           :in-theory (enable rw3-precision-fuel-bound))))

(defun rw3-precision-search (fuel precision eps)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel)
          (<= (rusqrt-dyadic-width precision) eps))
      (nfix precision)
    (rw3-precision-search (1- fuel)
                          (1+ (nfix precision))
                          eps)))

(defthm natp-of-rw3-precision-search
  (natp (rw3-precision-search fuel precision eps))
  :hints (("Goal"
           :induct (rw3-precision-search fuel precision eps)
           :in-theory (enable rw3-precision-search))))

(defthm rw3-precision-search-suffices
  (implies (and (natp fuel)
                (natp precision)
                (<= (rusqrt-dyadic-width (+ fuel precision)) eps))
           (<= (rusqrt-dyadic-width
                (rw3-precision-search fuel precision eps))
               eps))
  :hints (("Goal"
           :induct (rw3-precision-search fuel precision eps)
           :in-theory (enable rw3-precision-search))))

(defun rw3-precision-for-epsilon (eps)
  (if (and (rationalp eps)
           (< 0 eps))
      (rw3-precision-search (rw3-precision-fuel-bound eps) 0 eps)
    0))

(defthm natp-of-rw3-precision-for-epsilon
  (natp (rw3-precision-for-epsilon eps))
  :hints (("Goal"
           :use ((:instance natp-of-rw3-precision-search
                            (fuel (rw3-precision-fuel-bound eps))
                            (precision 0)))
           :in-theory (enable rw3-precision-for-epsilon))))

(defthm rw3-precision-for-epsilon-suffices
  (implies (and (rationalp eps)
                (< 0 eps))
           (<= (rusqrt-dyadic-width
                (rw3-precision-for-epsilon eps))
               eps))
  :hints (("Goal"
           :use ((:instance natp-of-rw3-precision-fuel-bound)
                 (:instance rw3-precision-fuel-bound-suffices)
                 (:instance rw3-precision-search-suffices
                            (fuel (rw3-precision-fuel-bound eps))
                            (precision 0)))
           :in-theory (enable rw3-precision-for-epsilon))))

(defun rw3-twiddle-table-from-sine (s)
  (list (qcx 1 0)
        (qcx -1/2 (- s))
        (qcx -1/2 s)))

(defun rw3-twiddle-table-lo (precision)
  (rw3-twiddle-table-from-sine (rw3-sine-lo precision)))

(defun rw3-twiddle-table-hi (precision)
  (rw3-twiddle-table-from-sine (rw3-sine-hi precision)))

(defun rw3-twiddle-table-mid (precision)
  (rw3-twiddle-table-from-sine (rw3-sine-mid precision)))


; The public approximation builder returns the midpoint table.  The companion
; lower and upper tables remain available as a checkable rational certificate.
(defun rw3-twiddle-table-for-epsilon (eps)
  (rw3-twiddle-table-mid (rw3-precision-for-epsilon eps)))
(defthm qcx-vectorp-of-rw3-twiddle-table-from-sine
  (implies (rationalp s)
           (qcx-vectorp 3 (rw3-twiddle-table-from-sine s)))
  :hints (("Goal"
           :in-theory (enable rw3-twiddle-table-from-sine
                              qcx-vectorp qcx-list-rationalp
                              qcx-rationalp qcx))))

(defthm qcx-vectorp-of-rw3-twiddle-table-lo
  (qcx-vectorp 3 (rw3-twiddle-table-lo precision))
  :hints (("Goal"
           :use ((:instance qcx-vectorp-of-rw3-twiddle-table-from-sine
                            (s (rw3-sine-lo precision)))
                 (:instance rationalp-of-rw3-sine-lo))
           :in-theory '(rw3-twiddle-table-lo))))

(defthm qcx-vectorp-of-rw3-twiddle-table-hi
  (qcx-vectorp 3 (rw3-twiddle-table-hi precision))
  :hints (("Goal"
           :use ((:instance qcx-vectorp-of-rw3-twiddle-table-from-sine
                            (s (rw3-sine-hi precision)))
                 (:instance rationalp-of-rw3-sine-hi))
           :in-theory '(rw3-twiddle-table-hi))))

(defthm qcx-vectorp-of-rw3-twiddle-table-mid
  (qcx-vectorp 3 (rw3-twiddle-table-mid precision))
  :hints (("Goal"
           :use ((:instance qcx-vectorp-of-rw3-twiddle-table-from-sine
                            (s (rw3-sine-mid precision)))
                 (:instance rationalp-of-rw3-sine-mid))
           :in-theory '(rw3-twiddle-table-mid))))


(defthm qcx-vectorp-of-rw3-twiddle-table-for-epsilon
  (qcx-vectorp 3 (rw3-twiddle-table-for-epsilon eps))
  :hints (("Goal"
           :use ((:instance qcx-vectorp-of-rw3-twiddle-table-mid
                            (precision (rw3-precision-for-epsilon eps))))
           :in-theory '(rw3-twiddle-table-for-epsilon))))
(defthm rw3-twiddle-table-from-sine-conjugate-pair
  (and (equal (nth 0 (rw3-twiddle-table-from-sine s))
              (qcx 1 0))
       (equal (qcx-re (nth 1 (rw3-twiddle-table-from-sine s))) -1/2)
       (equal (qcx-re (nth 2 (rw3-twiddle-table-from-sine s))) -1/2)
       (equal (qcx-im (nth 1 (rw3-twiddle-table-from-sine s))) (- s))
       (equal (qcx-im (nth 2 (rw3-twiddle-table-from-sine s))) s))
  :hints (("Goal"
           :in-theory (enable rw3-twiddle-table-from-sine
                              qcx qcx-re qcx-im))))

(defthm qcx-dist-of-rw3-twiddles-from-sines
  (implies (and (rationalp a)
                (rationalp b)
                (<= a b))
           (and (equal (qcx-dist (qcx -1/2 (- a))
                                 (qcx -1/2 (- b)))
                       (- b a))
                (equal (qcx-dist (qcx -1/2 a)
                                 (qcx -1/2 b))
                       (- b a))))
  :hints (("Goal"
           :in-theory (enable qcx-dist qcx-l1 qcx-sub qcx-add qcx-neg
                              qcx qcx-re qcx-im abs))))

(defthm rw3-generated-twiddle-tables-close
  (qcx-table-closep
   (rusqrt-dyadic-width precision)
   (rw3-twiddle-table-lo precision)
   (rw3-twiddle-table-hi precision))
  :hints (("Goal"
           :use ((:instance rw3-sine-lo-at-most-hi)
                 (:instance rw3-sine-width)
                 (:instance qcx-dist-of-rw3-twiddles-from-sines
                            (a (rw3-sine-lo precision))
                            (b (rw3-sine-hi precision))))
           :in-theory (enable rw3-twiddle-table-lo
                              rw3-twiddle-table-hi
                              rw3-twiddle-table-from-sine
                              qcx-table-closep qcx-dist qcx-l1
                              qcx-sub qcx-add qcx-neg qcx
                              qcx-re qcx-im abs))))


(defthm rw3-generated-mid-table-close-to-lo
  (qcx-table-closep
   (rusqrt-dyadic-width precision)
   (rw3-twiddle-table-mid precision)
   (rw3-twiddle-table-lo precision))
  :hints (("Goal"
           :use ((:instance rw3-sine-lo-at-most-hi)
                 (:instance rw3-sine-width)
                 (:instance rationalp-of-rw3-sine-lo)
                 (:instance rationalp-of-rw3-sine-hi))
           :in-theory (enable rw3-twiddle-table-mid
                              rw3-twiddle-table-lo
                              rw3-twiddle-table-from-sine
                              rw3-sine-mid qcx-table-closep
                              qcx-dist qcx-l1 qcx-sub qcx-add qcx-neg
                              qcx qcx-re qcx-im abs))))

(defthm rw3-generated-mid-table-close-to-hi
  (qcx-table-closep
   (rusqrt-dyadic-width precision)
   (rw3-twiddle-table-mid precision)
   (rw3-twiddle-table-hi precision))
  :hints (("Goal"
           :use ((:instance rw3-sine-lo-at-most-hi)
                 (:instance rw3-sine-width)
                 (:instance rationalp-of-rw3-sine-lo)
                 (:instance rationalp-of-rw3-sine-hi))
           :in-theory (enable rw3-twiddle-table-mid
                              rw3-twiddle-table-hi
                              rw3-twiddle-table-from-sine
                              rw3-sine-mid qcx-table-closep
                              qcx-dist qcx-l1 qcx-sub qcx-add qcx-neg
                              qcx qcx-re qcx-im abs))))
(defthm rw3-qcx-table-closep-monotone
  (implies (and (qcx-table-closep small xs ys)
                (<= small large))
           (qcx-table-closep large xs ys))
  :hints (("Goal"
           :induct (qcx-table-closep small xs ys)
           :in-theory (enable qcx-table-closep))))


(defthm rw3-generated-twiddle-tables-close-for-epsilon
  (implies (and (rationalp eps)
                (< 0 eps))
           (qcx-table-closep
            eps
            (rw3-twiddle-table-lo (rw3-precision-for-epsilon eps))
            (rw3-twiddle-table-hi (rw3-precision-for-epsilon eps))))
  :hints (("Goal"
           :use ((:instance rw3-generated-twiddle-tables-close
                            (precision (rw3-precision-for-epsilon eps)))
                 (:instance rw3-precision-for-epsilon-suffices)
                 (:instance rw3-qcx-table-closep-monotone
                            (small (rusqrt-dyadic-width
                                    (rw3-precision-for-epsilon eps)))
                            (large eps)
                            (xs (rw3-twiddle-table-lo
                                 (rw3-precision-for-epsilon eps)))
                            (ys (rw3-twiddle-table-hi
                                 (rw3-precision-for-epsilon eps)))))
           :in-theory nil)))


(defthm rw3-built-twiddle-table-close-to-certificate
  (implies (and (rationalp eps)
                (< 0 eps))
           (and
            (qcx-table-closep
             eps
             (rw3-twiddle-table-for-epsilon eps)
             (rw3-twiddle-table-lo (rw3-precision-for-epsilon eps)))
            (qcx-table-closep
             eps
             (rw3-twiddle-table-for-epsilon eps)
             (rw3-twiddle-table-hi (rw3-precision-for-epsilon eps)))))
  :hints (("Goal"
           :use ((:instance rw3-generated-mid-table-close-to-lo
                            (precision (rw3-precision-for-epsilon eps)))
                 (:instance rw3-generated-mid-table-close-to-hi
                            (precision (rw3-precision-for-epsilon eps)))
                 (:instance rw3-precision-for-epsilon-suffices)
                 (:instance rw3-qcx-table-closep-monotone
                            (small (rusqrt-dyadic-width
                                    (rw3-precision-for-epsilon eps)))
                            (large eps)
                            (xs (rw3-twiddle-table-mid
                                 (rw3-precision-for-epsilon eps)))
                            (ys (rw3-twiddle-table-lo
                                 (rw3-precision-for-epsilon eps))))
                 (:instance rw3-qcx-table-closep-monotone
                            (small (rusqrt-dyadic-width
                                    (rw3-precision-for-epsilon eps)))
                            (large eps)
                            (xs (rw3-twiddle-table-mid
                                 (rw3-precision-for-epsilon eps)))
                            (ys (rw3-twiddle-table-hi
                                 (rw3-precision-for-epsilon eps)))))
           :in-theory '(rw3-twiddle-table-for-epsilon))))
(defthm rw-table-epsilon-for-positive-output-positive
  (implies (and (rationalp output-eps)
                (< 0 output-eps)
                (rational-listp xs))
           (< 0 (rw-table-epsilon-for-output output-eps xs)))
  :hints (("Goal"
           :use ((:instance reciprocal-one-plus-rational-list-l1-positive))
           :in-theory (enable rw-table-epsilon-for-output)))
  :rule-classes :linear)
(defthm rw3-generated-winograd-outputs-close
  (implies (and (rational-listp xs)
                (equal (len xs) 3)
                (rationalp output-eps)
                (<= 0 output-eps)
                (<= (rusqrt-dyadic-width precision)
                    (rw-table-epsilon-for-output output-eps xs)))
           (dft-output-closep
            output-eps
            (rw3-rational-winograd xs
                                   (rw3-twiddle-table-lo precision))
            (rw3-rational-winograd xs
                                   (rw3-twiddle-table-hi precision))))
  :hints (("Goal"
           :use ((:instance rw3-rational-winograd-requested-output-tolerance
                            (a (rw3-twiddle-table-lo precision))
                            (b (rw3-twiddle-table-hi precision)))
                 (:instance rw3-generated-twiddle-tables-close)
                 (:instance rw3-qcx-table-closep-monotone
                            (small (rusqrt-dyadic-width precision))
                            (large (rw-table-epsilon-for-output output-eps xs))
                            (xs (rw3-twiddle-table-lo precision))
                            (ys (rw3-twiddle-table-hi precision)))
                 (:instance qcx-vectorp-of-rw3-twiddle-table-lo)
                 (:instance qcx-vectorp-of-rw3-twiddle-table-hi))
           :in-theory nil)))

(defthm rw3-generated-adp-outputs-close
  (implies (and (rational-listp xs)
                (equal (len xs) 3)
                (rationalp output-eps)
                (<= 0 output-eps)
                (<= (rusqrt-dyadic-width precision)
                    (rw-table-epsilon-for-output output-eps xs)))
           (dft-output-closep
            output-eps
            (rw3-rational-adp xs
                              (rw3-twiddle-table-lo precision))
            (rw3-rational-adp xs
                              (rw3-twiddle-table-hi precision))))
  :hints (("Goal"
           :use ((:instance rw3-rational-adp-requested-output-tolerance
                            (a (rw3-twiddle-table-lo precision))
                            (b (rw3-twiddle-table-hi precision)))
                 (:instance rw3-generated-twiddle-tables-close)
                 (:instance rw3-qcx-table-closep-monotone
                            (small (rusqrt-dyadic-width precision))
                            (large (rw-table-epsilon-for-output output-eps xs))
                            (xs (rw3-twiddle-table-lo precision))
                            (ys (rw3-twiddle-table-hi precision)))
                 (:instance qcx-vectorp-of-rw3-twiddle-table-lo)
                 (:instance qcx-vectorp-of-rw3-twiddle-table-hi))
           :in-theory nil)))


(defun rw3-output-precision (output-eps xs)
  (rw3-precision-for-epsilon
   (rw-table-epsilon-for-output output-eps xs)))

(defthm rw3-output-precision-suffices
  (implies (and (rational-listp xs)
                (rationalp output-eps)
                (< 0 output-eps))
           (<= (rusqrt-dyadic-width
                (rw3-output-precision output-eps xs))
               (rw-table-epsilon-for-output output-eps xs)))
  :hints (("Goal"
           :use ((:instance rw-table-epsilon-for-positive-output-positive)
                 (:instance rationalp-of-rw-table-epsilon-for-output)
                 (:instance rw3-precision-for-epsilon-suffices
                            (eps (rw-table-epsilon-for-output output-eps xs))))
           :in-theory '(rw3-output-precision))))

(defthm rw3-built-winograd-outputs-meet-positive-request
  (implies (and (rational-listp xs)
                (equal (len xs) 3)
                (rationalp output-eps)
                (< 0 output-eps))
           (dft-output-closep
            output-eps
            (rw3-rational-winograd
             xs (rw3-twiddle-table-lo
                 (rw3-output-precision output-eps xs)))
            (rw3-rational-winograd
             xs (rw3-twiddle-table-hi
                 (rw3-output-precision output-eps xs)))))
  :hints (("Goal"
           :use ((:instance rw3-output-precision-suffices)
                 (:instance rw3-generated-winograd-outputs-close
                            (precision (rw3-output-precision output-eps xs))))
           :in-theory nil)))

(defthm rw3-built-adp-outputs-meet-positive-request
  (implies (and (rational-listp xs)
                (equal (len xs) 3)
                (rationalp output-eps)
                (< 0 output-eps))
           (dft-output-closep
            output-eps
            (rw3-rational-adp
             xs (rw3-twiddle-table-lo
                 (rw3-output-precision output-eps xs)))
            (rw3-rational-adp
             xs (rw3-twiddle-table-hi
                 (rw3-output-precision output-eps xs)))))
  :hints (("Goal"
           :use ((:instance rw3-output-precision-suffices)
                 (:instance rw3-generated-adp-outputs-close
                            (precision (rw3-output-precision output-eps xs))))
           :in-theory nil)))
; A small executable landmark.  Ten bisections already give a width of 1/1024.
(defthm rw3-sine-width-at-precision-10
  (equal (rusqrt-dyadic-width 10) 1/1024))

(defthm rw3-sine-interval-at-precision-10
  (equal (rw3-sine-interval 10)
         (cons 443/512 887/1024))
  :hints (("Goal"
           :in-theory (enable rw3-sine-interval rusqrt-build
                              rusqrt-iterate rusqrt-step
                              rusqrt-midpoint rusqrt-lo rusqrt-hi))))

(defthm rw3-precision-for-one-thousandth
  (equal (rw3-precision-for-epsilon 1/1000) 10)
  :hints (("Goal"
           :in-theory (enable rw3-precision-for-epsilon
                              rw3-precision-fuel-bound
                              rw3-precision-search
                              rusqrt-dyadic-width))))

(defthm rw3-output-precision-for-smoke-input
  (equal (rw3-output-precision 1/1000 '(1 2 3)) 13)
  :hints (("Goal"
           :in-theory (enable rw3-output-precision
                              rw-table-epsilon-for-output
                              rational-list-l1
                              rw3-precision-for-epsilon
                              rw3-precision-fuel-bound
                              rw3-precision-search
                              rusqrt-dyadic-width))))
