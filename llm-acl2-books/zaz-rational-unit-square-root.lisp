; Certified dyadic bisection for square roots of rationals in [0,1].
;
; This is ordinary ACL2.  It does not introduce real numbers.  Instead it
; returns a rational interval whose endpoints enclose any nonnegative square
; root in the elementary order/squaring sense, and proves that the interval
; width is exactly 2^(-precision).

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

(defun rusqrt-lo (interval)
  (if (consp interval) (car interval) 0))

(defun rusqrt-hi (interval)
  (if (consp interval) (cdr interval) 0))

(defun rusqrt-width (interval)
  (- (rusqrt-hi interval) (rusqrt-lo interval)))

(defun rusqrt-midpoint (interval)
  (/ (+ (rusqrt-lo interval) (rusqrt-hi interval)) 2))

(defun rusqrt-enclosesp (a interval)
  (and (rationalp a)
       (<= 0 a)
       (rationalp (rusqrt-lo interval))
       (rationalp (rusqrt-hi interval))
       (<= 0 (rusqrt-lo interval))
       (<= (rusqrt-lo interval) (rusqrt-hi interval))
       (<= (* (rusqrt-lo interval) (rusqrt-lo interval)) a)
       (<= a (* (rusqrt-hi interval) (rusqrt-hi interval)))))


(defthm rusqrt-enclosesp-implies-rationalp-lo
  (implies (rusqrt-enclosesp a interval)
           (rationalp (rusqrt-lo interval)))
  :hints (("Goal" :in-theory (enable rusqrt-enclosesp))))

(defthm rusqrt-enclosesp-implies-rationalp-hi
  (implies (rusqrt-enclosesp a interval)
           (rationalp (rusqrt-hi interval)))
  :hints (("Goal" :in-theory (enable rusqrt-enclosesp))))

(defthm rusqrt-enclosesp-implies-lo-nonnegative
  (implies (rusqrt-enclosesp a interval)
           (<= 0 (rusqrt-lo interval)))
  :hints (("Goal" :in-theory (enable rusqrt-enclosesp)))
  :rule-classes :linear)

(defthm rusqrt-enclosesp-implies-lo-at-most-hi
  (implies (rusqrt-enclosesp a interval)
           (<= (rusqrt-lo interval) (rusqrt-hi interval)))
  :hints (("Goal" :in-theory (enable rusqrt-enclosesp)))
  :rule-classes :linear)

(defthm rusqrt-enclosesp-implies-lower-square-bound
  (implies (rusqrt-enclosesp a interval)
           (<= (* (rusqrt-lo interval) (rusqrt-lo interval)) a))
  :hints (("Goal" :in-theory (enable rusqrt-enclosesp)))
  :rule-classes :linear)

(defthm rusqrt-enclosesp-implies-upper-square-bound
  (implies (rusqrt-enclosesp a interval)
           (<= a (* (rusqrt-hi interval) (rusqrt-hi interval))))
  :hints (("Goal" :in-theory (enable rusqrt-enclosesp)))
  :rule-classes :linear)

(defun rusqrt-step (a interval)
  (let ((mid (rusqrt-midpoint interval)))
    (if (<= (* mid mid) a)
        (cons mid (rusqrt-hi interval))
      (cons (rusqrt-lo interval) mid))))

(defun rusqrt-iterate (precision a interval)
  (declare (xargs :measure (nfix precision)))
  (if (zp precision)
      interval
    (rusqrt-iterate (1- precision) a (rusqrt-step a interval))))

(defun rusqrt-build (precision a)
  (rusqrt-iterate precision a (cons 0 1)))

(defun rusqrt-dyadic-width (precision)
  (declare (xargs :measure (nfix precision)))
  (if (zp precision)
      1
    (/ (rusqrt-dyadic-width (1- precision)) 2)))

(defthm rationalp-of-rusqrt-midpoint
  (implies (and (rationalp (rusqrt-lo interval))
                (rationalp (rusqrt-hi interval)))
           (rationalp (rusqrt-midpoint interval)))
  :rule-classes :type-prescription)

(defthm rusqrt-lo-at-most-midpoint
  (implies (and (rationalp (rusqrt-lo interval))
                (rationalp (rusqrt-hi interval))
                (<= (rusqrt-lo interval) (rusqrt-hi interval)))
           (<= (rusqrt-lo interval) (rusqrt-midpoint interval)))
  :rule-classes :linear)

(defthm rusqrt-midpoint-at-most-hi
  (implies (and (rationalp (rusqrt-lo interval))
                (rationalp (rusqrt-hi interval))
                (<= (rusqrt-lo interval) (rusqrt-hi interval)))
           (<= (rusqrt-midpoint interval) (rusqrt-hi interval)))
  :rule-classes :linear)

(defthm rusqrt-width-of-step
  (implies (and (rationalp (rusqrt-lo interval))
                (rationalp (rusqrt-hi interval)))
           (equal (rusqrt-width (rusqrt-step a interval))
                  (/ (rusqrt-width interval) 2)))
  :hints (("Goal" :in-theory (enable rusqrt-step rusqrt-width
                                      rusqrt-midpoint rusqrt-lo rusqrt-hi))))

(defthm rusqrt-enclosesp-of-step
  (implies (rusqrt-enclosesp a interval)
           (rusqrt-enclosesp a (rusqrt-step a interval)))
  :hints (("Goal"
           :in-theory (enable rusqrt-enclosesp rusqrt-step
                              rusqrt-midpoint rusqrt-lo rusqrt-hi)
           :nonlinearp t)))

(defthm rusqrt-enclosesp-of-iterate
  (implies (rusqrt-enclosesp a interval)
           (rusqrt-enclosesp a
                             (rusqrt-iterate precision a interval)))
  :hints (("Goal" :induct (rusqrt-iterate precision a interval)
           :in-theory (enable rusqrt-iterate))))

(defthm rusqrt-iterate-width
  (implies (and (rationalp (rusqrt-lo interval))
                (rationalp (rusqrt-hi interval)))
           (equal (rusqrt-width (rusqrt-iterate precision a interval))
                  (* (rusqrt-dyadic-width precision)
                     (rusqrt-width interval))))
  :hints (("Goal" :induct (rusqrt-iterate precision a interval)
           :in-theory (enable rusqrt-iterate rusqrt-dyadic-width))))

(defthm rationalp-of-rusqrt-dyadic-width
  (rationalp (rusqrt-dyadic-width precision))
  :rule-classes :type-prescription)

(defthm rusqrt-dyadic-width-positive
  (< 0 (rusqrt-dyadic-width precision))
  :rule-classes :linear)

(defthm rusqrt-dyadic-width-of-successor
  (implies (natp precision)
           (equal (rusqrt-dyadic-width (1+ precision))
                  (/ (rusqrt-dyadic-width precision) 2)))
  :hints (("Goal" :expand ((rusqrt-dyadic-width (1+ precision))))))

(defthm rusqrt-build-encloses-unit-target
  (implies (and (rationalp a)
                (<= 0 a)
                (<= a 1))
           (rusqrt-enclosesp a (rusqrt-build precision a)))
  :hints (("Goal"
           :use ((:instance rusqrt-enclosesp-of-iterate
                            (interval (cons 0 1))))
           :in-theory (enable rusqrt-build rusqrt-enclosesp
                              rusqrt-lo rusqrt-hi))))

(defthm rusqrt-build-width
  (equal (rusqrt-width (rusqrt-build precision a))
         (rusqrt-dyadic-width precision))
  :hints (("Goal"
           :use ((:instance rusqrt-iterate-width
                            (interval (cons 0 1))))
           :in-theory (enable rusqrt-build rusqrt-width
                              rusqrt-lo rusqrt-hi))))

(defthm rationalp-of-rusqrt-build-lo
  (implies (and (rationalp a)
                (<= 0 a)
                (<= a 1))
           (rationalp (rusqrt-lo (rusqrt-build precision a))))
  :hints (("Goal"
           :use ((:instance rusqrt-build-encloses-unit-target)
                 (:instance rusqrt-enclosesp-implies-rationalp-lo
                            (interval (rusqrt-build precision a))))
           :in-theory nil))
  :rule-classes :type-prescription)

(defthm rationalp-of-rusqrt-build-hi
  (implies (and (rationalp a)
                (<= 0 a)
                (<= a 1))
           (rationalp (rusqrt-hi (rusqrt-build precision a))))
  :hints (("Goal"
           :use ((:instance rusqrt-build-encloses-unit-target)
                 (:instance rusqrt-enclosesp-implies-rationalp-hi
                            (interval (rusqrt-build precision a))))
           :in-theory nil))
  :rule-classes :type-prescription)

(defthm rusqrt-build-lo-nonnegative
  (implies (and (rationalp a)
                (<= 0 a)
                (<= a 1))
           (<= 0 (rusqrt-lo (rusqrt-build precision a))))
  :hints (("Goal"
           :use ((:instance rusqrt-build-encloses-unit-target)
                 (:instance rusqrt-enclosesp-implies-lo-nonnegative
                            (interval (rusqrt-build precision a))))
           :in-theory nil))
  :rule-classes :linear)

(defthm rusqrt-build-lo-at-most-hi
  (implies (and (rationalp a)
                (<= 0 a)
                (<= a 1))
           (<= (rusqrt-lo (rusqrt-build precision a))
               (rusqrt-hi (rusqrt-build precision a))))
  :hints (("Goal"
           :use ((:instance rusqrt-build-encloses-unit-target)
                 (:instance rusqrt-enclosesp-implies-lo-at-most-hi
                            (interval (rusqrt-build precision a))))
           :in-theory nil))
  :rule-classes :linear)

(defthm rusqrt-build-lower-square-bound
  (implies (and (rationalp a)
                (<= 0 a)
                (<= a 1))
           (<= (* (rusqrt-lo (rusqrt-build precision a))
                  (rusqrt-lo (rusqrt-build precision a)))
               a))
  :hints (("Goal"
           :use ((:instance rusqrt-build-encloses-unit-target)
                 (:instance rusqrt-enclosesp-implies-lower-square-bound
                            (interval (rusqrt-build precision a))))
           :in-theory nil))
  :rule-classes :linear)

(defthm rusqrt-build-upper-square-bound
  (implies (and (rationalp a)
                (<= 0 a)
                (<= a 1))
           (<= a
               (* (rusqrt-hi (rusqrt-build precision a))
                  (rusqrt-hi (rusqrt-build precision a)))))
  :hints (("Goal"
           :use ((:instance rusqrt-build-encloses-unit-target)
                 (:instance rusqrt-enclosesp-implies-upper-square-bound
                            (interval (rusqrt-build precision a))))
           :in-theory nil))
  :rule-classes :linear)
