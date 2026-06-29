; Finite dyadic search for a nonzero stereographic closure sector.
; The search starts one grid step to the right of zero, so the trivial
; tangent zero is never returned as the left endpoint.
(in-package "ACL2")

(include-book "zco-dyadic-sign-bracket-search")
(include-book "zcm-bisected-stereographic-twiddle")

(defun rts-sector-grid-step (depth n)
  (/ (nfix n) (rds-dyadic-count depth)))

(defun rts-sector-grid-remaining (depth)
  (1- (rds-dyadic-count depth)))

(defun rts-sector-bracket-search (depth n)
  (let ((step (rts-sector-grid-step depth n)))
    (rds-adjacent-bracket-search
     (rts-sector-grid-remaining depth)
     (rts-imag-polynomial n)
     step
     step)))

(defun rts-sector-bracket-existsp (depth n)
  (let ((step (rts-sector-grid-step depth n)))
    (rds-adjacent-bracket-existsp
     (rts-sector-grid-remaining depth)
     (rts-imag-polynomial n)
     step
     step)))

(defun rts-sector-lower (depth n)
  (rpb-lo (rts-sector-bracket-search depth n)))

(defun rts-sector-upper (depth n)
  (rpb-hi (rts-sector-bracket-search depth n)))

(defun rts-sector-radius (depth n)
  (+ 1
     (abs (rts-sector-lower depth n))
     (abs (rts-sector-upper depth n))))

(defthm rationalp-of-rts-sector-grid-step
  (rationalp (rts-sector-grid-step depth n))
  :hints (("Goal"
           :in-theory (enable rts-sector-grid-step rds-dyadic-count)))
  :rule-classes :type-prescription)

(defthm rts-sector-grid-step-nonnegative
  (<= 0 (rts-sector-grid-step depth n))
  :hints (("Goal"
           :in-theory (enable rts-sector-grid-step rds-dyadic-count)
           :nonlinearp t))
  :rule-classes :linear)

(defthm rts-sector-natp-of-one-less-positive
  (implies (and (integerp x) (< 0 x))
           (natp (1- x)))
  :hints (("Goal" :in-theory (enable natp))))

(defthm natp-of-rts-sector-grid-remaining
  (natp (rts-sector-grid-remaining depth))
  :hints (("Goal"
           :use ((:instance posp-of-rds-dyadic-count)
                 (:instance rts-sector-natp-of-one-less-positive
                            (x (rds-dyadic-count depth))))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(rts-sector-grid-remaining posp)))))

(defthm rts-sector-search-consp-iff-exists
  (equal (consp (rts-sector-bracket-search depth n))
         (rts-sector-bracket-existsp depth n))
  :hints (("Goal"
           :use ((:instance rds-search-consp-iff-exists
                            (remaining (rts-sector-grid-remaining depth))
                            (poly (rts-imag-polynomial n))
                            (x (rts-sector-grid-step depth n))
                            (step (rts-sector-grid-step depth n))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(rts-sector-bracket-search
              rts-sector-bracket-existsp)))))

(defthm rts-sector-bracket-search-sound
  (implies (consp (rts-sector-bracket-search depth n))
           (rpb-sign-bracketp
            (rts-imag-polynomial n)
            (rts-sector-bracket-search depth n)))
  :hints (("Goal"
           :use ((:instance rds-adjacent-bracket-search-sound
                            (remaining (rts-sector-grid-remaining depth))
                            (poly (rts-imag-polynomial n))
                            (x (rts-sector-grid-step depth n))
                            (step (rts-sector-grid-step depth n)))
                 (:instance rational-listp-of-rts-imag-polynomial
                            (steps n)))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(rts-sector-bracket-search
              rationalp-of-rts-sector-grid-step
              rts-sector-grid-step-nonnegative)))))

(defthm rts-sector-bracket-search-width
  (implies (consp (rts-sector-bracket-search depth n))
           (equal (rpb-width (rts-sector-bracket-search depth n))
                  (rts-sector-grid-step depth n)))
  :hints (("Goal"
           :use ((:instance rds-adjacent-bracket-search-width
                            (remaining (rts-sector-grid-remaining depth))
                            (poly (rts-imag-polynomial n))
                            (x (rts-sector-grid-step depth n))
                            (step (rts-sector-grid-step depth n))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(rts-sector-bracket-search
              rationalp-of-rts-sector-grid-step)))))

(defthm rationalp-of-rts-sector-lower
  (implies (consp (rts-sector-bracket-search depth n))
           (rationalp (rts-sector-lower depth n)))
  :hints (("Goal"
           :use ((:instance rts-sector-bracket-search-sound)
                 (:instance rpb-sign-bracketp-implies-rationalp-lo
                            (poly (rts-imag-polynomial n))
                            (interval (rts-sector-bracket-search depth n))))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(rts-sector-lower))))
  :rule-classes :type-prescription)

(defthm rationalp-of-rts-sector-upper
  (implies (consp (rts-sector-bracket-search depth n))
           (rationalp (rts-sector-upper depth n)))
  :hints (("Goal"
           :use ((:instance rts-sector-bracket-search-sound)
                 (:instance rpb-sign-bracketp-implies-rationalp-hi
                            (poly (rts-imag-polynomial n))
                            (interval (rts-sector-bracket-search depth n))))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(rts-sector-upper))))
  :rule-classes :type-prescription)

(defthm rationalp-of-rts-sector-radius
  (implies (consp (rts-sector-bracket-search depth n))
           (rationalp (rts-sector-radius depth n)))
  :hints (("Goal"
           :use ((:instance rationalp-of-rts-sector-lower)
                 (:instance rationalp-of-rts-sector-upper)
                 (:instance rationalp-of-rts-abs
                            (x (rts-sector-lower depth n)))
                 (:instance rationalp-of-rts-abs
                            (x (rts-sector-upper depth n))))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(rts-sector-radius))))
  :rule-classes :type-prescription)

(defthm rts-sector-search-complete-and-sound
  (implies (rts-sector-bracket-existsp depth n)
           (and (consp (rts-sector-bracket-search depth n))
                (rpb-sign-bracketp
                 (rts-imag-polynomial n)
                 (rts-sector-bracket-search depth n))))
  :hints (("Goal"
           :use ((:instance rts-sector-search-consp-iff-exists)
                 (:instance rts-sector-bracket-search-sound))
           :in-theory (theory 'minimal-theory))))
