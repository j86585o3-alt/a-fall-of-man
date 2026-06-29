; Certified finite search for rational polynomial sign brackets on uniform
; dyadic grids.  Ordinary ACL2, exact rational arithmetic only.
(in-package "ACL2")

(include-book "zch-rational-polynomial-sign-bisection")

(defun rds-adjacent-bracketp (poly x step)
  (and (<= (tc-poly-eval poly x) 0)
       (<= 0 (tc-poly-eval poly (+ x step)))))

(defun rds-adjacent-bracket-search (remaining poly x step)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (if (rds-adjacent-bracketp poly x step)
        (cons x (+ x step))
      (rds-adjacent-bracket-search
       (1- remaining) poly (+ x step) step))))

(defun rds-adjacent-bracket-existsp (remaining poly x step)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (or (rds-adjacent-bracketp poly x step)
        (rds-adjacent-bracket-existsp
         (1- remaining) poly (+ x step) step))))

(defun rds-dyadic-count (depth)
  (expt 2 (nfix depth)))

(defun rds-dyadic-step (depth lo hi)
  (/ (- hi lo) (rds-dyadic-count depth)))

(defun rds-dyadic-search (depth poly lo hi)
  (rds-adjacent-bracket-search
   (rds-dyadic-count depth)
   poly lo (rds-dyadic-step depth lo hi)))

(defun rds-dyadic-bracket-existsp (depth poly lo hi)
  (rds-adjacent-bracket-existsp
   (rds-dyadic-count depth)
   poly lo (rds-dyadic-step depth lo hi)))

(defthm booleanp-of-rds-adjacent-bracketp
  (booleanp (rds-adjacent-bracketp poly x step))
  :hints (("Goal" :in-theory (enable rds-adjacent-bracketp))))

(defthm booleanp-of-rds-adjacent-bracket-existsp
  (booleanp (rds-adjacent-bracket-existsp remaining poly x step))
  :hints (("Goal"
           :induct (rds-adjacent-bracket-existsp remaining poly x step)
           :in-theory (enable rds-adjacent-bracket-existsp))))

(defthm rationalp-of-rds-next-point
  (implies (and (rationalp x)
                (rationalp step))
           (rationalp (+ x step)))
  :rule-classes :type-prescription)

(defthm rds-adjacent-bracket-head-sound
  (implies (and (rational-listp poly)
                (rationalp x)
                (rationalp step)
                (<= 0 step)
                (rds-adjacent-bracketp poly x step))
           (rpb-sign-bracketp poly (cons x (+ x step))))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(rds-adjacent-bracketp rpb-sign-bracketp
              rpb-lo rpb-hi car-cons cdr-cons)))))

(defthm rds-adjacent-bracket-search-sound
  (implies (and (rational-listp poly)
                (rationalp x)
                (rationalp step)
                (<= 0 step)
                (consp (rds-adjacent-bracket-search
                        remaining poly x step)))
           (rpb-sign-bracketp
            poly
            (rds-adjacent-bracket-search remaining poly x step)))
  :hints (("Goal"
           :induct (rds-adjacent-bracket-search remaining poly x step)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(rds-adjacent-bracket-search
              rationalp-of-rds-next-point)))
          ("Subgoal *1/2"
           :use ((:instance rds-adjacent-bracket-head-sound))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(rds-adjacent-bracket-search)))))

(defthm rds-adjacent-bracket-head-width
  (implies (rationalp step)
           (equal (rpb-width (cons x (+ x step))) step))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(rpb-width rpb-lo rpb-hi car-cons cdr-cons)))))

(defthm rds-adjacent-bracket-search-width
  (implies (and (rationalp step)
                (consp (rds-adjacent-bracket-search
                        remaining poly x step)))
           (equal (rpb-width
                   (rds-adjacent-bracket-search remaining poly x step))
                  step))
  :hints (("Goal"
           :induct (rds-adjacent-bracket-search remaining poly x step)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(rds-adjacent-bracket-search)))
          ("Subgoal *1/2"
           :use ((:instance rds-adjacent-bracket-head-width))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(rds-adjacent-bracket-search)))))

(defthm rds-search-consp-iff-exists
  (equal (consp (rds-adjacent-bracket-search remaining poly x step))
         (rds-adjacent-bracket-existsp remaining poly x step))
  :hints (("Goal"
           :induct (rds-adjacent-bracket-search remaining poly x step)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(rds-adjacent-bracket-search
              rds-adjacent-bracket-existsp)))))

(defthm natp-of-rds-dyadic-count
  (natp (rds-dyadic-count depth))
  :hints (("Goal" :in-theory (enable rds-dyadic-count))))

(defthm posp-of-rds-dyadic-count
  (posp (rds-dyadic-count depth))
  :hints (("Goal" :in-theory (enable rds-dyadic-count posp))))

(defthm rationalp-of-rds-dyadic-step
  (implies (and (rationalp lo)
                (rationalp hi))
           (rationalp (rds-dyadic-step depth lo hi)))
  :hints (("Goal" :in-theory (enable rds-dyadic-step rds-dyadic-count)))
  :rule-classes :type-prescription)

(defthm rds-dyadic-step-nonnegative
  (implies (and (rationalp lo)
                (rationalp hi)
                (<= lo hi))
           (<= 0 (rds-dyadic-step depth lo hi)))
  :hints (("Goal"
           :in-theory (enable rds-dyadic-step rds-dyadic-count)
           :nonlinearp t))
  :rule-classes :linear)

(defthm rds-dyadic-search-sound
  (implies (and (rational-listp poly)
                (rationalp lo)
                (rationalp hi)
                (<= lo hi)
                (consp (rds-dyadic-search depth poly lo hi)))
           (rpb-sign-bracketp
            poly (rds-dyadic-search depth poly lo hi)))
  :hints (("Goal"
           :use ((:instance rds-adjacent-bracket-search-sound
                            (remaining (rds-dyadic-count depth))
                            (x lo)
                            (step (rds-dyadic-step depth lo hi))))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(rds-dyadic-search
                             rationalp-of-rds-dyadic-step
                             rds-dyadic-step-nonnegative)))))

(defthm rds-dyadic-search-width
  (implies (and (rationalp lo)
                (rationalp hi)
                (consp (rds-dyadic-search depth poly lo hi)))
           (equal (rpb-width (rds-dyadic-search depth poly lo hi))
                  (rds-dyadic-step depth lo hi)))
  :hints (("Goal"
           :use ((:instance rds-adjacent-bracket-search-width
                            (remaining (rds-dyadic-count depth))
                            (x lo)
                            (step (rds-dyadic-step depth lo hi))))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(rds-dyadic-search
                             rationalp-of-rds-dyadic-step)))))

(defthm rds-dyadic-search-consp-iff-exists
  (equal (consp (rds-dyadic-search depth poly lo hi))
         (rds-dyadic-bracket-existsp depth poly lo hi))
  :hints (("Goal"
           :use ((:instance rds-search-consp-iff-exists
                            (remaining (rds-dyadic-count depth))
                            (x lo)
                            (step (rds-dyadic-step depth lo hi))))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(rds-dyadic-search
                             rds-dyadic-bracket-existsp)))))

(defthm rds-dyadic-search-complete-and-sound
  (implies (and (rational-listp poly)
                (rationalp lo)
                (rationalp hi)
                (<= lo hi)
                (rds-dyadic-bracket-existsp depth poly lo hi))
           (and (consp (rds-dyadic-search depth poly lo hi))
                (rpb-sign-bracketp
                 poly (rds-dyadic-search depth poly lo hi))))
  :hints (("Goal"
           :use ((:instance rds-dyadic-search-consp-iff-exists)
                 (:instance rds-dyadic-search-sound))
           :in-theory (theory 'minimal-theory))))
