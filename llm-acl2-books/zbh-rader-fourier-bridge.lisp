; Compact completion of the scalar-to-Fourier bridge for Rader plans.
(in-package "ACL2")
(include-book "zbg-compact-rader-certificate")

(defthm rfb-constant-row-is-repeat
  (equal (rwd-constant-row-aux count value)
         (repeat (nfix count) value))
  :hints (("Goal"
           :induct (rwd-constant-row-aux count value)
           :in-theory (enable rwd-constant-row-aux repeat))))

(defthm rfb-nth0-of-constant-row
  (implies (and (natp k) (< k (nfix count)))
           (equal (tc-nth0 k (rwd-constant-row-aux count value))
                  value))
  :hints (("Goal"
           :use ((:instance tc-nth0-is-nth-when-in-bounds
                            (xs (rwd-constant-row-aux count value)))
                 (:instance nth-of-repeat
                            (n k) (m (nfix count)) (a value)))
           :in-theory (enable rfb-constant-row-is-repeat))))


(defthm rfb-unit-row-after-zero
  (implies (posp index)
           (equal (rwd-unit-row-aux count index 0)
                  (rwd-constant-row-aux count 0)))
  :hints (("Goal"
           :induct (rwd-unit-row-aux count index 0)
           :in-theory (e/d (rwd-unit-row-aux
                                rwd-constant-row-aux)
                               (rfb-constant-row-is-repeat)))))

(defthm rfb-unit-row-zero-open
  (implies (posp p)
           (equal (rwd-unit-row p 0)
                  (cons 1 (rwd-constant-row-aux (1- p) 0))))
  :hints (("Goal"
           :use ((:instance rfb-unit-row-after-zero
                            (count (1- p)) (index 1)))
           :in-theory (enable rwd-unit-row rwd-unit-row-aux))))

(defthm rfb-nth0-of-unit-row-zero
  (implies (and (posp p) (natp k) (< k p))
           (equal (tc-nth0 k (rwd-unit-row p 0))
                  (if (equal k 0) 1 0)))
  :hints (("Goal" :cases ((equal k 0))
           :use ((:instance rfb-unit-row-zero-open)
                 (:instance rfb-nth0-of-constant-row
                            (count (1- p)) (value 0) (k (1- k))))
           :in-theory (e/d (tc-nth0) (rgi-not-less-implies-ge)))))


(defthm rfb-len-of-unit-row
  (equal (len (rwd-unit-row p position)) (nfix p))
  :hints (("Goal"
           :use ((:instance len-of-rwd-unit-row-aux
                            (count p) (index 0)))
           :in-theory (enable rwd-unit-row))))

(defthm rfb-entry-of-dc-term-one
  (implies (and (posp p)
                (natp row) (< row p)
                (natp column) (< column p))
           (equal (tc-matrix-entry row column
                                   (wbc-term-matrix (rwd-dc-term p) 1))
                  (if (equal column 0) 1 0)))
  :hints (("Goal" :cases ((equal column 0))
           :use ((:instance rgi-entry-of-wbc-term-matrix-general
                            (left (rwd-constant-row-aux p 1))
                            (right (rwd-unit-row p 0))
                            (coefficient 1))
                 (:instance rfb-nth0-of-constant-row
                            (count p) (value 1) (k row))
                 (:instance rfb-nth0-of-unit-row-zero
                            (k column))
                 (:instance len-of-rwd-constant-row-aux
                            (count p) (value 1))
                 (:instance rfb-len-of-unit-row
                            (position 0)))
           :in-theory '(rwd-dc-term rgi-nfix-when-posp))))

(defthm rfb-entry-of-dc-term-zero
  (implies (and (posp p)
                (natp row) (< row p)
                (natp column) (< column p))
           (equal (tc-matrix-entry row column
                                   (wbc-term-matrix (rwd-dc-term p) 0))
                  0))
  :hints (("Goal"
           :use ((:instance rgi-entry-of-wbc-term-matrix-general
                            (left (rwd-constant-row-aux p 1))
                            (right (rwd-unit-row p 0))
                            (coefficient 0))
                 (:instance len-of-rwd-constant-row-aux
                            (count p) (value 1))
                 (:instance rfb-len-of-unit-row
                            (position 0)))
           :in-theory '(rwd-dc-term rgi-nfix-when-posp))))

(defthm rfb-entry-of-base-term-one
  (implies (and (posp p)
                (natp row) (< row p)
                (natp column) (< column p))
           (equal (tc-matrix-entry row column
                                   (wbc-term-matrix (rwd-base-term p) 1))
                  (rgi-base-entry row column)))
  :hints (("Goal" :cases ((equal row 0) (equal column 0))
           :use ((:instance rgi-entry-of-wbc-term-matrix-general
                            (left (rwd-unit-row p 0))
                            (right (rwd-unit-row p 0))
                            (coefficient 1))
                 (:instance rfb-nth0-of-unit-row-zero (k row))
                 (:instance rfb-nth0-of-unit-row-zero (k column))
                 (:instance rfb-len-of-unit-row (position 0)))
           :in-theory '(rwd-base-term rgi-base-entry rgi-nfix-when-posp nfix natp))))


(defthm rfb-head-term-matrix-rational
  (implies (wbc-plan-validp n (cons term terms) (cons coefficient post))
           (rational-matrixp n n (wbc-term-matrix term coefficient)))
  :hints (("Goal"
           :use ((:instance rgi-plan-validp-head-facts
                            (terms (cons term terms))
                            (post (cons coefficient post)))
                 (:instance rational-matrixp-of-wbc-term-matrix
                            (term term) (coefficient coefficient)))
           :in-theory '(car-cons cdr-cons))))

(defthm rfb-valid-plan-entry-step
  (implies (and (wbc-plan-validp n (cons term terms)
                                 (cons coefficient post))
                (wbc-plan-validp n terms post)
                (posp n)
                (natp row) (< row n)
                (natp column) (< column n))
           (equal
            (tc-matrix-entry
             row column
             (wbc-plan-matrix (cons term terms)
                              (cons coefficient post)))
            (+ (tc-matrix-entry row column
                                (wbc-term-matrix term coefficient))
               (tc-matrix-entry row column
                                (wbc-plan-matrix terms post)))))
  :hints (("Goal"
           :use ((:instance rfb-head-term-matrix-rational)
                 (:instance rational-matrixp-of-plan-matrix)
                 (:instance rgi-plan-matrix-entry-step-nonempty
                            (p n)))
           :in-theory nil)))


(defthm rfb-cdr-of-full-terms
  (equal (cdr (rwd-full-terms p inputs kernels terms))
         (cons (rwd-base-term p)
               (rwd-lift-terms p inputs kernels terms)))
  :hints (("Goal"
           :use ((:instance rgi-full-terms-open))
           :in-theory '(cdr-cons rwd-base-term))))

(defthm rfb-consp-of-cdr-full-terms
  (consp (cdr (rwd-full-terms p inputs kernels terms)))
  :hints (("Goal" :use ((:instance rfb-cdr-of-full-terms))
           :in-theory nil)))

(defthm rfb-cdr-of-nonzero-post
  (equal (cdr (rwd-nonzero-post post)) (cons 1 post))
  :hints (("Goal"
           :use ((:instance rgi-rwd-nonzero-post-open))
           :in-theory '(cdr-cons))))

(defthm rfb-nonzero-tail-validp
  (implies (and (tc-compact-post-certifiesp n out post)
                (posp p))
           (wbc-plan-validp
            p
            (cons (rwd-base-term p)
                  (rwd-lift-terms p inputs kernels (tc-plan-terms n)))
            (cons 1 post)))
  :hints (("Goal"
           :use ((:instance rgi-nonzero-full-plan-validp)
                 (:instance wbc-plan-validp-of-tail
                            (n p)
                            (terms (rwd-full-terms
                                    p inputs kernels (tc-plan-terms n)))
                            (post (rwd-nonzero-post post)))
                 (:instance rgi-full-terms-open
                            (terms (tc-plan-terms n)))
                 (:instance rgi-rwd-nonzero-post-open)
                 (:instance rfb-cdr-of-full-terms
                            (terms (tc-plan-terms n)))
                 (:instance rfb-consp-of-cdr-full-terms
                            (terms (tc-plan-terms n)))
                 (:instance rfb-cdr-of-nonzero-post))
           :in-theory nil)))

(defthm rfb-nonzero-tail-entry
  (implies (and (tc-compact-post-certifiesp n out post)
                (natp out)
                (posp p)
                (equal (len inputs) (nfix n))
                (equal (len kernels) (nfix n))
                (natp row) (< row p)
                (natp column) (< column p))
           (equal
            (tc-matrix-entry
             row column
             (wbc-plan-matrix
              (cons (rwd-base-term p)
                    (rwd-lift-terms p inputs kernels (tc-plan-terms n)))
              (cons 1 post)))
            (+ (rgi-base-entry row column)
               (rgi-lifted-entry n out row column inputs kernels))))
  :hints (("Goal"
           :use ((:instance tc-compact-post-plan-validp)
                 (:instance wbc-plan-validp-of-rwd-lift
                            (terms (tc-plan-terms n)))
                 (:instance rfb-nonzero-tail-validp)
                 (:instance rfb-valid-plan-entry-step
                            (n p)
                            (term (rwd-base-term p))
                            (coefficient 1)
                            (terms (rwd-lift-terms
                                    p inputs kernels (tc-plan-terms n)))
                            (post post))
                 (:instance rfb-entry-of-base-term-one)
                 (:instance rgi-entry-of-compact-lifted-plan))
           :in-theory nil)))


(defthm rfb-full-terms-exact-open
  (equal
   (rwd-full-terms p inputs kernels terms)
   (cons (rwd-dc-term p)
         (cons (rwd-base-term p)
               (rwd-lift-terms p inputs kernels terms))))
  :hints (("Goal"
           :use ((:instance rgi-full-terms-open))
           :in-theory '(rwd-dc-term rwd-base-term))))

(defthm rfb-nonzero-post-exact-open
  (equal (rwd-nonzero-post post)
         (cons 0 (cons 1 post)))
  :hints (("Goal"
           :use ((:instance rgi-rwd-nonzero-post-open))
           :in-theory nil)))

(defthm rfb-expanded-full-validp
  (implies (and (tc-compact-post-certifiesp n out post)
                (posp p))
           (wbc-plan-validp
            p
            (cons (rwd-dc-term p)
                  (cons (rwd-base-term p)
                        (rwd-lift-terms p inputs kernels
                                        (tc-plan-terms n))))
            (cons 0 (cons 1 post))))
  :hints (("Goal"
           :use ((:instance rgi-nonzero-full-plan-validp)
                 (:instance rfb-full-terms-exact-open
                            (terms (tc-plan-terms n)))
                 (:instance rfb-nonzero-post-exact-open))
           :in-theory nil)))

(defthm rfb-expanded-full-nonzero-entry
  (implies (and (tc-compact-post-certifiesp n out post)
                (natp out)
                (posp p)
                (equal (len inputs) (nfix n))
                (equal (len kernels) (nfix n))
                (natp row) (< row p)
                (natp column) (< column p))
           (equal
            (tc-matrix-entry
             row column
             (wbc-plan-matrix
              (cons (rwd-dc-term p)
                    (cons (rwd-base-term p)
                          (rwd-lift-terms p inputs kernels
                                          (tc-plan-terms n))))
              (cons 0 (cons 1 post))))
            (+ (rgi-base-entry row column)
               (rgi-lifted-entry n out row column inputs kernels))))
  :hints (("Goal"
           :use ((:instance rfb-expanded-full-validp)
                 (:instance rfb-nonzero-tail-validp)
                 (:instance rfb-valid-plan-entry-step
                            (n p)
                            (term (rwd-dc-term p))
                            (coefficient 0)
                            (terms
                             (cons (rwd-base-term p)
                                   (rwd-lift-terms
                                    p inputs kernels (tc-plan-terms n))))
                            (post (cons 1 post)))
                 (:instance rfb-entry-of-dc-term-zero)
                 (:instance rfb-nonzero-tail-entry))
           :in-theory nil)))

(defthm rfb-full-nonzero-entry
  (implies (and (tc-compact-post-certifiesp n out post)
                (natp out)
                (posp p)
                (equal (len inputs) (nfix n))
                (equal (len kernels) (nfix n))
                (natp row) (< row p)
                (natp column) (< column p))
           (equal
            (tc-matrix-entry
             row column
             (wbc-plan-matrix
              (rwd-full-terms p inputs kernels (tc-plan-terms n))
              (rwd-nonzero-post post)))
            (+ (rgi-base-entry row column)
               (rgi-lifted-entry n out row column inputs kernels))))
  :hints (("Goal"
           :use ((:instance rfb-full-terms-exact-open
                            (terms (tc-plan-terms n)))
                 (:instance rfb-nonzero-post-exact-open)
                 (:instance rfb-expanded-full-nonzero-entry))
           :in-theory nil)))
