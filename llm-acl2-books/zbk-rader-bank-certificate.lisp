; Compact bank certificates for generated Rader/Toom-Cook DFT plans.
(in-package "ACL2")
(include-book "zbj-rader-output-matrix-certificate")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The zero-frequency plan.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rbk-nfix-of-len
  (equal (nfix (len xs)) (len xs))
  :hints (("Goal" :in-theory (enable nfix))))

(defthm rbk-len-of-zero-row
  (equal (len (rwd-zero-row count)) (nfix count))
  :hints (("Goal" :in-theory (enable rwd-zero-row
                                      rwd-constant-row-aux))))

(defthm rbk-rational-listp-of-zero-row
  (rational-listp (rwd-zero-row count))
  :hints (("Goal"
           :induct (rwd-constant-row-aux count 0)
           :in-theory (e/d (rwd-zero-row
                             rwd-constant-row-aux
                             rational-listp)
                            (rfb-constant-row-is-repeat)))))

(defthm rbk-dc-post-open
  (equal (rwd-dc-post rank)
         (cons 1 (cons 0 (rwd-zero-row rank))))
  :hints (("Goal" :in-theory '(rwd-dc-post))))

(defthm rbk-cdr-of-dc-post
  (equal (cdr (rwd-dc-post rank))
         (cons 0 (rwd-zero-row rank)))
  :hints (("Goal"
           :use ((:instance rbk-dc-post-open))
           :in-theory '(cdr-cons))))

(defthm rbk-rational-listp-of-dc-post
  (rational-listp (rwd-dc-post rank))
  :hints (("Goal"
           :use ((:instance rbk-dc-post-open)
                 (:instance rbk-rational-listp-of-zero-row
                            (count rank)))
           :in-theory '(rational-listp car-cons cdr-cons))))

(defthm rbk-len-of-dc-post
  (equal (len (rwd-dc-post rank)) (+ 2 (nfix rank)))
  :hints (("Goal"
           :use ((:instance rbk-dc-post-open)
                 (:instance rbk-len-of-zero-row (count rank)))
           :in-theory '(len car-cons cdr-cons))))

(defthm rbk-dc-full-plan-validp
  (implies (and (posp p)
                (wbc-terms-validp n terms))
           (wbc-plan-validp
            p
            (rwd-full-terms p inputs kernels terms)
            (rwd-dc-post (len terms))))
  :hints (("Goal"
           :use ((:instance rgi-full-terms-validp)
                 (:instance rbk-rational-listp-of-dc-post
                            (rank (len terms)))
                 (:instance len-of-rwd-full-terms)
                 (:instance rbk-len-of-dc-post
                            (rank (len terms)))
                 (:instance rbk-nfix-of-len (xs terms))
                 (:instance consp-of-rwd-full-terms)
                 (:instance rgi-wbc-plan-validp-from-components
                            (n p)
                            (terms (rwd-full-terms
                                    p inputs kernels terms))
                            (post (rwd-dc-post (len terms)))))
           :in-theory nil)))

(defun rbk-zero-postp (post)
  (if (endp post)
      t
    (and (equal (car post) 0)
         (rbk-zero-postp (cdr post)))))

(defthm rbk-zero-postp-of-zero-row
  (rbk-zero-postp (rwd-zero-row count))
  :hints (("Goal"
           :induct (rwd-constant-row-aux count 0)
           :in-theory (e/d (rbk-zero-postp
                             rwd-zero-row
                             rwd-constant-row-aux)
                            (rfb-constant-row-is-repeat)))))

(defthm rbk-zero-postp-car
  (implies (and (rbk-zero-postp post) (consp post))
           (equal (car post) 0))
  :hints (("Goal" :in-theory (enable rbk-zero-postp))))

(defthm rbk-zero-postp-cdr
  (implies (rbk-zero-postp post)
           (rbk-zero-postp (cdr post)))
  :hints (("Goal" :in-theory (enable rbk-zero-postp))))

(defthm rbk-term-entry-at-zero
  (implies (and (consp term)
                (natp row) (< row (len (car term)))
                (natp column) (< column (len (cdr term))))
           (equal (tc-matrix-entry
                   row column (wbc-term-matrix term 0))
                  0))
  :hints (("Goal"
           :use ((:instance rgi-entry-of-wbc-term-matrix-general
                            (left (car term))
                            (right (cdr term))
                            (coefficient 0)))
           :in-theory '(cons-car-cdr binary-*))))

(defthm rbk-zero-small-plan-validp
  (implies (and (posp n)
                (consp terms)
                (wbc-terms-validp n terms))
           (wbc-plan-validp n terms (rwd-zero-row (len terms))))
  :hints (("Goal"
           :use ((:instance rbk-rational-listp-of-zero-row
                            (count (len terms)))
                 (:instance rbk-len-of-zero-row
                            (count (len terms)))
                 (:instance rbk-nfix-of-len (xs terms))
                 (:instance rgi-wbc-plan-validp-from-components
                            (post (rwd-zero-row (len terms)))))
           :in-theory nil)))

(defthm rbk-rgi-plan-entry-of-zero-post
  (implies (rbk-zero-postp post)
           (equal (rgi-plan-entry row column inputs kernels terms post)
                  0))
  :hints (("Goal"
           :induct (rgi-plan-entry row column inputs kernels terms post)
           :in-theory '(rgi-plan-entry rbk-zero-postp
                         binary-* binary-+ car-cons cdr-cons))))

(defthm rbk-lifted-zero-plan-entry
  (implies (and (posp n)
                (consp terms)
                (wbc-terms-validp n terms)
                (posp p)
                (natp row) (< row p)
                (natp column) (< column p))
           (equal
            (tc-matrix-entry
             row column
             (wbc-plan-matrix
              (rwd-lift-terms p inputs kernels terms)
              (rwd-zero-row (len terms))))
            0))
  :hints (("Goal"
           :use ((:instance rbk-zero-small-plan-validp)
                 (:instance rgi-entry-of-lifted-plan
                            (post (rwd-zero-row (len terms))))
                 (:instance rbk-zero-postp-of-zero-row
                            (count (len terms)))
                 (:instance rbk-rgi-plan-entry-of-zero-post
                            (post (rwd-zero-row (len terms)))))
           :in-theory nil)))

(defthm rbk-entry-of-base-term-zero
  (implies (and (posp p)
                (natp row) (< row p)
                (natp column) (< column p))
           (equal (tc-matrix-entry
                   row column (wbc-term-matrix (rwd-base-term p) 0))
                  0))
  :hints (("Goal"
           :use ((:instance rbk-term-entry-at-zero
                            (term (rwd-base-term p)))
                 (:instance rfb-len-of-unit-row (position 0))
                 (:instance rgi-nfix-when-posp (n p)))
           :in-theory '(rwd-base-term car-cons cdr-cons))))

(defthm rbk-dc-tail-validp
  (implies (and (posp p)
                (wbc-terms-validp n terms))
           (wbc-plan-validp
            p
            (cons (rwd-base-term p)
                  (rwd-lift-terms p inputs kernels terms))
            (cons 0 (rwd-zero-row (len terms)))))
  :hints (("Goal"
           :use ((:instance rbk-dc-full-plan-validp)
                 (:instance wbc-plan-validp-of-tail
                            (n p)
                            (terms (rwd-full-terms
                                    p inputs kernels terms))
                            (post (rwd-dc-post (len terms))))
                 (:instance rfb-cdr-of-full-terms)
                 (:instance rbk-cdr-of-dc-post
                            (rank (len terms))))
           :in-theory nil)))


(defthm rbk-dc-tail-entry
  (implies (and (posp p)
                (posp n)
                (consp terms)
                (wbc-terms-validp n terms)
                (natp row) (< row p)
                (natp column) (< column p))
           (equal
            (tc-matrix-entry
             row column
             (wbc-plan-matrix
              (cons (rwd-base-term p)
                    (rwd-lift-terms p inputs kernels terms))
              (cons 0 (rwd-zero-row (len terms)))))
            0))
  :hints (("Goal"
           :use ((:instance rbk-dc-tail-validp)
                 (:instance rbk-zero-small-plan-validp)
                 (:instance wbc-plan-validp-of-rwd-lift
                            (post (rwd-zero-row (len terms))))
                 (:instance rfb-valid-plan-entry-step
                            (n p)
                            (term (rwd-base-term p))
                            (coefficient 0)
                            (terms (rwd-lift-terms p inputs kernels terms))
                            (post (rwd-zero-row (len terms))))
                 (:instance rbk-entry-of-base-term-zero)
                 (:instance rbk-lifted-zero-plan-entry))
           :in-theory nil)))

(defthm rbk-dc-plan-entry
  (implies (and (posp p)
                (posp n)
                (consp terms)
                (wbc-terms-validp n terms)
                (natp row) (< row p)
                (natp column) (< column p))
           (equal
            (tc-matrix-entry
             row column
             (wbc-plan-matrix
              (rwd-full-terms p inputs kernels terms)
              (rwd-dc-post (len terms))))
            (if (equal column 0) 1 0)))
  :hints (("Goal"
           :use ((:instance rbk-dc-full-plan-validp)
                 (:instance rbk-dc-tail-validp)
                 (:instance rfb-valid-plan-entry-step
                            (n p)
                            (term (rwd-dc-term p))
                            (coefficient 1)
                            (terms (cons (rwd-base-term p)
                                         (rwd-lift-terms
                                          p inputs kernels terms)))
                            (post (cons 0 (rwd-zero-row (len terms)))))
                 (:instance rfb-entry-of-dc-term-one)
                 (:instance rbk-dc-tail-entry)
                 (:instance rfb-full-terms-exact-open)
                 (:instance rbk-dc-post-open
                            (rank (len terms))))
           :in-theory '(rbk-zero-postp rbk-zero-postp-of-zero-row))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Extensional zero-frequency certificate.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rbk-times-zero
  (equal (* x 0) 0))

(defthm rbk-fourier-zero-entry
  (implies (and (posp p)
                (natp row) (< row p)
                (natp column) (< column p))
           (equal (tc-matrix-entry
                   row column (rwd-fourier-matrix p 0))
                  (if (equal column 0) 1 0)))
  :hints (("Goal"
           :use ((:instance rom-entry-of-fourier-matrix
                            (output 0))
                 (:instance rom-nfix-when-natp (x row))
                 (:instance rom-nfix-when-natp (x column))
                 (:instance rom-nfix-when-natp (x 0))
                 (:instance rom-natp-zero)
                 (:instance rgi-nfix-when-posp (n p)))
           :in-theory '(rgi-fourier-entry rbk-times-zero nfix |(mod 0 y)|))))

(defthm rbk-rational-matrixp-of-dc-plan
  (implies (and (posp p)
                (wbc-terms-validp n terms))
           (rational-matrixp
            p p
            (wbc-plan-matrix
             (rwd-full-terms p inputs kernels terms)
             (rwd-dc-post (len terms)))))
  :hints (("Goal"
           :use ((:instance rbk-dc-full-plan-validp)
                 (:instance rational-matrixp-of-plan-matrix
                            (n p)
                            (terms (rwd-full-terms
                                    p inputs kernels terms))
                            (post (rwd-dc-post (len terms)))))
           :in-theory nil)))

(defthm rbk-dc-plan-row-length
  (implies (and (posp p)
                (wbc-terms-validp n terms)
                (natp row) (< row p))
           (equal
            (len
             (tc-nth0
              row
              (wbc-plan-matrix
               (rwd-full-terms p inputs kernels terms)
               (rwd-dc-post (len terms)))))
            p))
  :hints (("Goal"
           :use ((:instance rbk-rational-matrixp-of-dc-plan)
                 (:instance len-of-tc-nth0-of-rational-matrixp
                            (rows p) (cols p)
                            (matrix
                             (wbc-plan-matrix
                              (rwd-full-terms p inputs kernels terms)
                              (rwd-dc-post (len terms))))))
           :in-theory '(rgi-nfix-when-posp))))

(defthm rbk-dc-plan-row-true-listp
  (implies (and (posp p)
                (wbc-terms-validp n terms)
                (natp row) (< row p))
           (true-listp
            (tc-nth0
             row
             (wbc-plan-matrix
              (rwd-full-terms p inputs kernels terms)
              (rwd-dc-post (len terms))))))
  :hints (("Goal"
           :use ((:instance rom-proper-matrixp-of-wbc-plan-matrix
                            (terms (rwd-full-terms
                                    p inputs kernels terms))
                            (post (rwd-dc-post (len terms))))
                 (:instance rom-true-listp-of-proper-matrix-row
                            (matrix
                             (wbc-plan-matrix
                              (rwd-full-terms p inputs kernels terms)
                              (rwd-dc-post (len terms)))))
                 (:instance tc-len-of-rational-matrixp
                            (rows p) (cols p)
                            (matrix
                             (wbc-plan-matrix
                              (rwd-full-terms p inputs kernels terms)
                              (rwd-dc-post (len terms)))))
                 (:instance rbk-rational-matrixp-of-dc-plan))
           :in-theory '(rgi-nfix-when-posp))))

(defthm rbk-nth-of-dc-plan-row-equals-fourier-zero
  (implies (and (posp p)
                (posp n)
                (consp terms)
                (wbc-terms-validp n terms)
                (natp row) (< row p)
                (natp column) (< column p))
           (equal
            (nth
             column
             (tc-nth0
              row
              (wbc-plan-matrix
               (rwd-full-terms p inputs kernels terms)
               (rwd-dc-post (len terms)))))
            (nth column
                 (tc-nth0 row (rwd-fourier-matrix p 0)))))
  :hints
  (("Goal"
    :use
    ((:instance tc-equality-chain-5
                (a (nth
                    column
                    (tc-nth0
                     row
                     (wbc-plan-matrix
                      (rwd-full-terms p inputs kernels terms)
                      (rwd-dc-post (len terms))))))
                (b (tc-matrix-entry
                    row column
                    (wbc-plan-matrix
                     (rwd-full-terms p inputs kernels terms)
                     (rwd-dc-post (len terms)))))
                (c (if (equal column 0) 1 0))
                (d (tc-matrix-entry
                    row column (rwd-fourier-matrix p 0)))
                (e (nth column
                        (tc-nth0 row
                                 (rwd-fourier-matrix p 0)))))
     (:instance rbk-dc-plan-entry)
     (:instance rbk-fourier-zero-entry)
     (:instance tc-nth0-is-nth-when-in-bounds
                (k column)
                (xs
                 (tc-nth0
                  row
                  (wbc-plan-matrix
                   (rwd-full-terms p inputs kernels terms)
                   (rwd-dc-post (len terms))))))
     (:instance tc-nth0-is-nth-when-in-bounds
                (k column)
                (xs (tc-nth0 row
                             (rwd-fourier-matrix p 0))))
     (:instance rbk-dc-plan-row-length)
     (:instance rom-fourier-row-length (output 0)))
    :in-theory '(tc-matrix-entry))))

(defthm rbk-dc-plan-row-equals-fourier-zero-row
  (implies (and (posp p)
                (posp n)
                (consp terms)
                (wbc-terms-validp n terms)
                (natp row) (< row p))
           (equal
            (tc-nth0
             row
             (wbc-plan-matrix
              (rwd-full-terms p inputs kernels terms)
              (rwd-dc-post (len terms))))
            (tc-nth0 row (rwd-fourier-matrix p 0))))
  :hints
  (("Goal"
    :use
    ((:functional-instance
      equal-by-nths
      (equal-by-nths-lhs
       (lambda ()
         (tc-nth0
          row
          (wbc-plan-matrix
           (rwd-full-terms p inputs kernels terms)
           (rwd-dc-post (len terms))))))
      (equal-by-nths-rhs
       (lambda ()
         (tc-nth0 row (rwd-fourier-matrix p 0))))
      (equal-by-nths-hyp
       (lambda ()
         (and (posp p)
              (posp n)
              (consp terms)
              (wbc-terms-validp n terms)
              (natp row) (< row p))))))
    :in-theory
    '((:rewrite rbk-dc-plan-row-true-listp)
      (:rewrite rom-fourier-row-true-listp)
      (:rewrite rbk-dc-plan-row-length)
      (:rewrite rom-fourier-row-length)
      (:rewrite rbk-nth-of-dc-plan-row-equals-fourier-zero)))))

(defthm rbk-dc-plan-matrix-length
  (implies (and (posp p)
                (wbc-terms-validp n terms))
           (equal
            (len
             (wbc-plan-matrix
              (rwd-full-terms p inputs kernels terms)
              (rwd-dc-post (len terms))))
            p))
  :hints (("Goal"
           :use ((:instance rbk-rational-matrixp-of-dc-plan)
                 (:instance tc-len-of-rational-matrixp
                            (rows p) (cols p)
                            (matrix
                             (wbc-plan-matrix
                              (rwd-full-terms p inputs kernels terms)
                              (rwd-dc-post (len terms))))))
           :in-theory '(rgi-nfix-when-posp))))

(defthm rbk-nth-of-dc-plan-matrix-equals-fourier-zero
  (implies (and (posp p)
                (posp n)
                (consp terms)
                (wbc-terms-validp n terms)
                (natp row) (< row p))
           (equal
            (nth
             row
             (wbc-plan-matrix
              (rwd-full-terms p inputs kernels terms)
              (rwd-dc-post (len terms))))
            (nth row (rwd-fourier-matrix p 0))))
  :hints
  (("Goal"
    :use
    ((:instance tc-equality-chain-3
                (a (nth
                    row
                    (wbc-plan-matrix
                     (rwd-full-terms p inputs kernels terms)
                     (rwd-dc-post (len terms)))))
                (b (tc-nth0
                    row
                    (wbc-plan-matrix
                     (rwd-full-terms p inputs kernels terms)
                     (rwd-dc-post (len terms)))))
                (c (tc-nth0 row
                            (rwd-fourier-matrix p 0)))
                (d (nth row
                        (rwd-fourier-matrix p 0))))
     (:instance tc-nth0-is-nth-when-in-bounds
                (k row)
                (xs
                 (wbc-plan-matrix
                  (rwd-full-terms p inputs kernels terms)
                  (rwd-dc-post (len terms)))))
     (:instance tc-nth0-is-nth-when-in-bounds
                (k row)
                (xs (rwd-fourier-matrix p 0)))
     (:instance rbk-dc-plan-matrix-length)
     (:instance rom-fourier-matrix-length (output 0))
     (:instance rbk-dc-plan-row-equals-fourier-zero-row))
    :in-theory nil)))

(defthm rbk-dc-plan-matrix-equals-fourier-zero
  (implies (and (posp p)
                (posp n)
                (consp terms)
                (wbc-terms-validp n terms))
           (equal
            (wbc-plan-matrix
             (rwd-full-terms p inputs kernels terms)
             (rwd-dc-post (len terms)))
            (rwd-fourier-matrix p 0)))
  :hints
  (("Goal"
    :use
    ((:functional-instance
      equal-by-nths
      (equal-by-nths-lhs
       (lambda ()
         (wbc-plan-matrix
          (rwd-full-terms p inputs kernels terms)
          (rwd-dc-post (len terms)))))
      (equal-by-nths-rhs
       (lambda () (rwd-fourier-matrix p 0)))
      (equal-by-nths-hyp
       (lambda ()
         (and (posp p)
              (posp n)
              (consp terms)
              (wbc-terms-validp n terms))))))
    :in-theory
    '((:rewrite tc-true-listp-of-wbc-plan-matrix)
      (:rewrite rom-true-listp-of-fourier-matrix)
      (:rewrite rbk-dc-plan-matrix-length)
      (:rewrite rom-fourier-matrix-length)
      (:rewrite rbk-nth-of-dc-plan-matrix-equals-fourier-zero)))))

(defthm rbk-dc-plan-certificate
  (implies (and (posp p)
                (posp n)
                (consp terms)
                (wbc-terms-validp n terms))
           (rwd-plan-certifies-outputp
            p 0
            (rwd-full-terms p inputs kernels terms)
            (rwd-dc-post (len terms))))
  :hints (("Goal"
           :use ((:instance rbk-dc-full-plan-validp)
                 (:instance rbk-dc-plan-matrix-equals-fourier-zero))
           :in-theory '(rwd-plan-certifies-outputp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A joint compact certificate for the nonzero-output bank.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rbk-compact-bankp
  (small-out p outputs inputs kernels posts)
  (declare (xargs :measure (acl2-count outputs)
                  :verify-guards nil
                  :hints (("Goal"
                           :in-theory
                           (disable rgi-compact-outputp
                                    tc-compact-post-certifiesp)))))
  (if (endp outputs)
      (endp posts)
    (and
     (consp posts)
     (tc-compact-post-certifiesp
      (1- (nfix p)) (nfix small-out) (car posts))
     (rgi-compact-outputp
      p (nfix small-out) (car outputs) inputs kernels)
     (rbk-compact-bankp
      (1+ (nfix small-out)) p
      (cdr outputs) inputs kernels (cdr posts)))))


(defun rbk-nat-listp (xs)
  (if (endp xs)
      t
    (and (natp (car xs))
         (rbk-nat-listp (cdr xs)))))

(defthm rbk-nat-listp-head
  (implies (and (rbk-nat-listp xs) (consp xs))
           (natp (car xs)))
  :hints (("Goal" :in-theory (enable rbk-nat-listp))))

(defthm rbk-nat-listp-tail
  (implies (rbk-nat-listp xs)
           (rbk-nat-listp (cdr xs)))
  :rule-classes nil
  :hints (("Goal"
           :cases ((consp xs))
           :in-theory '(rbk-nat-listp))))

(defthm rbk-natp-of-nfix
  (natp (nfix x))
  :hints (("Goal" :in-theory (enable nfix natp))))

(defthm rbk-natp-next-index
  (natp (1+ (nfix small-out)))
  :hints (("Goal" :in-theory (enable nfix natp))))

(defthm rbk-rwd-bank-empty-posts
  (implies (endp outputs)
           (rwd-bank-certifies-aux p outputs terms nil))
  :hints
  (("Goal"
    :expand ((rwd-bank-certifies-aux p outputs terms nil))
    :in-theory nil)))

(defthm rbk-rwd-bank-nonzero-posts-open
  (implies
   (and (not (endp outputs))
        (consp posts))
   (equal
    (rwd-bank-certifies-aux
     p outputs terms (rwd-nonzero-posts posts))
    (and
     (rwd-plan-certifies-outputp
      p (car outputs) terms (rwd-nonzero-post (car posts)))
     (rwd-bank-certifies-aux
      p (cdr outputs) terms (rwd-nonzero-posts (cdr posts))))))
  :hints
  (("Goal"
    :expand
    ((rwd-nonzero-posts posts)
     (rwd-bank-certifies-aux
      p outputs terms
      (cons (rwd-nonzero-post (car posts))
            (rwd-nonzero-posts (cdr posts)))))
    :in-theory '(car-cons cdr-cons))))

(defun rbk-compact-bank-induct (small-out outputs posts)
  (if (endp outputs)
      (list small-out outputs posts)
    (rbk-compact-bank-induct
     (1+ (nfix small-out)) (cdr outputs) (cdr posts))))

(defthm rbk-compact-bank-implies-nonzero-certificate
  (implies
   (and (rbk-compact-bankp
         small-out p outputs inputs kernels posts)
        (rbk-nat-listp outputs)
        (natp small-out)
        (posp p))
   (rwd-bank-certifies-aux
    p outputs
    (rwd-full-terms
     p inputs kernels (tc-plan-terms (1- (nfix p))))
    (rwd-nonzero-posts posts)))
  :hints
  (("Goal"
    :induct (rbk-compact-bank-induct small-out outputs posts))
   ("Subgoal *1/2"
    :use ((:instance rbk-nat-listp-head (xs outputs))
          (:instance rbk-nat-listp-tail (xs outputs))
          (:instance rbk-natp-of-nfix (x small-out))
          (:instance rbk-natp-next-index)
          (:instance rbk-rwd-bank-nonzero-posts-open
                     (terms (rwd-full-terms
                             p inputs kernels
                             (tc-plan-terms (1- (nfix p))))))
          (:instance rom-compact-output-implies-plan-certificate
                     (small-out (nfix small-out))
                     (post (car posts))
                     (output (car outputs))))
    :expand
    ((rbk-compact-bankp
      small-out p outputs inputs kernels posts)
     (rwd-nonzero-posts posts)
     (rwd-bank-certifies-aux
      p outputs
      (rwd-full-terms
       p inputs kernels (tc-plan-terms (1- (nfix p))))
      (rwd-nonzero-posts posts)))
    :in-theory '(rbk-compact-bankp rbk-compact-bank-induct))
   ("Subgoal *1/1"
    :use ((:instance rbk-rwd-bank-empty-posts
                     (terms (rwd-full-terms
                             p inputs kernels
                             (tc-plan-terms (1- (nfix p)))))))
    :expand
    ((rbk-compact-bankp
      small-out p outputs inputs kernels posts)
     (rwd-nonzero-posts posts)
     (rwd-bank-certifies-aux
      p outputs
      (rwd-full-terms
       p inputs kernels (tc-plan-terms (1- (nfix p))))
      (rwd-nonzero-posts posts)))
    :in-theory '(rbk-compact-bankp rbk-compact-bank-induct))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The complete generated Rader bank.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rbk-generated-terms-validp
  (wbc-terms-validp n (tc-plan-terms n))
  :hints
  (("Goal"
    :use ((:instance wbc-terms-validp-of-tc-plan-terms-aux
                     (count (if (posp n) (1- (* 2 n)) 0))
                     (point 0)))
    :in-theory '(tc-plan-terms))))

(defthm rbk-generated-terms-consp
  (implies (posp n)
           (consp (tc-plan-terms n)))
  :hints
  (("Goal"
    :use ((:instance consp-of-tc-plan-terms-aux
                     (count (1- (* 2 n)))
                     (point 0)))
    :in-theory '(tc-plan-terms posp zp nfix))))

(defthm rbk-full-bank-open
  (equal
   (rwd-bank-certifiesp
    p
    (rwd-output-order outputs)
    terms
    (rwd-full-posts rank posts))
   (and
    (rwd-plan-certifies-outputp p 0 terms (rwd-dc-post rank))
    (rwd-bank-certifies-aux
     p outputs terms (rwd-nonzero-posts posts))))
  :hints
  (("Goal"
    :in-theory '(rwd-bank-certifiesp
                  rwd-output-order rwd-full-posts
                  rwd-bank-certifies-aux
                  car-cons cdr-cons))))

(defthm rbk-compact-bank-implies-full-certificate
  (implies
   (and
    (posp p)
    (posp (1- (nfix p)))
    (rbk-compact-bankp 0 p outputs inputs kernels posts)
    (rbk-nat-listp outputs))
   (rwd-bank-certifiesp
    p
    (rwd-output-order outputs)
    (rwd-full-terms
     p inputs kernels (tc-plan-terms (1- (nfix p))))
    (rwd-full-posts
     (len (tc-plan-terms (1- (nfix p)))) posts)))
  :hints
  (("Goal"
    :use
    ((:instance rom-natp-zero)
     (:instance rbk-generated-terms-validp
                (n (1- (nfix p))))
     (:instance rbk-generated-terms-consp
                (n (1- (nfix p))))
     (:instance rbk-dc-plan-certificate
                (n (1- (nfix p)))
                (terms (tc-plan-terms (1- (nfix p)))))
     (:instance rbk-compact-bank-implies-nonzero-certificate
                (small-out 0))
     (:instance rbk-full-bank-open
                (terms
                 (rwd-full-terms
                  p inputs kernels
                  (tc-plan-terms (1- (nfix p)))))
                (rank (len (tc-plan-terms (1- (nfix p)))))))
    :in-theory nil)))
