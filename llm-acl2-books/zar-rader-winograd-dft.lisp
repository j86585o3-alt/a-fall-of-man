; Proof-carrying Rader/Winograd DFT compilers over rational-complex tables.
(in-package "ACL2")
(include-book "zaq-winograd-bilinear-bank")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Canonical bilinear coefficient matrices for one rational DFT output.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rwd-fourier-row-aux (count j input-index output-index p)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (if (equal (nfix j)
                     (mod (* (nfix input-index)
                             (nfix output-index))
                          (nfix p)))
              1 0)
          (rwd-fourier-row-aux (1- count) (1+ (nfix j))
                               input-index output-index p))))

(defun rwd-fourier-matrix-aux (count input-index output-index p)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (rwd-fourier-row-aux p 0 input-index output-index p)
          (rwd-fourier-matrix-aux (1- count) (1+ (nfix input-index))
                                  output-index p))))

(defun rwd-fourier-matrix (p output-index)
  (rwd-fourier-matrix-aux p 0 output-index p))

(defun rwd-direct-output (p output-index xs table)
  (wbc-matrix-eval (rwd-fourier-matrix p output-index) xs table))

(defun rwd-direct-outputs (outputs p xs table)
  (if (endp outputs)
      nil
    (cons (rwd-direct-output p (car outputs) xs table)
          (rwd-direct-outputs (cdr outputs) p xs table))))

(defthm rational-rowp-of-rwd-fourier-row-aux
  (rational-rowp count
                 (rwd-fourier-row-aux count j input-index output-index p))
  :hints (("Goal"
           :induct (rwd-fourier-row-aux count j input-index output-index p)
           :in-theory (enable rwd-fourier-row-aux rational-rowp))))

(defthm rational-matrixp-of-rwd-fourier-matrix-aux
  (rational-matrixp count p
                    (rwd-fourier-matrix-aux count input-index
                                            output-index p))
  :hints (("Goal"
           :induct (rwd-fourier-matrix-aux count input-index output-index p)
           :in-theory (enable rwd-fourier-matrix-aux rational-matrixp))))

(defthm rational-matrixp-of-rwd-fourier-matrix
  (rational-matrixp p p (rwd-fourier-matrix p output-index))
  :hints (("Goal"
           :use ((:instance rational-matrixp-of-rwd-fourier-matrix-aux
                            (count p) (input-index 0)))
           :in-theory (enable rwd-fourier-matrix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lifting a small Rader convolution plan into p-dimensional DFT coordinates.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rwd-coefficient-at (index indices coefficients)
  (if (or (endp indices) (endp coefficients))
      0
    (if (equal (nfix index) (nfix (car indices)))
        (car coefficients)
      (rwd-coefficient-at index (cdr indices) (cdr coefficients)))))

(defun rwd-lift-row-aux (count index indices coefficients)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (rwd-coefficient-at index indices coefficients)
          (rwd-lift-row-aux (1- count) (1+ (nfix index))
                            indices coefficients))))

(defun rwd-lift-row (p indices coefficients)
  (rwd-lift-row-aux p 0 indices coefficients))

(defun rwd-lift-terms (p input-indices kernel-indices terms)
  (if (endp terms)
      nil
    (cons (cons (rwd-lift-row p input-indices (caar terms))
                (rwd-lift-row p kernel-indices (cdar terms)))
          (rwd-lift-terms p input-indices kernel-indices (cdr terms)))))

(defun rwd-constant-row-aux (count value)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons value (rwd-constant-row-aux (1- count) value))))

(defun rwd-unit-row-aux (count index position)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (if (equal (nfix index) (nfix position)) 1 0)
          (rwd-unit-row-aux (1- count) (1+ (nfix index)) position))))

(defun rwd-unit-row (p position)
  (rwd-unit-row-aux p 0 position))

(defun rwd-dc-term (p)
  (cons (rwd-constant-row-aux p 1)
        (rwd-unit-row p 0)))

(defun rwd-base-term (p)
  (cons (rwd-unit-row p 0)
        (rwd-unit-row p 0)))

(defun rwd-full-terms (p input-indices kernel-indices terms)
  (cons (rwd-dc-term p)
        (cons (rwd-base-term p)
              (rwd-lift-terms p input-indices kernel-indices terms))))

(defun rwd-zero-row (count)
  (rwd-constant-row-aux count 0))

(defun rwd-dc-post (rank)
  (cons 1 (cons 0 (rwd-zero-row rank))))

(defun rwd-nonzero-post (post)
  (cons 0 (cons 1 post)))

(defun rwd-nonzero-posts (posts)
  (if (endp posts)
      nil
    (cons (rwd-nonzero-post (car posts))
          (rwd-nonzero-posts (cdr posts)))))

(defun rwd-full-posts (rank posts)
  (cons (rwd-dc-post rank)
        (rwd-nonzero-posts posts)))

(defun rwd-output-order (output-indices)
  (cons 0 output-indices))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Exact coefficient-matrix certificate and the generic correctness theorem.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rwd-plan-certifies-outputp (p output-index terms post)
  (and (wbc-plan-validp p terms post)
       (equal (wbc-plan-matrix terms post)
              (rwd-fourier-matrix p output-index))))

(defun rwd-bank-certifies-aux (p outputs terms posts)
  (if (or (endp outputs) (endp posts))
      (and (endp outputs) (endp posts))
    (and (rwd-plan-certifies-outputp p (car outputs) terms (car posts))
         (rwd-bank-certifies-aux p (cdr outputs) terms (cdr posts)))))

(defun rwd-bank-certifiesp (p outputs terms posts)
  (rwd-bank-certifies-aux p outputs terms posts))

(defthm rwd-certified-head-correct
  (implies (and (rwd-plan-certifies-outputp p output-index terms post)
                (qcx-vectorp p xs)
                (qcx-vectorp p table))
           (equal (wbc-post-output post
                                   (wbc-product-bank terms xs table))
                  (rwd-direct-output p output-index xs table)))
  :hints (("Goal"
           :use ((:instance wbc-post-output-of-product-bank)
                 (:instance wbc-plan-output-is-matrix-eval
                            (n p) (ys table)))
           :in-theory (enable rwd-plan-certifies-outputp
                              rwd-direct-output))))

(defthm rwd-bank-certifies-aux-correct
  (implies (and (rwd-bank-certifies-aux p outputs terms posts)
                (qcx-vectorp p xs)
                (qcx-vectorp p table))
           (equal (wbc-post-bank-output
                   posts (wbc-product-bank terms xs table))
                  (rwd-direct-outputs outputs p xs table)))
  :hints (("Goal"
           :induct (rwd-bank-certifies-aux p outputs terms posts)
           :in-theory
           (e/d (rwd-bank-certifies-aux
                 wbc-post-bank-output
                 rwd-direct-outputs)
                (rwd-plan-certifies-outputp
                 wbc-post-output wbc-product-bank
                 rwd-direct-output qcx-vectorp)))))

(defthm rwd-certified-bank-correct
  (implies (and (rwd-bank-certifiesp p outputs terms posts)
                (qcx-vectorp p xs)
                (qcx-vectorp p table))
           (equal (wbc-bank-output terms posts xs table)
                  (rwd-direct-outputs outputs p xs table)))
  :hints (("Goal"
           :use ((:instance rwd-bank-certifies-aux-correct))
           :in-theory (enable rwd-bank-certifiesp wbc-bank-output))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The compiler and its proof-carrying acceptance predicate.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rwd-compile-terms (p input-indices kernel-indices small-terms)
  (rwd-full-terms p input-indices kernel-indices small-terms))

(defun rwd-compile-posts (small-terms small-posts)
  (rwd-full-posts (len small-terms) small-posts))

(defun rwd-compile-outputs (output-indices)
  (rwd-output-order output-indices))

(defun rwd-compiled-certifiesp
  (p input-indices kernel-indices output-indices small-terms small-posts)
  (rwd-bank-certifiesp
   p
   (rwd-compile-outputs output-indices)
   (rwd-compile-terms p input-indices kernel-indices small-terms)
   (rwd-compile-posts small-terms small-posts)))

(defun rwd-run
  (p input-indices kernel-indices small-terms small-posts xs table)
  (wbc-bank-output
   (rwd-compile-terms p input-indices kernel-indices small-terms)
   (rwd-compile-posts small-terms small-posts)
   xs table))

(defthm rwd-compiled-certifiesp-is-bank-certifiesp
  (equal
   (rwd-compiled-certifiesp
    p input-indices kernel-indices output-indices
    small-terms small-posts)
   (rwd-bank-certifiesp
    p
    (rwd-compile-outputs output-indices)
    (rwd-compile-terms p input-indices kernel-indices small-terms)
    (rwd-compile-posts small-terms small-posts)))
  :hints (("Goal" :in-theory (enable rwd-compiled-certifiesp))))

(defthm rwd-run-is-bank-output
  (equal
   (rwd-run p input-indices kernel-indices
            small-terms small-posts xs table)
   (wbc-bank-output
    (rwd-compile-terms p input-indices kernel-indices small-terms)
    (rwd-compile-posts small-terms small-posts)
    xs table))
  :hints (("Goal" :in-theory (enable rwd-run))))

(defthm rwd-compiled-transform-correct
  (implies
   (and (rwd-compiled-certifiesp
         p input-indices kernel-indices output-indices
         small-terms small-posts)
        (qcx-vectorp p xs)
        (qcx-vectorp p table))
   (equal (rwd-run p input-indices kernel-indices
                   small-terms small-posts xs table)
          (rwd-direct-outputs (rwd-compile-outputs output-indices)
                              p xs table)))
  :hints (("Goal"
           :use ((:instance rwd-compiled-certifiesp-is-bank-certifiesp)
                 (:instance rwd-run-is-bank-output)
                 (:instance rwd-certified-bank-correct
                            (outputs (rwd-compile-outputs output-indices))
                            (terms (rwd-compile-terms
                                    p input-indices kernel-indices small-terms))
                            (posts (rwd-compile-posts
                                    small-terms small-posts))
                            (table table)))
           :in-theory nil)))

(defun rwd-complex-product-count (small-terms)
  (+ 2 (len small-terms)))
