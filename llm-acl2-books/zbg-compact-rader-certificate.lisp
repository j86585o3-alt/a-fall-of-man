; A scalar certificate bridge from generated cyclic convolution to Rader DFTs.
(in-package "ACL2")
(include-book "zbe-generated-cyclic66")
(include-book "zbf-rader-index-certificate")

(defun rgi-position (index indices)
  (if (endp indices)
      0
    (if (equal (nfix index) (nfix (car indices)))
        0
      (1+ (rgi-position index (cdr indices))))))

(defun rgi-lifted-entry (n out row column inputs kernels)
  (let ((a (rgi-position row inputs))
        (b (rgi-position column kernels)))
    (if (and (< a (nfix n))
             (< b (nfix n))
             (equal (mod (+ a b) (nfix n)) (nfix out)))
        1 0)))

(defun rgi-base-entry (row column)
  (if (and (equal (nfix row) 0)
           (equal (nfix column) 0))
      1 0))

(defun rgi-fourier-entry (p output row column)
  (if (equal (nfix column)
             (mod (* (nfix row) (nfix output)) (nfix p)))
      1 0))

(defun rgi-compact-output-rowp
  (count column p small-out output inputs kernels)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let ((row (1- (nfix count))))
      (and (equal (+ (rgi-base-entry row column)
                     (rgi-lifted-entry (1- (nfix p)) small-out
                                       row column inputs kernels))
                  (rgi-fourier-entry p output row column))
           (rgi-compact-output-rowp
            (1- count) column p small-out output inputs kernels)))))

(defun rgi-compact-outputp-aux
  (count p small-out output inputs kernels)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let ((column (1- (nfix count))))
      (and (rgi-compact-output-rowp
            p column p small-out output inputs kernels)
           (rgi-compact-outputp-aux
            (1- count) p small-out output inputs kernels)))))

(defun rgi-compact-outputp (p small-out output inputs kernels)
  (and (< 2 (nfix p))
       (equal (len inputs) (1- (nfix p)))
       (equal (len kernels) (1- (nfix p)))
       (rgi-compact-outputp-aux p p small-out output inputs kernels)))

(defun rgi-compact-bankp-aux
  (small-out p outputs inputs kernels)
  (declare (xargs :measure (acl2-count outputs)
                  :hints (("Goal" :in-theory (disable rgi-compact-outputp)))))
  (if (endp outputs)
      t
    (and (rgi-compact-outputp p (nfix small-out) (car outputs)
                              inputs kernels)
         (rgi-compact-bankp-aux (1+ (nfix small-out)) p (cdr outputs)
                                inputs kernels))))

(defun rgi-compact-bankp (p outputs inputs kernels)
  (and (equal (len outputs) (1- (nfix p)))
       (rgi-compact-bankp-aux 0 p outputs inputs kernels)))

(defthm rgi-position-bound
  (<= (rgi-position index indices) (len indices))
  :rule-classes :linear)

(defun rgi-coefficient-induct (index indices coefficients)
  (if (or (endp indices) (endp coefficients))
      (list index indices coefficients)
    (rgi-coefficient-induct index (cdr indices) (cdr coefficients))))

(defthm rwd-coefficient-at-is-position
  (implies (and (< (rgi-position index indices) (len indices))
                (equal (len coefficients) (len indices)))
           (equal (rwd-coefficient-at index indices coefficients)
                  (tc-nth0 (rgi-position index indices) coefficients)))
  :hints (("Goal" :induct (rgi-coefficient-induct index indices coefficients)
           :in-theory (enable rgi-coefficient-induct rgi-position
                              rwd-coefficient-at tc-nth0))))

(defthm rwd-coefficient-at-zero-outside-position
  (implies (<= (len indices) (rgi-position index indices))
           (equal (rwd-coefficient-at index indices coefficients) 0))
  :hints (("Goal" :induct (rgi-coefficient-induct index indices coefficients)
           :in-theory (enable rgi-coefficient-induct rgi-position
                              rwd-coefficient-at))))

(defun rgi-lift-nth-induct (count index column)
  (if (or (zp count) (zp column))
      (list count index column)
    (rgi-lift-nth-induct (1- count) (1+ (nfix index))
                         (1- column))))

(defthm car-of-rwd-lift-row-aux
  (implies (not (zp count))
           (equal (car (rwd-lift-row-aux count index indices coefficients))
                  (rwd-coefficient-at index indices coefficients)))
  :hints (("Goal" :expand ((rwd-lift-row-aux count index indices coefficients)))))

(defthm tc-nth0-of-rwd-lift-row-aux
  (implies (and (natp index) (natp column)
                (< column (nfix count)))
           (equal (tc-nth0 column
                           (rwd-lift-row-aux count index
                                             indices coefficients))
                  (rwd-coefficient-at (+ index column)
                                      indices coefficients)))
  :hints (("Goal"
           :induct (rgi-lift-nth-induct count index column)
           :in-theory (enable rgi-lift-nth-induct tc-nth0
                              rwd-lift-row-aux))))

(defthm tc-nth0-of-rwd-lift-row
  (implies (and (natp column) (< column (nfix p)))
           (equal (tc-nth0 column (rwd-lift-row p indices coefficients))
                  (rwd-coefficient-at column indices coefficients)))
  :hints (("Goal"
           :use ((:instance tc-nth0-of-rwd-lift-row-aux
                            (count p) (index 0)))
           :in-theory (enable rwd-lift-row))))

(defun rgi-row-nth-induct (row k)
  (if (zp k) row
    (rgi-row-nth-induct (cdr row) (1- k))))

(defthm tc-nth0-of-wbc-row-scale-general
  (implies (and (natp column) (< column (len row)))
           (equal (tc-nth0 column (wbc-row-scale c row))
                  (* c (tc-nth0 column row))))
  :hints (("Goal" :induct (rgi-row-nth-induct row column)
           :in-theory (enable rgi-row-nth-induct tc-nth0
                              wbc-row-scale))))

(defun rgi-matrix-nth-induct (matrix row)
  (if (zp row) matrix
    (rgi-matrix-nth-induct (cdr matrix) (1- row))))

(defthm tc-nth0-row-of-wbc-matrix-scale-general
  (implies (and (natp row) (< row (len matrix)))
           (equal (tc-nth0 row (wbc-matrix-scale c matrix))
                  (wbc-row-scale c (tc-nth0 row matrix))))
  :hints (("Goal" :induct (rgi-matrix-nth-induct matrix row)
           :in-theory (enable rgi-matrix-nth-induct tc-nth0
                              wbc-matrix-scale))))

(defthm rgi-entry-of-wbc-matrix-scale
  (implies (and (natp row) (< row (len matrix))
                (natp column)
                (< column (len (tc-nth0 row matrix))))
           (equal (tc-matrix-entry row column
                                   (wbc-matrix-scale c matrix))
                  (* c (tc-matrix-entry row column matrix))))
  :hints (("Goal"
           :use ((:instance tc-nth0-row-of-wbc-matrix-scale-general)
                 (:instance tc-nth0-of-wbc-row-scale-general
                            (row (tc-nth0 row matrix))))
           :in-theory (enable tc-matrix-entry))))

(defthm tc-nth0-row-of-wbc-outer
  (implies (and (natp row) (< row (len left)))
           (equal (tc-nth0 row (wbc-outer left right))
                  (wbc-row-scale (tc-nth0 row left) right)))
  :hints (("Goal" :induct (rgi-matrix-nth-induct left row)
           :in-theory (enable rgi-matrix-nth-induct tc-nth0 wbc-outer))))

(defthm rgi-entry-of-wbc-outer
  (implies (and (natp row) (< row (len left))
                (natp column) (< column (len right)))
           (equal (tc-matrix-entry row column (wbc-outer left right))
                  (* (tc-nth0 row left)
                     (tc-nth0 column right))))
  :hints (("Goal"
           :use ((:instance tc-nth0-row-of-wbc-outer)
                 (:instance tc-nth0-of-wbc-row-scale-general
                            (c (tc-nth0 row left))
                            (row right)))
           :in-theory (enable tc-matrix-entry))))

(defthm len-of-rwd-lift-row-aux
  (equal (len (rwd-lift-row-aux count index indices coefficients))
         (nfix count))
  :hints (("Goal" :induct (rwd-lift-row-aux count index indices coefficients)
           :in-theory (enable rwd-lift-row-aux))))

(defthm len-of-rwd-lift-row
  (equal (len (rwd-lift-row p indices coefficients))
         (nfix p))
  :hints (("Goal"
           :use ((:instance len-of-rwd-lift-row-aux
                            (count p) (index 0)))
           :in-theory (enable rwd-lift-row))))

(defthm rgi-entry-of-lifted-term-matrix
  (implies (and (natp row) (< row (nfix p))
                (natp column) (< column (nfix p)))
           (equal
            (tc-matrix-entry
             row column
             (wbc-term-matrix
              (cons (rwd-lift-row p inputs left)
                    (rwd-lift-row p kernels right))
              coefficient))
            (* coefficient
               (rwd-coefficient-at row inputs left)
               (rwd-coefficient-at column kernels right))))
  :hints (("Goal"
           :use ((:instance rgi-entry-of-wbc-matrix-scale
                            (c coefficient)
                            (matrix (wbc-outer
                                     (rwd-lift-row p inputs left)
                                     (rwd-lift-row p kernels right))))
                 (:instance rgi-entry-of-wbc-outer
                            (left (rwd-lift-row p inputs left))
                            (right (rwd-lift-row p kernels right))))
           :in-theory (e/d (wbc-term-matrix)
                            (rgi-entry-of-wbc-matrix-scale
                             rgi-entry-of-wbc-outer)))))

(defthm rationalp-of-rwd-coefficient-at
  (implies (rational-listp coefficients)
           (rationalp (rwd-coefficient-at index indices coefficients)))
  :hints (("Goal" :induct (rwd-coefficient-at index indices coefficients)
           :in-theory (enable rwd-coefficient-at rational-listp))))

(defthm rational-listp-of-rwd-lift-row-aux
  (implies (rational-listp coefficients)
           (rational-listp
            (rwd-lift-row-aux count index indices coefficients)))
  :hints (("Goal"
           :induct (rwd-lift-row-aux count index indices coefficients)
           :in-theory (enable rwd-lift-row-aux rational-listp))))

(defthm rational-rowp-of-rwd-lift-row
  (implies (rational-listp coefficients)
           (rational-rowp p (rwd-lift-row p indices coefficients)))
  :hints (("Goal"
           :use ((:instance rational-listp-of-rwd-lift-row-aux
                            (count p) (index 0)))
           :in-theory (enable rational-rowp rwd-lift-row))))

(defthm len-of-rwd-lift-terms
  (equal (len (rwd-lift-terms p inputs kernels terms))
         (len terms))
  :hints (("Goal" :induct (rwd-lift-terms p inputs kernels terms)
           :in-theory (enable rwd-lift-terms))))

(defthm wbc-terms-validp-of-rwd-lift-terms
  (implies (wbc-terms-validp n terms)
           (wbc-terms-validp
            p (rwd-lift-terms p inputs kernels terms)))
  :hints (("Goal" :induct (rwd-lift-terms p inputs kernels terms)
           :in-theory (enable rwd-lift-terms wbc-terms-validp))))

(defthm wbc-plan-validp-of-rwd-lift
  (implies (and (wbc-plan-validp n terms post)
                (posp p))
           (wbc-plan-validp
            p (rwd-lift-terms p inputs kernels terms) post))
  :hints (("Goal"
           :use ((:instance len-of-rwd-lift-terms)
                 (:instance wbc-terms-validp-of-rwd-lift-terms))
           :in-theory (enable wbc-plan-validp))))

(defun rgi-plan-entry (row column inputs kernels terms post)
  (if (or (endp terms) (endp post))
      0
    (+ (* (car post)
          (rwd-coefficient-at row inputs (caar terms))
          (rwd-coefficient-at column kernels (cdar terms)))
       (rgi-plan-entry row column inputs kernels
                       (cdr terms) (cdr post)))))

(defthm rgi-consp-of-positive-rational-matrix
  (implies (and (posp rows)
                (rational-matrixp rows cols matrix))
           (consp matrix))
  :hints (("Goal" :in-theory (enable rational-matrixp))))

(defthm rgi-rational-rowp-implies-rational-listp
  (implies (rational-rowp n row)
           (rational-listp row))
  :hints (("Goal" :in-theory (enable rational-rowp))))

(defthm rgi-rational-matrixp-of-lifted-term
  (implies (and (posp p)
                (rational-rowp n left)
                (rational-rowp n right)
                (rationalp coefficient))
           (rational-matrixp
            p p
            (wbc-term-matrix
             (cons (rwd-lift-row p inputs left)
                   (rwd-lift-row p kernels right))
             coefficient)))
  :hints (("Goal"
           :use ((:instance rgi-rational-rowp-implies-rational-listp
                            (row left))
                 (:instance rgi-rational-rowp-implies-rational-listp
                            (row right))
                 (:instance rational-rowp-of-rwd-lift-row
                            (indices inputs) (coefficients left))
                 (:instance rational-rowp-of-rwd-lift-row
                            (indices kernels) (coefficients right))
                 (:instance rational-matrixp-of-wbc-term-matrix
                            (n p)
                            (term (cons (rwd-lift-row p inputs left)
                                        (rwd-lift-row p kernels right)))))
           :in-theory (enable car-cons cdr-cons))))

(defthm rgi-entry-of-lifted-term-matrix-posp
  (implies (and (posp p)
                (natp row) (< row p)
                (natp column) (< column p))
           (equal
            (tc-matrix-entry
             row column
             (wbc-term-matrix
              (cons (rwd-lift-row p inputs left)
                    (rwd-lift-row p kernels right))
              coefficient))
            (* coefficient
               (rwd-coefficient-at row inputs left)
               (rwd-coefficient-at column kernels right))))
  :hints (("Goal"
           :use ((:instance rgi-entry-of-lifted-term-matrix))
           :in-theory (enable posp nfix))))

(defthm rgi-plan-matrix-entry-step-nonempty
  (implies (and (posp p)
                (natp row) (< row p)
                (natp column) (< column p)
                (rational-matrixp p p (wbc-term-matrix term coefficient))
                (rational-matrixp p p (wbc-plan-matrix terms post)))
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
           :use ((:instance rgi-consp-of-positive-rational-matrix
                            (rows p) (cols p)
                            (matrix (wbc-plan-matrix terms post)))
                 (:instance tc-entry-of-wbc-matrix-add-rational
                            (n p)
                            (a (wbc-term-matrix term coefficient))
                            (b (wbc-plan-matrix terms post))))
           :expand ((wbc-plan-matrix (cons term terms)
                                     (cons coefficient post)))
           :in-theory (disable wbc-plan-matrix
                               rgi-consp-of-positive-rational-matrix
                               tc-entry-of-wbc-matrix-add-rational))))

(defthm rgi-matrix-entry-nil
  (equal (tc-matrix-entry row column nil) 0)
  :hints (("Goal" :in-theory (enable tc-matrix-entry tc-nth0))))

(defthm rgi-plan-matrix-left-empty
  (equal (wbc-plan-matrix nil post) nil)
  :hints (("Goal" :in-theory (enable wbc-plan-matrix))))

(defthm rgi-plan-matrix-singleton
  (implies (and (consp post)
                (endp (cdr post)))
           (equal (wbc-plan-matrix (list term) post)
                  (wbc-term-matrix term (car post))))
  :hints (("Goal"
           :expand ((wbc-plan-matrix (list term) post)
                    (wbc-plan-matrix nil (cdr post)))
           :in-theory (disable wbc-plan-matrix))))

(defthm rgi-plan-matrix-entry-step-empty
  (implies (endp (wbc-plan-matrix terms post))
           (equal
            (tc-matrix-entry
             row column
             (wbc-plan-matrix (cons term terms)
                              (cons coefficient post)))
            (tc-matrix-entry row column
                             (wbc-term-matrix term coefficient))))
  :hints (("Goal"
           :expand ((wbc-plan-matrix (cons term terms)
                                     (cons coefficient post)))
           :in-theory (e/d (tc-matrix-entry tc-nth0)
                            (wbc-plan-matrix)))))

(defthm rgi-plan-validp-head-facts
  (implies (wbc-plan-validp n terms post)
           (and (consp terms)
                (consp post)
                (consp (car terms))
                (rational-rowp n (caar terms))
                (rational-rowp n (cdar terms))
                (rationalp (car post))))
  :hints (("Goal" :in-theory (enable wbc-plan-validp
                                      wbc-terms-validp
                                      rational-listp))))

(defthm rgi-equal-len-consp-cdr
  (implies (and (consp a)
                (consp b)
                (equal (len a) (len b)))
           (equal (consp (cdr a))
                  (consp (cdr b))))
  :hints (("Goal" :cases ((consp (cdr a)) (consp (cdr b))))))

(defthm rgi-plan-validp-lengths
  (implies (wbc-plan-validp n terms post)
           (equal (len terms) (len post)))
  :hints (("Goal" :in-theory (enable wbc-plan-validp))))

(defthm rgi-cons-car-cdr
  (implies (consp x)
           (equal (cons (car x) (cdr x)) x)))

(defthm rgi-plan-validp-tail-shapes
  (implies (wbc-plan-validp n terms post)
           (equal (consp (cdr terms))
                  (consp (cdr post))))
  :hints (("Goal"
           :use ((:instance rgi-plan-validp-head-facts)
                 (:instance rgi-plan-validp-lengths)
                 (:instance rgi-equal-len-consp-cdr
                            (a terms) (b post)))
           :in-theory nil)))

(defthm rgi-entry-of-lifted-plan-step
  (implies (and (wbc-plan-validp n terms post)
                (posp p)
                (natp row) (< row p)
                (natp column) (< column p))
           (equal
            (tc-matrix-entry
             row column
             (wbc-plan-matrix
              (rwd-lift-terms p inputs kernels terms) post))
            (+ (* (car post)
                  (rwd-coefficient-at row inputs (caar terms))
                  (rwd-coefficient-at column kernels (cdar terms)))
               (tc-matrix-entry
                row column
                (wbc-plan-matrix
                 (rwd-lift-terms p inputs kernels (cdr terms))
                 (cdr post))))))
  :hints (("Goal" :cases ((endp (cdr terms)))
           :in-theory nil)
          ("Subgoal 2"
           :use ((:instance rgi-plan-validp-head-facts)
                 (:instance rgi-cons-car-cdr (x post))
                 (:instance wbc-plan-validp-of-tail)
                 (:instance wbc-plan-validp-of-rwd-lift
                            (terms (cdr terms)) (post (cdr post)))
                 (:instance rational-matrixp-of-plan-matrix
                            (n p)
                            (terms (rwd-lift-terms p inputs kernels
                                                   (cdr terms)))
                            (post (cdr post)))
                 (:instance rgi-rational-matrixp-of-lifted-term
                            (left (caar terms)) (right (cdar terms))
                            (coefficient (car post)))
                 (:instance rgi-plan-matrix-entry-step-nonempty
                            (term (cons (rwd-lift-row p inputs (caar terms))
                                        (rwd-lift-row p kernels (cdar terms))))
                            (coefficient (car post))
                            (terms (rwd-lift-terms p inputs kernels
                                                   (cdr terms)))
                            (post (cdr post)))
                 (:instance rgi-entry-of-lifted-term-matrix-posp
                            (left (caar terms)) (right (cdar terms))
                            (coefficient (car post))))
           :expand ((rwd-lift-terms p inputs kernels terms))
           :in-theory nil)
          ("Subgoal 1"
           :use ((:instance rgi-plan-validp-head-facts)
                 (:instance rgi-cons-car-cdr (x post))
                 (:instance rgi-plan-validp-tail-shapes)
                 (:instance rgi-rational-matrixp-of-lifted-term
                            (left (caar terms)) (right (cdar terms))
                            (coefficient (car post)))
                 (:instance rgi-plan-matrix-left-empty
                            (post (cdr post)))
                 (:instance rgi-matrix-entry-nil)
                 (:instance rgi-plan-matrix-singleton
                            (term (cons (rwd-lift-row p inputs (caar terms))
                                        (rwd-lift-row p kernels (cdar terms)))))
                 (:instance rgi-entry-of-lifted-term-matrix-posp
                            (left (caar terms)) (right (cdar terms))
                            (coefficient (car post))))
           :expand ((rwd-lift-terms p inputs kernels terms)
                    (rwd-lift-terms p inputs kernels (cdr terms)))
           :in-theory nil)))

(defthm rgi-lifted-plan-entry-empty-terms
  (implies (endp terms)
           (equal
            (tc-matrix-entry
             row column
             (wbc-plan-matrix
              (rwd-lift-terms p inputs kernels terms) post))
            0))
  :hints (("Goal"
           :in-theory (enable rwd-lift-terms wbc-plan-matrix
                              tc-matrix-entry tc-nth0))))

(defthm rgi-entry-of-lifted-plan
  (implies (and (wbc-plan-validp n terms post)
                (posp p)
                (natp row) (< row p)
                (natp column) (< column p))
           (equal
            (tc-matrix-entry
             row column
             (wbc-plan-matrix
              (rwd-lift-terms p inputs kernels terms) post))
            (rgi-plan-entry row column inputs kernels terms post)))
  :hints (("Goal" :induct (wbc-plan-output terms post nil nil)
           :in-theory (enable wbc-plan-output))
          ("Subgoal *1/2"
           :use ((:instance rgi-entry-of-lifted-plan-step)
                 (:instance wbc-plan-validp-of-tail)
                 (:instance rgi-lifted-plan-entry-empty-terms
                            (terms (cdr terms)) (post (cdr post))))
           :expand ((rgi-plan-entry row column inputs kernels terms post)
                    (rgi-plan-entry row column inputs kernels
                                    (cdr terms) (cdr post)))
           :in-theory nil)
          ("Subgoal *1/1"
           :use ((:instance rgi-plan-validp-head-facts)
                 (:instance rgi-entry-of-lifted-plan-step))
           :expand ((rgi-plan-entry row column inputs kernels terms post))
           :in-theory nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Naturality of coefficient matrices under finite index lifting.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm natp-of-rgi-position
  (natp (rgi-position index indices))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (rgi-position index indices)
           :in-theory (enable rgi-position))))

(defthm rgi-len-from-rational-rowp
  (implies (rational-rowp n coefficients)
           (equal (len coefficients) (nfix n)))
  :hints (("Goal" :in-theory (enable rational-rowp))))

(defthm rgi-coefficient-at-position
  (implies (and (rational-rowp n coefficients)
                (equal (len indices) (nfix n))
                (< (rgi-position index indices) (nfix n)))
           (equal (rwd-coefficient-at index indices coefficients)
                  (tc-nth0 (rgi-position index indices) coefficients)))
  :hints (("Goal"
           :use ((:instance rgi-len-from-rational-rowp)
                 (:instance rwd-coefficient-at-is-position))
           :in-theory nil)))

(defthm rgi-wbc-term-matrix-open
  (equal (wbc-term-matrix (cons left right) coefficient)
         (wbc-matrix-scale coefficient (wbc-outer left right)))
  :hints (("Goal" :in-theory (enable wbc-term-matrix))))

(defthm rgi-mul-congruence
  (implies (equal x y)
           (equal (* c x) (* c y)))
  :rule-classes nil)

(defthm rgi-len-of-wbc-outer-row
  (implies (and (natp row) (< row (len left)))
           (equal (len (tc-nth0 row (wbc-outer left right)))
                  (len right)))
  :hints (("Goal"
           :use ((:instance tc-nth0-row-of-wbc-outer)
                 (:instance len-of-wbc-row-scale
                            (c (tc-nth0 row left)) (row right)))
           :in-theory nil)))

(defthm rgi-entry-of-wbc-term-matrix-general
  (implies (and (natp row) (< row (len left))
                (natp column) (< column (len right)))
           (equal (tc-matrix-entry row column
                                   (wbc-term-matrix
                                    (cons left right) coefficient))
                  (* coefficient
                     (tc-nth0 row left)
                     (tc-nth0 column right))))
  :hints (("Goal"
           :use ((:instance tc-equality-chain-3
                            (a (tc-matrix-entry
                                row column
                                (wbc-term-matrix
                                 (cons left right) coefficient)))
                            (b (tc-matrix-entry
                                row column
                                (wbc-matrix-scale
                                 coefficient (wbc-outer left right))))
                            (c (* coefficient
                                  (tc-matrix-entry row column
                                                   (wbc-outer left right))))
                            (d (* coefficient
                                  (tc-nth0 row left)
                                  (tc-nth0 column right))))
                 (:instance rgi-wbc-term-matrix-open)
                 (:instance len-of-wbc-outer
                            (a left) (b right))
                 (:instance rgi-len-of-wbc-outer-row)
                 (:instance rgi-entry-of-wbc-matrix-scale
                            (c coefficient)
                            (matrix (wbc-outer left right)))
                 (:instance rgi-entry-of-wbc-outer)
                 (:instance rgi-mul-congruence
                            (c coefficient)
                            (x (tc-matrix-entry row column
                                                (wbc-outer left right)))
                            (y (* (tc-nth0 row left)
                                  (tc-nth0 column right)))))
           :in-theory nil)))

(defthm rgi-entry-of-term-at-positions
  (implies (and (rational-rowp n left)
                (rational-rowp n right)
                (equal (len inputs) (nfix n))
                (equal (len kernels) (nfix n))
                (< (rgi-position row inputs) (nfix n))
                (< (rgi-position column kernels) (nfix n))
                (rationalp coefficient))
           (equal
            (tc-matrix-entry
             (rgi-position row inputs)
             (rgi-position column kernels)
             (wbc-term-matrix (cons left right) coefficient))
            (* coefficient
               (rwd-coefficient-at row inputs left)
               (rwd-coefficient-at column kernels right))))
  :hints (("Goal"
           :use ((:instance natp-of-rgi-position
                            (index row) (indices inputs))
                 (:instance natp-of-rgi-position
                            (index column) (indices kernels))
                 (:instance rgi-len-from-rational-rowp
                            (coefficients left))
                 (:instance rgi-len-from-rational-rowp
                            (coefficients right))
                 (:instance rgi-coefficient-at-position
                            (index row) (indices inputs)
                            (coefficients left))
                 (:instance rgi-coefficient-at-position
                            (index column) (indices kernels)
                            (coefficients right))
                 (:instance rgi-entry-of-wbc-term-matrix-general
                            (row (rgi-position row inputs))
                            (column (rgi-position column kernels))
                            (left left) (right right)))
           :in-theory nil)))

(defthm rgi-plan-matrix-when-endp-terms
  (implies (endp terms)
           (equal (wbc-plan-matrix terms post) nil))
  :hints (("Goal" :in-theory (enable wbc-plan-matrix))))

(defthm rgi-plan-validp-implies-posp
  (implies (wbc-plan-validp n terms post)
           (posp n))
  :hints (("Goal" :in-theory (enable wbc-plan-validp))))

(defthm rgi-nfix-when-posp
  (implies (posp n)
           (equal (nfix n) n))
  :hints (("Goal" :in-theory (enable posp nfix))))

(defthm rgi-plan-matrix-entry-one-term
  (implies (and (consp terms)
                (consp post)
                (endp (cdr terms))
                (endp (cdr post)))
           (equal (tc-matrix-entry row column
                                   (wbc-plan-matrix terms post))
                  (tc-matrix-entry row column
                                   (wbc-term-matrix
                                    (car terms) (car post)))))
  :hints (("Goal"
           :use ((:instance rgi-cons-car-cdr (x terms))
                 (:instance rgi-cons-car-cdr (x post))
                 (:instance rgi-plan-matrix-when-endp-terms
                            (terms (cdr terms)) (post (cdr post)))
                 (:instance rgi-plan-matrix-entry-step-empty
                            (term (car terms))
                            (coefficient (car post))
                            (terms (cdr terms))
                            (post (cdr post))))
           :in-theory nil)))

(defthm rgi-plan-entry-at-positions-step
  (implies (and (wbc-plan-validp n terms post)
                (equal (len inputs) (nfix n))
                (equal (len kernels) (nfix n))
                (< (rgi-position row inputs) (nfix n))
                (< (rgi-position column kernels) (nfix n)))
           (equal
            (tc-matrix-entry
             (rgi-position row inputs)
             (rgi-position column kernels)
             (wbc-plan-matrix terms post))
            (+ (* (car post)
                  (rwd-coefficient-at row inputs (caar terms))
                  (rwd-coefficient-at column kernels (cdar terms)))
               (tc-matrix-entry
                (rgi-position row inputs)
                (rgi-position column kernels)
                (wbc-plan-matrix (cdr terms) (cdr post))))))
  :hints (("Goal" :cases ((endp (cdr terms)))
           :in-theory nil)
          ("Subgoal 2"
           :use ((:instance rgi-plan-validp-head-facts)
                 (:instance rgi-cons-car-cdr (x terms))
                 (:instance rgi-cons-car-cdr (x (car terms)))
                 (:instance rgi-cons-car-cdr (x post))
                 (:instance rgi-plan-validp-implies-posp)
                 (:instance rgi-nfix-when-posp)
                 (:instance wbc-plan-validp-of-tail)
                 (:instance rational-matrixp-of-plan-matrix
                            (terms (cdr terms)) (post (cdr post)))
                 (:instance rational-matrixp-of-wbc-term-matrix
                            (term (car terms))
                            (coefficient (car post)))
                 (:instance rgi-plan-matrix-entry-step-nonempty
                            (p n)
                            (row (rgi-position row inputs))
                            (column (rgi-position column kernels))
                            (term (car terms))
                            (coefficient (car post))
                            (terms (cdr terms))
                            (post (cdr post)))
                 (:instance rgi-entry-of-term-at-positions
                            (left (caar terms))
                            (right (cdar terms))
                            (coefficient (car post)))
                 (:instance natp-of-rgi-position
                            (index row) (indices inputs))
                 (:instance natp-of-rgi-position
                            (index column) (indices kernels)))
           :in-theory nil)
          ("Subgoal 1"
           :use ((:instance rgi-plan-validp-head-facts)
                 (:instance rgi-plan-validp-tail-shapes)
                 (:instance rgi-cons-car-cdr (x terms))
                 (:instance rgi-cons-car-cdr (x (car terms)))
                 (:instance rgi-cons-car-cdr (x post))
                 (:instance rgi-plan-validp-implies-posp)
                 (:instance rgi-nfix-when-posp)
                 (:instance rgi-plan-matrix-entry-one-term
                            (row (rgi-position row inputs))
                            (column (rgi-position column kernels)))
                 (:instance rgi-plan-matrix-when-endp-terms
                            (terms (cdr terms)) (post (cdr post)))
                 (:instance rgi-matrix-entry-nil
                            (row (rgi-position row inputs))
                            (column (rgi-position column kernels)))
                 (:instance rgi-entry-of-term-at-positions
                            (left (caar terms))
                            (right (cdar terms))
                            (coefficient (car post))))
           :in-theory nil)))

(defthm rgi-plan-entry-at-positions
  (implies (and (wbc-plan-validp n terms post)
                (equal (len inputs) (nfix n))
                (equal (len kernels) (nfix n))
                (< (rgi-position row inputs) (nfix n))
                (< (rgi-position column kernels) (nfix n)))
           (equal
            (rgi-plan-entry row column inputs kernels terms post)
            (tc-matrix-entry
             (rgi-position row inputs)
             (rgi-position column kernels)
             (wbc-plan-matrix terms post))))
  :hints (("Goal" :induct (wbc-plan-output terms post nil nil)
           :in-theory (enable wbc-plan-output))
          ("Subgoal *1/2"
           :use ((:instance rgi-plan-entry-at-positions-step)
                 (:instance wbc-plan-validp-of-tail)
                 (:instance rgi-plan-matrix-when-endp-terms
                            (terms (cdr terms)) (post (cdr post)))
                 (:instance rgi-matrix-entry-nil
                            (row (rgi-position row inputs))
                            (column (rgi-position column kernels))))
           :expand ((rgi-plan-entry row column inputs kernels terms post)
                    (rgi-plan-entry row column inputs kernels
                                    (cdr terms) (cdr post)))
           :in-theory nil)
          ("Subgoal *1/1"
           :use ((:instance rgi-plan-validp-head-facts))
           :in-theory nil)))

(defthm rgi-plan-entry-zero-outside-position
  (implies (or (<= (len inputs) (rgi-position row inputs))
               (<= (len kernels) (rgi-position column kernels)))
           (equal (rgi-plan-entry row column inputs kernels terms post) 0))
  :hints (("Goal" :induct (wbc-plan-output terms post nil nil)
           :in-theory (enable wbc-plan-output))
          ("Subgoal *1/2"
           :use ((:instance rwd-coefficient-at-zero-outside-position
                            (index row) (indices inputs)
                            (coefficients (caar terms)))
                 (:instance rwd-coefficient-at-zero-outside-position
                            (index column) (indices kernels)
                            (coefficients (cdar terms))))
           :expand ((rgi-plan-entry row column inputs kernels terms post))
           :in-theory nil)
          ("Subgoal *1/1"
           :expand ((rgi-plan-entry row column inputs kernels terms post))
           :in-theory nil)))

(defthm rgi-lifted-entry-when-inside
  (implies (and (posp n)
                (natp out)
                (< (rgi-position row inputs) n)
                (< (rgi-position column kernels) n))
           (equal (rgi-lifted-entry n out row column inputs kernels)
                  (if (equal (mod (+ (rgi-position row inputs)
                                     (rgi-position column kernels))
                                  n)
                             out)
                      1 0)))
  :hints (("Goal" :in-theory (enable rgi-lifted-entry posp nfix))))

(defthm rgi-lifted-entry-when-outside
  (implies (or (<= (nfix n) (rgi-position row inputs))
               (<= (nfix n) (rgi-position column kernels)))
           (equal (rgi-lifted-entry n out row column inputs kernels) 0))
  :hints (("Goal" :in-theory (enable rgi-lifted-entry))))

(defthm rgi-entry-of-compact-lifted-plan-inside
  (implies
   (and (tc-compact-post-certifiesp n out post)
        (natp out)
        (posp p)
        (equal (len inputs) (nfix n))
        (equal (len kernels) (nfix n))
        (< (rgi-position row inputs) (nfix n))
        (< (rgi-position column kernels) (nfix n))
        (natp row) (< row p)
        (natp column) (< column p))
   (equal
    (tc-matrix-entry
     row column
     (wbc-plan-matrix
      (rwd-lift-terms p inputs kernels (tc-plan-terms n)) post))
    (rgi-lifted-entry n out row column inputs kernels)))
  :hints
  (("Goal"
    :use
    ((:instance tc-equality-chain-5
                (a (tc-matrix-entry
                    row column
                    (wbc-plan-matrix
                     (rwd-lift-terms p inputs kernels (tc-plan-terms n))
                     post)))
                (b (rgi-plan-entry
                    row column inputs kernels (tc-plan-terms n) post))
                (c (tc-matrix-entry
                    (rgi-position row inputs)
                    (rgi-position column kernels)
                    (wbc-plan-matrix (tc-plan-terms n) post)))
                (d (if (equal
                        (mod (+ (rgi-position row inputs)
                                (rgi-position column kernels)) n)
                        out)
                       1 0))
                (e (rgi-lifted-entry n out row column inputs kernels)))
     (:instance natp-of-rgi-position
                (index row) (indices inputs))
     (:instance natp-of-rgi-position
                (index column) (indices kernels))
     (:instance tc-compact-post-plan-validp)
     (:instance tc-compact-post-certifiesp-implies-posp)
     (:instance rgi-nfix-when-posp)
     (:instance rgi-entry-of-lifted-plan
                (terms (tc-plan-terms n)))
     (:instance rgi-plan-entry-at-positions
                (terms (tc-plan-terms n)))
     (:instance tc-entry-of-compact-certified-plan
                (row (rgi-position row inputs))
                (column (rgi-position column kernels)))
     (:instance rgi-lifted-entry-when-inside))
    :in-theory nil)))

(defthm rgi-entry-of-compact-lifted-plan-outside
  (implies
   (and (tc-compact-post-certifiesp n out post)
        (posp p)
        (equal (len inputs) (nfix n))
        (equal (len kernels) (nfix n))
        (or (<= (nfix n) (rgi-position row inputs))
            (<= (nfix n) (rgi-position column kernels)))
        (natp row) (< row p)
        (natp column) (< column p))
   (equal
    (tc-matrix-entry
     row column
     (wbc-plan-matrix
      (rwd-lift-terms p inputs kernels (tc-plan-terms n)) post))
    (rgi-lifted-entry n out row column inputs kernels)))
  :hints
  (("Goal"
    :use ((:instance tc-compact-post-plan-validp)
          (:instance rgi-entry-of-lifted-plan
                     (terms (tc-plan-terms n)))
          (:instance rgi-plan-entry-zero-outside-position
                     (terms (tc-plan-terms n)))
          (:instance rgi-lifted-entry-when-outside))
    :in-theory nil)))

(defthm rgi-not-less-implies-ge
  (implies (and (rationalp a) (rationalp b) (not (< a b)))
           (<= b a)))

(defthm rgi-inside-or-outside
  (implies (and (rationalp a) (rationalp b) (rationalp n))
           (or (and (< a n) (< b n))
               (or (<= n a) (<= n b))))
  :rule-classes nil)

(defthm rgi-entry-of-compact-lifted-plan
  (implies
   (and (tc-compact-post-certifiesp n out post)
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
      (rwd-lift-terms p inputs kernels (tc-plan-terms n)) post))
    (rgi-lifted-entry n out row column inputs kernels)))
  :hints
  (("Goal"
    :use ((:instance natp-of-rgi-position
                     (index row) (indices inputs))
          (:instance natp-of-rgi-position
                     (index column) (indices kernels))
          (:instance rgi-inside-or-outside
                     (a (rgi-position row inputs))
                     (b (rgi-position column kernels))
                     (n (nfix n)))
          (:instance rgi-entry-of-compact-lifted-plan-inside)
          (:instance rgi-entry-of-compact-lifted-plan-outside))
    :in-theory nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The two exceptional Rader terms.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm len-of-rwd-constant-row-aux
  (equal (len (rwd-constant-row-aux count value)) (nfix count))
  :hints (("Goal" :induct (rwd-constant-row-aux count value)
           :in-theory (enable rwd-constant-row-aux))))

(defthm rational-listp-of-rwd-constant-row-aux
  (implies (rationalp value)
           (rational-listp (rwd-constant-row-aux count value)))
  :hints (("Goal" :induct (rwd-constant-row-aux count value)
           :in-theory (enable rwd-constant-row-aux rational-listp))))

(defthm rational-rowp-of-rwd-constant-row-aux
  (implies (rationalp value)
           (rational-rowp count (rwd-constant-row-aux count value)))
  :hints (("Goal"
           :use ((:instance len-of-rwd-constant-row-aux)
                 (:instance rational-listp-of-rwd-constant-row-aux))
           :in-theory (enable rational-rowp))))

(defthm len-of-rwd-unit-row-aux
  (equal (len (rwd-unit-row-aux count index position)) (nfix count))
  :hints (("Goal" :induct (rwd-unit-row-aux count index position)
           :in-theory (enable rwd-unit-row-aux))))

(defthm rational-listp-of-rwd-unit-row-aux
  (rational-listp (rwd-unit-row-aux count index position))
  :hints (("Goal" :induct (rwd-unit-row-aux count index position)
           :in-theory (enable rwd-unit-row-aux rational-listp))))

(defthm rational-rowp-of-rwd-unit-row
  (rational-rowp p (rwd-unit-row p position))
  :hints (("Goal"
           :use ((:instance len-of-rwd-unit-row-aux
                            (count p) (index 0))
                 (:instance rational-listp-of-rwd-unit-row-aux
                            (count p) (index 0)))
           :in-theory (enable rwd-unit-row rational-rowp))))

(defthm tc-compact-post-rational-listp
  (implies (tc-compact-post-certifiesp n out post)
           (rational-listp post))
  :hints (("Goal" :in-theory (enable tc-compact-post-certifiesp))))

(defthm tc-compact-post-length
  (implies (tc-compact-post-certifiesp n out post)
           (equal (len post) (1- (* 2 n))))
  :hints (("Goal" :in-theory (enable tc-compact-post-certifiesp))))

(defthm rgi-wbc-terms-validp-cons2
  (implies (and (posp n)
                (rational-rowp n left0)
                (rational-rowp n right0)
                (rational-rowp n left1)
                (rational-rowp n right1)
                (wbc-terms-validp n rest))
           (wbc-terms-validp
            n (cons (cons left0 right0)
                    (cons (cons left1 right1) rest))))
  :hints (("Goal"
           :expand ((wbc-terms-validp
                     n (cons (cons left0 right0)
                             (cons (cons left1 right1) rest)))
                    (wbc-terms-validp
                     n (cons (cons left1 right1) rest)))
           :in-theory (disable wbc-terms-validp))))

(defthmd rgi-full-terms-open
  (equal
   (rwd-full-terms p inputs kernels terms)
   (cons (cons (rwd-constant-row-aux p 1)
               (rwd-unit-row p 0))
         (cons (cons (rwd-unit-row p 0)
                     (rwd-unit-row p 0))
               (rwd-lift-terms p inputs kernels terms))))
  :hints (("Goal" :in-theory '(rwd-full-terms
                                rwd-dc-term
                                rwd-base-term))))

(defthm rgi-full-terms-validp
  (implies (and (posp p)
                (wbc-terms-validp n terms))
           (wbc-terms-validp
            p (rwd-full-terms p inputs kernels terms)))
  :hints (("Goal"
           :use ((:instance wbc-terms-validp-of-rwd-lift-terms)
                 (:instance rational-rowp-of-rwd-constant-row-aux
                            (count p) (value 1))
                 (:instance rational-rowp-of-rwd-unit-row
                            (position 0))
                 (:instance rgi-full-terms-open)
                 (:instance rgi-wbc-terms-validp-cons2
                            (n p)
                            (left0 (rwd-constant-row-aux p 1))
                            (right0 (rwd-unit-row p 0))
                            (left1 (rwd-unit-row p 0))
                            (right1 (rwd-unit-row p 0))
                            (rest (rwd-lift-terms
                                   p inputs kernels terms))))
           :in-theory nil)))

(defthm rational-listp-of-rwd-nonzero-post
  (implies (rational-listp post)
           (rational-listp (rwd-nonzero-post post)))
  :hints (("Goal" :in-theory (enable rwd-nonzero-post rational-listp))))

(defthm rgi-len-cons2
  (equal (len (cons a (cons b rest)))
         (+ 2 (len rest)))
  :hints (("Goal" :in-theory (enable len))))

(defthm len-of-rwd-full-terms
  (equal (len (rwd-full-terms p inputs kernels terms))
         (+ 2 (len terms)))
  :hints (("Goal"
           :use ((:instance rgi-full-terms-open)
                 (:instance rgi-len-cons2
                            (a (cons (rwd-constant-row-aux p 1)
                                     (rwd-unit-row p 0)))
                            (b (cons (rwd-unit-row p 0)
                                     (rwd-unit-row p 0)))
                            (rest (rwd-lift-terms p inputs kernels terms)))
                 (:instance len-of-rwd-lift-terms))
           :in-theory nil)))

(defthm rgi-rwd-nonzero-post-open
  (equal (rwd-nonzero-post post)
         (cons 0 (cons 1 post)))
  :hints (("Goal" :in-theory '(rwd-nonzero-post))))

(defthm len-of-rwd-nonzero-post
  (equal (len (rwd-nonzero-post post))
         (+ 2 (len post)))
  :hints (("Goal"
           :use ((:instance rgi-rwd-nonzero-post-open)
                 (:instance rgi-len-cons2
                            (a 0) (b 1) (rest post)))
           :in-theory nil)))

(defthm consp-of-rwd-full-terms
  (consp (rwd-full-terms p inputs kernels terms))
  :hints (("Goal"
           :expand ((rwd-full-terms p inputs kernels terms))
           :in-theory '(consp))))

(defthm rgi-wbc-plan-validp-components
  (implies (wbc-plan-validp n terms post)
           (and (wbc-terms-validp n terms)
                (rational-listp post)
                (equal (len terms) (len post))))
  :hints (("Goal" :in-theory (enable wbc-plan-validp))))

(defthm rgi-wbc-plan-validp-from-components
  (implies (and (posp n)
                (consp terms)
                (wbc-terms-validp n terms)
                (rational-listp post)
                (equal (len terms) (len post)))
           (wbc-plan-validp n terms post))
  :hints (("Goal"
           :expand ((wbc-plan-validp n terms post))
           :in-theory nil)))

(defthm rgi-nonzero-full-plan-validp
  (implies (and (tc-compact-post-certifiesp n out post)
                (posp p))
           (wbc-plan-validp
            p
            (rwd-full-terms p inputs kernels (tc-plan-terms n))
            (rwd-nonzero-post post)))
  :hints (("Goal"
           :use ((:instance tc-compact-post-plan-validp)
                 (:instance rgi-wbc-plan-validp-components
                            (terms (tc-plan-terms n)))
                 (:instance rgi-full-terms-validp
                            (terms (tc-plan-terms n)))
                 (:instance rational-listp-of-rwd-nonzero-post)
                 (:instance len-of-rwd-full-terms
                            (terms (tc-plan-terms n)))
                 (:instance len-of-rwd-nonzero-post)
                 (:instance consp-of-rwd-full-terms
                            (terms (tc-plan-terms n)))
                 (:instance rgi-wbc-plan-validp-from-components
                            (n p)
                            (terms (rwd-full-terms
                                    p inputs kernels (tc-plan-terms n)))
                            (post (rwd-nonzero-post post))))
           :in-theory nil)))
