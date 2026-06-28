; Certified rational bilinear algorithms for cyclic convolution.
(in-package "ACL2")
(include-book "zam-qcx-adp-linear")
(include-book "arithmetic-5/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Linear and bilinear evaluation over rational-complex vectors.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun wbc-linear (coeffs xs)
  (if (or (endp coeffs) (endp xs))
      (qcx-zero)
    (qcx-add (qcx-scale (car coeffs) (car xs))
             (wbc-linear (cdr coeffs) (cdr xs)))))

(defun wbc-row-eval (row x ys)
  (if (or (endp row) (endp ys))
      (qcx-zero)
    (qcx-add (qcx-scale (car row)
                        (qcx-mul x (car ys)))
             (wbc-row-eval (cdr row) x (cdr ys)))))

(defun wbc-matrix-eval (matrix xs ys)
  (if (or (endp matrix) (endp xs))
      (qcx-zero)
    (qcx-add (wbc-row-eval (car matrix) (car xs) ys)
             (wbc-matrix-eval (cdr matrix) (cdr xs) ys))))

(defun rational-rowp (n row)
  (and (equal (len row) (nfix n))
       (rational-listp row)))

(defun rational-matrixp (rows cols matrix)
  (if (zp rows)
      (endp matrix)
    (and (consp matrix)
         (rational-rowp cols (car matrix))
         (rational-matrixp (1- rows) cols (cdr matrix)))))

(defun qcx-vectorp (n xs)
  (and (equal (len xs) (nfix n))
       (qcx-list-rationalp xs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Canonical rational matrices.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun wbc-row-add (a b)
  (if (or (endp a) (endp b))
      nil
    (cons (+ (car a) (car b))
          (wbc-row-add (cdr a) (cdr b)))))

(defun wbc-matrix-add (a b)
  (if (or (endp a) (endp b))
      nil
    (cons (wbc-row-add (car a) (car b))
          (wbc-matrix-add (cdr a) (cdr b)))))

(defun wbc-row-scale (c row)
  (if (endp row)
      nil
    (cons (* c (car row))
          (wbc-row-scale c (cdr row)))))

(defun wbc-matrix-scale (c matrix)
  (if (endp matrix)
      nil
    (cons (wbc-row-scale c (car matrix))
          (wbc-matrix-scale c (cdr matrix)))))

(defun wbc-outer (a b)
  (if (endp a)
      nil
    (cons (wbc-row-scale (car a) b)
          (wbc-outer (cdr a) b))))

(defthm qcx-scale-zero
  (equal (qcx-scale c (qcx-zero)) (qcx-zero)))

(defthm qcx-scale-one
  (implies (qcx-rationalp x)
           (equal (qcx-scale 1 x) x)))

(defthm qcx-scale-distributes-over-add
  (equal (qcx-scale c (qcx-add x y))
         (qcx-add (qcx-scale c x)
                  (qcx-scale c y))))

(defthm qcx-scale-compose
  (equal (qcx-scale a (qcx-scale b x))
         (qcx-scale (* a b) x)))

(defthm qcx-mul-of-scale-left
  (equal (qcx-mul (qcx-scale a x) y)
         (qcx-scale a (qcx-mul x y))))

(defthm qcx-mul-of-scale-right
  (equal (qcx-mul x (qcx-scale a y))
         (qcx-scale a (qcx-mul x y))))

(defun wbc-three-list-induct (a b xs)
  (if (or (endp a) (endp b) (endp xs))
      nil
    (wbc-three-list-induct (cdr a) (cdr b) (cdr xs))))

(defthm qcx-scale-of-add-coefficients
  (equal (qcx-scale (+ a b) x)
         (qcx-add (qcx-scale a x)
                  (qcx-scale b x))))

(defthm qcx-add-interchange
  (equal (qcx-add (qcx-add a r) (qcx-add b s))
         (qcx-add (qcx-add a b) (qcx-add r s)))
  :hints (("Goal"
           :use ((:instance qcx-add-associative (x a) (y r)
                            (z (qcx-add b s)))
                 (:instance qcx-add-associative (x r) (y b) (z s))
                 (:instance qcx-add-commutative (x r) (y b))
                 (:instance qcx-add-associative (x a) (y b)
                            (z (qcx-add r s))))
           :in-theory (disable qcx-add-associative
                               qcx-add-commutative))))


(defthm qcx-add-scaled-interchange
  (equal (qcx-add (qcx-scale (+ a b) x)
                  (qcx-add r s))
         (qcx-add (qcx-add (qcx-scale a x) r)
                  (qcx-add (qcx-scale b x) s)))
  :hints (("Goal"
           :use ((:instance qcx-scale-of-add-coefficients)
                 (:instance qcx-add-interchange
                            (a (qcx-scale a x))
                            (b (qcx-scale b x))))
           :in-theory nil)))

(defthm wbc-linear-of-row-add
  (implies (and (rational-listp a)
                (rational-listp b)
                (qcx-list-rationalp xs)
                (equal (len a) (len b))
                (equal (len a) (len xs)))
           (equal (wbc-linear (wbc-row-add a b) xs)
                  (qcx-add (wbc-linear a xs)
                           (wbc-linear b xs))))
  :hints (("Goal"
           :induct (wbc-three-list-induct a b xs)
           :in-theory (e/d (wbc-three-list-induct
                             wbc-row-add wbc-linear)
                            (qcx-add qcx-scale
                             qcx-add-associative
                             qcx-add-commutative
                             qcx-add-interchange
                             qcx-scale-of-add-coefficients)))))

(defun wbc-two-list-induct (a xs)
  (if (or (endp a) (endp xs))
      nil
    (wbc-two-list-induct (cdr a) (cdr xs))))

(defthm qcx-linear-scale-step
  (equal (qcx-add (qcx-scale c rest)
                  (qcx-scale (* c a) x))
         (qcx-scale c
                    (qcx-add (qcx-scale a x) rest)))
  :hints (("Goal"
           :use ((:instance qcx-scale-distributes-over-add
                            (c c) (x (qcx-scale a x)) (y rest))
                 (:instance qcx-scale-compose
                            (a c) (b a) (x x))
                 (:instance qcx-add-commutative
                            (x (qcx-scale c rest))
                            (y (qcx-scale (* c a) x))))
           :in-theory nil)))

(defthm qcx-scale-of-quoted-zero
  (equal (qcx-scale c '(0 . 0)) '(0 . 0))
  :hints (("Goal" :in-theory (enable qcx-scale qcx-re qcx-im qcx))))

(defthm wbc-linear-of-row-scale
  (implies (and (rationalp c)
                (rational-listp row)
                (qcx-list-rationalp xs)
                (equal (len row) (len xs)))
           (equal (wbc-linear (wbc-row-scale c row) xs)
                  (qcx-scale c (wbc-linear row xs))))
  :hints (("Goal"
           :induct (wbc-two-list-induct row xs)
           :in-theory (e/d (wbc-two-list-induct
                             wbc-row-scale wbc-linear)
                            (qcx-add qcx-scale qcx-zero
                             qcx-scale-compose
                             qcx-scale-distributes-over-add)))))

(defthm wbc-row-eval-of-row-add
  (implies (and (rational-listp a)
                (rational-listp b)
                (qcx-rationalp x)
                (qcx-list-rationalp ys)
                (equal (len a) (len b))
                (equal (len a) (len ys)))
           (equal (wbc-row-eval (wbc-row-add a b) x ys)
                  (qcx-add (wbc-row-eval a x ys)
                           (wbc-row-eval b x ys))))
  :hints (("Goal"
           :induct (wbc-three-list-induct a b ys)
           :in-theory (e/d (wbc-three-list-induct
                             wbc-row-add wbc-row-eval)
                            (qcx-add qcx-scale qcx-mul
                             qcx-add-associative
                             qcx-add-commutative
                             qcx-add-interchange
                             qcx-scale-of-add-coefficients)))))

(defthm wbc-row-eval-of-row-scale
  (implies (and (rationalp c)
                (rational-listp row)
                (qcx-rationalp x)
                (qcx-list-rationalp ys)
                (equal (len row) (len ys)))
           (equal (wbc-row-eval (wbc-row-scale c row) x ys)
                  (qcx-scale c (wbc-row-eval row x ys))))
  :hints (("Goal"
           :induct (wbc-two-list-induct row ys)
           :in-theory (e/d (wbc-two-list-induct
                             wbc-row-scale wbc-row-eval)
                            (qcx-add qcx-scale qcx-mul qcx-zero
                             qcx-scale-compose
                             qcx-scale-distributes-over-add)))))

(defun wbc-rational-matrix-listp (m matrix)
  (if (endp matrix)
      t
    (and (rational-rowp m (car matrix))
         (wbc-rational-matrix-listp m (cdr matrix)))))

(defthm rational-matrixp-implies-matrix-listp
  (implies (rational-matrixp n m matrix)
           (wbc-rational-matrix-listp m matrix))
  :hints (("Goal"
           :induct (rational-matrixp n m matrix)
           :in-theory (enable rational-matrixp
                              wbc-rational-matrix-listp))))

(defthm rational-matrixp-implies-length
  (implies (rational-matrixp n m matrix)
           (equal (len matrix) (nfix n)))
  :hints (("Goal"
           :induct (rational-matrixp n m matrix)
           :in-theory (enable rational-matrixp))))

(defthm wbc-matrix-eval-of-matrix-add-list
  (implies (and (wbc-rational-matrix-listp m a)
                (wbc-rational-matrix-listp m b)
                (qcx-list-rationalp xs)
                (qcx-list-rationalp ys)
                (equal (len a) (len b))
                (equal (len a) (len xs))
                (equal (len ys) (nfix m)))
           (equal (wbc-matrix-eval (wbc-matrix-add a b) xs ys)
                  (qcx-add (wbc-matrix-eval a xs ys)
                           (wbc-matrix-eval b xs ys))))
  :hints (("Goal"
           :induct (wbc-three-list-induct a b xs)
           :in-theory (e/d (wbc-three-list-induct
                             wbc-rational-matrix-listp rational-rowp
                             wbc-matrix-add wbc-matrix-eval)
                            (qcx-add qcx-scale qcx-mul qcx-zero
                             qcx-add-associative qcx-add-commutative)))))

(defthm wbc-matrix-eval-of-matrix-add
  (implies (and (rational-matrixp n m a)
                (rational-matrixp n m b)
                (qcx-vectorp n xs)
                (qcx-vectorp m ys))
           (equal (wbc-matrix-eval (wbc-matrix-add a b) xs ys)
                  (qcx-add (wbc-matrix-eval a xs ys)
                           (wbc-matrix-eval b xs ys))))
  :hints (("Goal"
           :use ((:instance wbc-matrix-eval-of-matrix-add-list))
           :in-theory (enable qcx-vectorp))))

(defthm wbc-matrix-eval-of-matrix-scale-list
  (implies (and (rationalp c)
                (wbc-rational-matrix-listp m matrix)
                (qcx-list-rationalp xs)
                (qcx-list-rationalp ys)
                (equal (len matrix) (len xs))
                (equal (len ys) (nfix m)))
           (equal (wbc-matrix-eval (wbc-matrix-scale c matrix) xs ys)
                  (qcx-scale c (wbc-matrix-eval matrix xs ys))))
  :hints (("Goal"
           :induct (wbc-two-list-induct matrix xs)
           :in-theory (e/d (wbc-two-list-induct
                             wbc-rational-matrix-listp rational-rowp
                             wbc-matrix-scale wbc-matrix-eval)
                            (qcx-add qcx-scale qcx-mul qcx-zero
                             qcx-scale-compose)))))

(defthm wbc-matrix-eval-of-matrix-scale
  (implies (and (rationalp c)
                (rational-matrixp n m matrix)
                (qcx-vectorp n xs)
                (qcx-vectorp m ys))
           (equal (wbc-matrix-eval (wbc-matrix-scale c matrix) xs ys)
                  (qcx-scale c (wbc-matrix-eval matrix xs ys))))
  :hints (("Goal"
           :use ((:instance wbc-matrix-eval-of-matrix-scale-list))
           :in-theory (enable qcx-vectorp))))

(defthm qcx-mul-of-quoted-zero-left
  (equal (qcx-mul '(0 . 0) x) '(0 . 0))
  :hints (("Goal" :in-theory (enable qcx-mul qcx qcx-re qcx-im))))

(defthm wbc-row-eval-is-mul-linear
  (implies (and (qcx-rationalp x)
                (qcx-list-rationalp ys)
                (rational-listp row)
                (equal (len row) (len ys)))
           (equal (wbc-row-eval row x ys)
                  (qcx-mul x (wbc-linear row ys))))
  :hints (("Goal"
           :induct (wbc-two-list-induct row ys)
           :in-theory (e/d (wbc-two-list-induct
                             wbc-row-eval wbc-linear)
                            (qcx-add qcx-scale qcx-mul qcx-zero)))))

(defthm wbc-row-eval-of-outer-row
  (implies (and (equal (len b) (len ys))
                (qcx-rationalp x)
                (qcx-list-rationalp ys)
                (rational-listp b)
                (rationalp a))
           (equal (wbc-row-eval (wbc-row-scale a b) x ys)
                  (qcx-mul (qcx-scale a x)
                           (wbc-linear b ys))))
  :hints (("Goal"
           :use ((:instance wbc-row-eval-of-row-scale
                            (c a) (row b))
                 (:instance wbc-row-eval-is-mul-linear
                            (row b))
                 (:instance qcx-mul-of-scale-left
                            (y (wbc-linear b ys))))
           :in-theory nil)))

(defthm wbc-matrix-eval-of-outer
  (implies (and (equal (len a) (len xs))
                (equal (len b) (len ys))
                (rational-listp a)
                (rational-listp b)
                (qcx-list-rationalp xs)
                (qcx-list-rationalp ys))
           (equal (wbc-matrix-eval (wbc-outer a b) xs ys)
                  (qcx-mul (wbc-linear a xs)
                           (wbc-linear b ys))))
  :hints (("Goal"
           :induct (wbc-two-list-induct a xs)
           :in-theory (e/d (wbc-two-list-induct
                             wbc-outer wbc-matrix-eval wbc-linear)
                            (qcx-add qcx-scale qcx-mul qcx-zero)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Rank-one plans and their coefficient matrices.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A rank term is (left-row . right-row).  POST supplies one rational
; coefficient per rank term for a single output.
(defun wbc-term-output (term coefficient xs ys)
  (qcx-scale coefficient
             (qcx-mul (wbc-linear (car term) xs)
                      (wbc-linear (cdr term) ys))))

(defun wbc-term-matrix (term coefficient)
  (wbc-matrix-scale coefficient
                    (wbc-outer (car term) (cdr term))))

(defun wbc-plan-output (terms post xs ys)
  (if (or (endp terms) (endp post))
      (qcx-zero)
    (qcx-add (wbc-term-output (car terms) (car post) xs ys)
             (wbc-plan-output (cdr terms) (cdr post) xs ys))))

(defun wbc-plan-matrix (terms post)
  (if (or (endp terms) (endp post))
      nil
    (let ((here (wbc-term-matrix (car terms) (car post)))
          (rest (wbc-plan-matrix (cdr terms) (cdr post))))
      (if (endp rest) here (wbc-matrix-add here rest)))))

(defun wbc-terms-validp (n terms)
  (if (endp terms)
      t
    (and (consp (car terms))
         (rational-rowp n (caar terms))
         (rational-rowp n (cdar terms))
         (wbc-terms-validp n (cdr terms)))))

(defun wbc-plan-validp (n terms post)
  (and (posp n)
       (consp terms)
       (wbc-terms-validp n terms)
       (rational-listp post)
       (equal (len terms) (len post))))

(defthm len-of-wbc-row-scale
  (equal (len (wbc-row-scale c row)) (len row))
  :hints (("Goal"
           :induct (wbc-row-scale c row)
           :in-theory (enable wbc-row-scale))))

(defthm rational-listp-of-wbc-row-scale
  (implies (and (rationalp c)
                (rational-listp row))
           (rational-listp (wbc-row-scale c row)))
  :hints (("Goal"
           :induct (wbc-row-scale c row)
           :in-theory (enable wbc-row-scale))))

(defthm rational-rowp-of-row-scale
  (implies (and (rational-rowp n row) (rationalp c))
           (rational-rowp n (wbc-row-scale c row)))
  :hints (("Goal" :in-theory (enable rational-rowp))))

(defthm len-of-wbc-outer
  (equal (len (wbc-outer a b)) (len a))
  :hints (("Goal"
           :induct (wbc-outer a b)
           :in-theory (enable wbc-outer))))

(defthm matrix-listp-of-wbc-outer
  (implies (and (rational-listp a)
                (rational-rowp n b))
           (wbc-rational-matrix-listp n (wbc-outer a b)))
  :hints (("Goal"
           :induct (wbc-outer a b)
           :in-theory (enable wbc-outer
                              wbc-rational-matrix-listp))))

(defthm matrix-listp-implies-rational-matrixp-of-len
  (implies (wbc-rational-matrix-listp m matrix)
           (rational-matrixp (len matrix) m matrix))
  :hints (("Goal"
           :induct (wbc-rational-matrix-listp m matrix)
           :in-theory (enable wbc-rational-matrix-listp
                              rational-matrixp))))

(defthm rational-matrixp-of-nfix-first
  (equal (rational-matrixp (nfix n) m matrix)
         (rational-matrixp n m matrix))
  :hints (("Goal"
           :induct (rational-matrixp n m matrix)
           :in-theory (enable rational-matrixp))))

(defthm rational-matrixp-of-outer
  (implies (and (rational-rowp n a)
                (rational-rowp n b))
           (rational-matrixp n n (wbc-outer a b)))
  :hints (("Goal"
           :use ((:instance matrix-listp-implies-rational-matrixp-of-len
                            (m n) (matrix (wbc-outer a b))))
           :in-theory (enable rational-rowp))))

(defthm len-of-wbc-matrix-scale
  (equal (len (wbc-matrix-scale c matrix)) (len matrix))
  :hints (("Goal"
           :induct (wbc-matrix-scale c matrix)
           :in-theory (enable wbc-matrix-scale))))

(defthm matrix-listp-of-wbc-matrix-scale
  (implies (and (rationalp c)
                (wbc-rational-matrix-listp m matrix))
           (wbc-rational-matrix-listp
            m (wbc-matrix-scale c matrix)))
  :hints (("Goal"
           :induct (wbc-matrix-scale c matrix)
           :in-theory (enable wbc-matrix-scale
                              wbc-rational-matrix-listp))))

(defthm rational-matrixp-of-matrix-scale
  (implies (and (rational-matrixp n m matrix)
                (rationalp c))
           (rational-matrixp n m (wbc-matrix-scale c matrix)))
  :hints (("Goal"
           :use ((:instance matrix-listp-implies-rational-matrixp-of-len
                            (matrix (wbc-matrix-scale c matrix)))))))

(defthm len-of-wbc-row-add
  (implies (equal (len a) (len b))
           (equal (len (wbc-row-add a b)) (len a)))
  :hints (("Goal"
           :induct (wbc-row-add a b)
           :in-theory (enable wbc-row-add))))

(defthm rational-listp-of-wbc-row-add
  (implies (and (rational-listp a)
                (rational-listp b)
                (equal (len a) (len b)))
           (rational-listp (wbc-row-add a b)))
  :hints (("Goal"
           :induct (wbc-row-add a b)
           :in-theory (enable wbc-row-add))))

(defthm rational-rowp-of-row-add
  (implies (and (rational-rowp n a) (rational-rowp n b))
           (rational-rowp n (wbc-row-add a b)))
  :hints (("Goal" :in-theory (enable rational-rowp))))

(defthm len-of-wbc-matrix-add
  (implies (equal (len a) (len b))
           (equal (len (wbc-matrix-add a b)) (len a)))
  :hints (("Goal"
           :induct (wbc-matrix-add a b)
           :in-theory (enable wbc-matrix-add))))

(defthm matrix-listp-of-wbc-matrix-add
  (implies (and (wbc-rational-matrix-listp m a)
                (wbc-rational-matrix-listp m b)
                (equal (len a) (len b)))
           (wbc-rational-matrix-listp m (wbc-matrix-add a b)))
  :hints (("Goal"
           :induct (wbc-matrix-add a b)
           :in-theory (enable wbc-matrix-add
                              wbc-rational-matrix-listp))))

(defthm rational-matrixp-of-matrix-add
  (implies (and (rational-matrixp n m a)
                (rational-matrixp n m b))
           (rational-matrixp n m (wbc-matrix-add a b)))
  :hints (("Goal"
           :use ((:instance matrix-listp-implies-rational-matrixp-of-len
                            (matrix (wbc-matrix-add a b)))))))

(defthm qcx-rationalp-of-wbc-linear
  (implies (and (rational-listp coeffs)
                (qcx-list-rationalp xs))
           (qcx-rationalp (wbc-linear coeffs xs)))
  :hints (("Goal"
           :induct (wbc-linear coeffs xs)
           :in-theory (enable wbc-linear))))

(defthm qcx-rationalp-of-wbc-term-output
  (implies (and (consp term)
                (rational-listp (car term))
                (rational-listp (cdr term))
                (rationalp coefficient)
                (qcx-list-rationalp xs)
                (qcx-list-rationalp ys))
           (qcx-rationalp
            (wbc-term-output term coefficient xs ys)))
  :hints (("Goal"
           :use ((:instance qcx-rationalp-of-wbc-linear
                            (coeffs (car term)) (xs xs))
                 (:instance qcx-rationalp-of-wbc-linear
                            (coeffs (cdr term)) (xs ys)))
           :in-theory (e/d (wbc-term-output)
                            (qcx qcx-re qcx-im qcx-rationalp
                             qcx-scale qcx-mul)))))

(defthm wbc-term-output-is-matrix-eval
  (implies (and (consp term)
                (rational-rowp n (car term))
                (rational-rowp n (cdr term))
                (rationalp coefficient)
                (qcx-vectorp n xs)
                (qcx-vectorp n ys))
           (equal (wbc-term-output term coefficient xs ys)
                  (wbc-matrix-eval
                   (wbc-term-matrix term coefficient) xs ys)))
  :hints (("Goal"
           :use ((:instance rational-matrixp-of-outer
                            (a (car term)) (b (cdr term)))
                 (:instance wbc-matrix-eval-of-outer
                            (a (car term)) (b (cdr term)))
                 (:instance wbc-matrix-eval-of-matrix-scale
                            (n n) (m n) (c coefficient)
                            (matrix (wbc-outer (car term) (cdr term)))))
           :in-theory (e/d (wbc-term-output wbc-term-matrix)
                            (qcx qcx-add qcx-scale qcx-mul qcx-zero
                             wbc-linear wbc-outer wbc-matrix-scale
                             wbc-matrix-eval)))))

(defthm qcx-rationalp-of-wbc-term-matrix-eval
  (implies (and (consp term)
                (rational-rowp n (car term))
                (rational-rowp n (cdr term))
                (rationalp coefficient)
                (qcx-vectorp n xs)
                (qcx-vectorp n ys))
           (qcx-rationalp
            (wbc-matrix-eval (wbc-term-matrix term coefficient)
                             xs ys)))
  :hints (("Goal"
           :use ((:instance wbc-term-output-is-matrix-eval)
                 (:instance qcx-rationalp-of-wbc-term-output))
           :in-theory (enable qcx-vectorp rational-rowp))))

(defthm rational-matrixp-of-wbc-term-matrix
  (implies (and (consp term)
                (rational-rowp n (car term))
                (rational-rowp n (cdr term))
                (rationalp coefficient))
           (rational-matrixp n n
                             (wbc-term-matrix term coefficient)))
  :hints (("Goal"
           :use ((:instance rational-matrixp-of-outer
                            (a (car term)) (b (cdr term)))
                 (:instance rational-matrixp-of-matrix-scale
                            (m n) (matrix (wbc-outer (car term)
                                                    (cdr term)))
                            (c coefficient)))
           :in-theory (enable wbc-term-matrix))))

(defthm wbc-plan-validp-of-tail
  (implies (and (wbc-plan-validp n terms post)
                (consp (cdr terms)))
           (wbc-plan-validp n (cdr terms) (cdr post)))
  :hints (("Goal"
           :in-theory (enable wbc-plan-validp wbc-terms-validp))))

(defthm rational-matrixp-of-plan-matrix
  (implies (wbc-plan-validp n terms post)
           (rational-matrixp n n (wbc-plan-matrix terms post)))
  :hints (("Goal" :induct (wbc-plan-output terms post xs ys)
           :in-theory (enable wbc-plan-validp wbc-terms-validp
                              wbc-plan-matrix))))

(defthm wbc-plan-matrix-nonempty-implies-consp-terms
  (implies (wbc-plan-matrix terms post)
           (consp terms))
  :hints (("Goal" :in-theory (enable wbc-plan-matrix))))

(defthm wbc-plan-matrix-nonempty-implies-consp-post
  (implies (wbc-plan-matrix terms post)
           (consp post))
  :hints (("Goal" :in-theory (enable wbc-plan-matrix))))

(defthm qcx-add-zero-left-of-term-matrix-eval
  (implies (and (consp term)
                (rational-rowp n (car term))
                (rational-rowp n (cdr term))
                (rationalp coefficient)
                (qcx-vectorp n xs)
                (qcx-vectorp n ys))
           (equal (qcx-add '(0 . 0)
                           (wbc-matrix-eval
                            (wbc-term-matrix term coefficient) xs ys))
                  (wbc-matrix-eval
                   (wbc-term-matrix term coefficient) xs ys)))
  :hints (("Goal"
           :use ((:instance qcx-rationalp-of-wbc-term-matrix-eval)
                 (:instance qcx-add-left-identity
                            (x (wbc-matrix-eval
                                (wbc-term-matrix term coefficient)
                                xs ys))))
           :in-theory (enable qcx-zero qcx))))

(defthm wbc-matrix-eval-of-nil
  (equal (wbc-matrix-eval nil xs ys)
         (qcx-zero))
  :hints (("Goal" :in-theory (enable wbc-matrix-eval))))

(defthm wbc-matrix-eval-of-term-plus-plan
  (implies (and (posp n)
                (consp term)
                (rational-rowp n (car term))
                (rational-rowp n (cdr term))
                (rationalp coefficient)
                (consp terms)
                (wbc-terms-validp n terms)
                (rational-listp post)
                (equal (len terms) (len post))
                (qcx-vectorp n xs)
                (qcx-vectorp n ys))
           (equal
            (wbc-matrix-eval
             (wbc-matrix-add (wbc-term-matrix term coefficient)
                             (wbc-plan-matrix terms post))
             xs ys)
            (qcx-add
             (wbc-matrix-eval (wbc-term-matrix term coefficient) xs ys)
             (wbc-matrix-eval (wbc-plan-matrix terms post) xs ys))))
  :hints (("Goal"
           :use ((:instance rational-matrixp-of-wbc-term-matrix)
                 (:instance rational-matrixp-of-plan-matrix
                            (terms terms) (post post))
                 (:instance wbc-matrix-eval-of-matrix-add
                            (n n) (m n)
                            (a (wbc-term-matrix term coefficient))
                            (b (wbc-plan-matrix terms post))))
           :in-theory (enable wbc-plan-validp))))

(defthm wbc-plan-output-is-matrix-eval
  (implies (and (wbc-plan-validp n terms post)
                (qcx-vectorp n xs)
                (qcx-vectorp n ys))
           (equal (wbc-plan-output terms post xs ys)
                  (wbc-matrix-eval (wbc-plan-matrix terms post) xs ys)))
  :hints (("Goal"
           :induct (wbc-plan-output terms post xs ys)
           :in-theory (e/d (wbc-plan-output wbc-plan-matrix
                             wbc-plan-validp wbc-terms-validp)
                            (qcx qcx-add qcx-scale qcx-mul qcx-zero
                             qcx-vectorp rational-rowp rational-matrixp
                             wbc-term-output wbc-term-matrix
                             wbc-matrix-eval wbc-matrix-add
                             wbc-matrix-scale wbc-outer)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Cyclic convolution as a canonical bilinear coefficient matrix.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun wbc-delta-row-aux (count j i out n)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (if (equal (mod (+ (nfix i) (nfix j)) (nfix n))
                     (nfix out))
              1 0)
          (wbc-delta-row-aux (1- count) (1+ (nfix j)) i out n))))

(defun wbc-delta-matrix-aux (count i out n)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (wbc-delta-row-aux n 0 i out n)
          (wbc-delta-matrix-aux (1- count) (1+ (nfix i)) out n))))

(defun wbc-cyclic-matrix (n out)
  (wbc-delta-matrix-aux n 0 out n))

(defun wbc-cyclic-output (n out xs ys)
  (wbc-matrix-eval (wbc-cyclic-matrix n out) xs ys))

(defthm rational-rowp-of-delta-row-aux
  (rational-rowp count (wbc-delta-row-aux count j i out n))
  :hints (("Goal" :induct (wbc-delta-row-aux count j i out n)
           :in-theory (enable rational-rowp wbc-delta-row-aux))))

(defthm rational-matrixp-of-delta-matrix-aux
  (rational-matrixp count n
                    (wbc-delta-matrix-aux count i out n))
  :hints (("Goal"
           :induct (wbc-delta-matrix-aux count i out n)
           :in-theory (enable wbc-delta-matrix-aux
                              rational-matrixp))))

(defthm rational-matrixp-of-cyclic-matrix
  (rational-matrixp n n (wbc-cyclic-matrix n out))
  :hints (("Goal"
           :use ((:instance rational-matrixp-of-delta-matrix-aux
                            (count n) (i 0)))
           :in-theory (enable wbc-cyclic-matrix))))

(defun wbc-plan-certifies-outputp (n out terms post)
  (and (wbc-plan-validp n terms post)
       (equal (wbc-plan-matrix terms post)
              (wbc-cyclic-matrix n out))))

(defthm wbc-certified-plan-correct
  (implies (and (wbc-plan-certifies-outputp n out terms post)
                (qcx-vectorp n xs)
                (qcx-vectorp n ys))
           (equal (wbc-plan-output terms post xs ys)
                  (wbc-cyclic-output n out xs ys)))
  :hints (("Goal"
           :use ((:instance wbc-plan-output-is-matrix-eval))
           :in-theory (enable wbc-plan-certifies-outputp
                              wbc-cyclic-output))))

(defun wbc-plan-rank (terms) (len terms))
