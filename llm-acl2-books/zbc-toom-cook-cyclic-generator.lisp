; Generated rational Toom-Cook plans for cyclic convolution.
(in-package "ACL2")
(include-book "zaq-winograd-bilinear-bank")
(include-book "arithmetic-5/top" :dir :system)

(defun tc-poly-add (a b)
  (cond ((endp a) b)
        ((endp b) a)
        (t (cons (+ (car a) (car b))
                 (tc-poly-add (cdr a) (cdr b))))))

(defun tc-poly-scale (c p)
  (if (endp p)
      nil
    (cons (* c (car p))
          (tc-poly-scale c (cdr p)))))

(defun tc-poly-mul-linear (p root)
  (tc-poly-add (tc-poly-scale (- root) p)
               (cons 0 p)))

(defun tc-lagrange-numerator-aux (count point omitted p)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      p
    (tc-lagrange-numerator-aux
     (1- count)
     (1+ (nfix point))
     omitted
     (if (equal (nfix point) (nfix omitted))
         p
       (tc-poly-mul-linear p (nfix point))))))

(defun tc-lagrange-denominator-aux (count point omitted acc)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      acc
    (tc-lagrange-denominator-aux
     (1- count)
     (1+ (nfix point))
     omitted
     (if (equal (nfix point) (nfix omitted))
         acc
       (* acc (- (nfix omitted) (nfix point)))))))

(defun tc-lagrange-row (m point)
  (let ((den (tc-lagrange-denominator-aux m 0 point 1)))
    (tc-poly-scale (/ den)
                   (tc-lagrange-numerator-aux m 0 point '(1)))))

(defun tc-powers-aux (count x power)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons power
          (tc-powers-aux (1- count) x (* x power)))))

(defun tc-evaluation-row (n point)
  (tc-powers-aux n point 1))

(defun tc-plan-terms-aux (count point n)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (let ((row (tc-evaluation-row n (nfix point))))
      (cons (cons row row)
            (tc-plan-terms-aux (1- count) (1+ (nfix point)) n)))))

(defun tc-plan-terms (n)
  (tc-plan-terms-aux (if (posp n) (1- (* 2 n)) 0) 0 n))

(defun tc-nth0 (k xs)
  (if (zp k)
      (if (consp xs) (car xs) 0)
    (tc-nth0 (1- k) (cdr xs))))

(defun tc-lagrange-bank-aux (count point m)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (tc-lagrange-row m (nfix point))
          (tc-lagrange-bank-aux (1- count) (1+ (nfix point)) m))))

(defun tc-lagrange-bank (m)
  (tc-lagrange-bank-aux m 0 m))

(defun tc-post-row-from-bank (n out bank)
  (if (endp bank)
      nil
    (cons (+ (tc-nth0 out (car bank))
             (tc-nth0 (+ (nfix out) (nfix n)) (car bank)))
          (tc-post-row-from-bank n out (cdr bank)))))

(defun tc-plan-posts-from-bank (count out n bank)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (tc-post-row-from-bank n (nfix out) bank)
          (tc-plan-posts-from-bank (1- count) (1+ (nfix out))
                                   n bank))))

(defun tc-post-row (n out)
  (let ((m (if (posp n) (1- (* 2 n)) 0)))
    (tc-post-row-from-bank n out (tc-lagrange-bank m))))

(defun tc-plan-posts (n)
  (let* ((m (if (posp n) (1- (* 2 n)) 0))
         (bank (tc-lagrange-bank m)))
    (tc-plan-posts-from-bank n 0 n bank)))

(defun tc-generated-plan-certifiesp (n)
  (wbc-bank-certifiesp n (tc-plan-terms n) (tc-plan-posts n)))

(defun tc-run (n xs ys)
  (wbc-bank-output (tc-plan-terms n) (tc-plan-posts n) xs ys))

(defthm len-of-tc-poly-scale
  (equal (len (tc-poly-scale c p)) (len p)))

(defthm rational-listp-of-tc-poly-scale
  (implies (and (rationalp c) (rational-listp p))
           (rational-listp (tc-poly-scale c p))))

(defthm len-of-tc-powers-aux
  (equal (len (tc-powers-aux count x power)) (nfix count)))

(defthm rational-listp-of-tc-powers-aux
  (implies (and (rationalp x) (rationalp power))
           (rational-listp (tc-powers-aux count x power))))

(defthm rational-rowp-of-tc-evaluation-row
  (implies (rationalp point)
           (rational-rowp n (tc-evaluation-row n point)))
  :hints (("Goal" :in-theory (enable rational-rowp tc-evaluation-row))))

(defthm len-of-tc-plan-terms-aux
  (equal (len (tc-plan-terms-aux count point n)) (nfix count)))

(defthm wbc-terms-validp-of-tc-plan-terms-aux
  (wbc-terms-validp n (tc-plan-terms-aux count point n)))

(defthm len-of-tc-plan-terms
  (equal (len (tc-plan-terms n))
         (if (posp n) (1- (* 2 n)) 0)))

(defthm tc-generated-rank
  (equal (wbc-bank-rank (tc-plan-terms n))
         (if (posp n) (1- (* 2 n)) 0))
  :hints (("Goal" :in-theory (enable wbc-bank-rank))))

(defun tc-row-moment-aux (post point degree acc)
  (if (endp post)
      acc
    (tc-row-moment-aux (cdr post)
                       (1+ (nfix point))
                       degree
                       (+ acc (* (car post)
                                 (expt (nfix point) (nfix degree)))))))

(defun tc-row-moment (post degree)
  (tc-row-moment-aux post 0 degree 0))

(defun tc-post-moments-okp-aux (count degree n out post)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and (equal (tc-row-moment post (nfix degree))
                (if (equal (mod (nfix degree) (nfix n))
                           (nfix out))
                    1 0))
         (tc-post-moments-okp-aux
          (1- count) (1+ (nfix degree)) n out post))))

(defun tc-post-moments-okp (n out post)
  (and (posp n)
       (tc-post-moments-okp-aux (1- (* 2 n)) 0 n out post)))

(defun tc-bank-moments-okp-aux (count out n posts)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (endp posts)
    (and (consp posts)
         (tc-post-moments-okp n (nfix out) (car posts))
         (tc-bank-moments-okp-aux
          (1- count) (1+ (nfix out)) n (cdr posts)))))

(defun tc-generated-moment-certificatep (n)
  (tc-bank-moments-okp-aux n 0 n (tc-plan-posts n)))

(defthm tc-positive-square
  (implies (and (rationalp x) (< 0 x))
           (< 0 (* x x))))

(defthm tc-generated-rank-beats-schoolbook
  (implies (and (integerp n) (< 1 n))
           (< (wbc-bank-rank (tc-plan-terms n)) (* n n)))
  :hints (("Goal"
           :use ((:instance tc-generated-rank)
                 (:instance tc-positive-square (x (- n 1))))
           :in-theory (disable tc-generated-rank tc-positive-square))))

(defthm tc-generated-plan-correct
  (implies (and (tc-generated-plan-certifiesp n)
                (qcx-vectorp n xs)
                (qcx-vectorp n ys))
           (equal (tc-run n xs ys)
                  (wbc-cyclic-convolution n xs ys)))
  :hints (("Goal"
           :use ((:instance wbc-certified-bank-correct
                            (terms (tc-plan-terms n))
                            (posts (tc-plan-posts n))))
           :in-theory (enable tc-generated-plan-certifiesp tc-run))))
