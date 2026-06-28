; Shared-product banks for certified Winograd cyclic convolutions.
(in-package "ACL2")
(include-book "zao-winograd-bilinear-convolution")

(defun wbc-product-bank (terms xs ys)
  (if (endp terms)
      nil
    (cons (qcx-mul (wbc-linear (caar terms) xs)
                   (wbc-linear (cdar terms) ys))
          (wbc-product-bank (cdr terms) xs ys))))

(defun wbc-post-output (post products)
  (wbc-linear post products))

(defthm wbc-post-output-of-product-bank
  (equal (wbc-post-output post (wbc-product-bank terms xs ys))
         (wbc-plan-output terms post xs ys))
  :hints (("Goal"
           :induct (wbc-plan-output terms post xs ys)
           :in-theory (enable wbc-post-output wbc-product-bank
                              wbc-plan-output wbc-term-output
                              wbc-linear))))

(defun wbc-post-bank-output (posts products)
  (if (endp posts)
      nil
    (cons (wbc-post-output (car posts) products)
          (wbc-post-bank-output (cdr posts) products))))

(defun wbc-bank-output (terms posts xs ys)
  (wbc-post-bank-output posts (wbc-product-bank terms xs ys)))

(defun wbc-cyclic-convolution-aux (count out n xs ys)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (wbc-cyclic-output n out xs ys)
          (wbc-cyclic-convolution-aux (1- count) (1+ (nfix out))
                                      n xs ys))))

(defun wbc-cyclic-convolution (n xs ys)
  (wbc-cyclic-convolution-aux n 0 n xs ys))

(defun wbc-bank-certifies-aux (count out n terms posts)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (endp posts)
    (and (consp posts)
         (wbc-plan-certifies-outputp n out terms (car posts))
         (wbc-bank-certifies-aux (1- count) (1+ (nfix out))
                                 n terms (cdr posts)))))

(defun wbc-bank-certifiesp (n terms posts)
  (wbc-bank-certifies-aux n 0 n terms posts))

(defthm len-of-wbc-product-bank
  (equal (len (wbc-product-bank terms xs ys))
         (len terms))
  :hints (("Goal" :induct (wbc-product-bank terms xs ys))))

(defthm len-of-wbc-post-bank-output
  (equal (len (wbc-post-bank-output posts products))
         (len posts))
  :hints (("Goal" :induct (wbc-post-bank-output posts products))))

(defthm wbc-certified-bank-head-correct
  (implies (and (wbc-plan-certifies-outputp n out terms post)
                (qcx-vectorp n xs)
                (qcx-vectorp n ys))
           (equal (wbc-post-output post
                                   (wbc-product-bank terms xs ys))
                  (wbc-cyclic-output n out xs ys)))
  :hints (("Goal"
           :use ((:instance wbc-post-output-of-product-bank)
                 (:instance wbc-certified-plan-correct))
           :in-theory nil)))

(defthm wbc-bank-certifies-aux-correct
  (implies (and (wbc-bank-certifies-aux count out n terms posts)
                (qcx-vectorp n xs)
                (qcx-vectorp n ys))
           (equal (wbc-post-bank-output
                   posts (wbc-product-bank terms xs ys))
                  (wbc-cyclic-convolution-aux count out n xs ys)))
  :hints (("Goal"
           :induct (wbc-bank-certifies-aux count out n terms posts)
           :in-theory
           (e/d (wbc-bank-certifies-aux
                 wbc-post-bank-output
                 wbc-cyclic-convolution-aux)
                (wbc-plan-certifies-outputp
                 wbc-plan-validp
                 qcx-vectorp
                 wbc-post-output
                 wbc-product-bank
                 wbc-cyclic-output)))))

(defthm wbc-certified-bank-correct
  (implies (and (wbc-bank-certifiesp n terms posts)
                (qcx-vectorp n xs)
                (qcx-vectorp n ys))
           (equal (wbc-bank-output terms posts xs ys)
                  (wbc-cyclic-convolution n xs ys)))
  :hints (("Goal"
           :use ((:instance wbc-bank-certifies-aux-correct
                            (count n) (out 0)))
           :in-theory (enable wbc-bank-certifiesp wbc-bank-output
                              wbc-cyclic-convolution))))

(defun wbc-bank-rank (terms)
  (len terms))
