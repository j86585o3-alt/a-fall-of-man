; A three-product Winograd plan for two-point cyclic convolution.
(in-package "ACL2")
(include-book "zao-winograd-bilinear-convolution")

; The three products are
;   m0 = (x0+x1)(y0+y1),  m1 = x0*y0,  m2 = x1*y1.
(defconst *wbc2-terms*
  (list (cons '(1 1) '(1 1))
        (cons '(1 0) '(1 0))
        (cons '(0 1) '(0 1))))

; z0 = m1+m2; z1 = m0-m1-m2.
(defconst *wbc2-post0* '(0 1 1))
(defconst *wbc2-post1* '(1 -1 -1))

(defthm wbc2-plan-valid-for-output0
  (wbc-plan-validp 2 *wbc2-terms* *wbc2-post0*)
  :hints (("Goal"
           :in-theory (enable wbc-plan-validp wbc-terms-validp
                              rational-rowp))))

(defthm wbc2-plan-valid-for-output1
  (wbc-plan-validp 2 *wbc2-terms* *wbc2-post1*)
  :hints (("Goal"
           :in-theory (enable wbc-plan-validp wbc-terms-validp
                              rational-rowp))))

(defthm wbc2-certifies-output0
  (wbc-plan-certifies-outputp 2 0 *wbc2-terms* *wbc2-post0*)
  :hints (("Goal"
           :in-theory (enable wbc-plan-certifies-outputp
                              wbc-plan-validp wbc-terms-validp
                              rational-rowp wbc-plan-matrix
                              wbc-term-matrix wbc-matrix-scale
                              wbc-outer wbc-row-scale wbc-matrix-add
                              wbc-row-add wbc-cyclic-matrix
                              wbc-delta-matrix-aux wbc-delta-row-aux))))

(defthm wbc2-certifies-output1
  (wbc-plan-certifies-outputp 2 1 *wbc2-terms* *wbc2-post1*)
  :hints (("Goal"
           :in-theory (enable wbc-plan-certifies-outputp
                              wbc-plan-validp wbc-terms-validp
                              rational-rowp wbc-plan-matrix
                              wbc-term-matrix wbc-matrix-scale
                              wbc-outer wbc-row-scale wbc-matrix-add
                              wbc-row-add wbc-cyclic-matrix
                              wbc-delta-matrix-aux wbc-delta-row-aux))))

(defthm wbc2-output0-correct
  (implies (and (qcx-vectorp 2 xs)
                (qcx-vectorp 2 ys))
           (equal (wbc-plan-output *wbc2-terms* *wbc2-post0* xs ys)
                  (wbc-cyclic-output 2 0 xs ys)))
  :hints (("Goal"
           :use ((:instance wbc-certified-plan-correct
                            (n 2) (out 0)
                            (terms *wbc2-terms*)
                            (post *wbc2-post0*))))))

(defthm wbc2-output1-correct
  (implies (and (qcx-vectorp 2 xs)
                (qcx-vectorp 2 ys))
           (equal (wbc-plan-output *wbc2-terms* *wbc2-post1* xs ys)
                  (wbc-cyclic-output 2 1 xs ys)))
  :hints (("Goal"
           :use ((:instance wbc-certified-plan-correct
                            (n 2) (out 1)
                            (terms *wbc2-terms*)
                            (post *wbc2-post1*))))))

(defthm wbc2-rank-is-three
  (equal (wbc-plan-rank *wbc2-terms*) 3)
  :hints (("Goal" :in-theory (enable wbc-plan-rank))))

(defthm wbc2-beats-naive-product-count
  (< (wbc-plan-rank *wbc2-terms*) (* 2 2))
  :hints (("Goal" :in-theory (enable wbc-plan-rank))))
