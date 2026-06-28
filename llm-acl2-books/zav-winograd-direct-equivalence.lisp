; Relate canonical bilinear Fourier matrices to the original rational-scalar-input DFT.
(in-package "ACL2")
(include-book "zar-rader-winograd-dft")
(include-book "zal-rational-fourier-kernel")

; Historical name: this only embeds each ACL2 rational x as (x . 0).
; It does not introduce an ACL2 real or a Lisp complex value.
(defun qcx-realify (xs)
  (if (endp xs)
      nil
    (cons (qcx (car xs) 0)
          (qcx-realify (cdr xs)))))

(defthm consp-of-qcx-realify
  (equal (consp (qcx-realify xs))
         (consp xs))
  :hints (("Goal" :in-theory (enable qcx-realify))))

(defthm car-of-qcx-realify
  (equal (car (qcx-realify xs))
         (if (consp xs)
             (qcx (car xs) 0)
           nil))
  :hints (("Goal" :in-theory (enable qcx-realify))))

(defthm cdr-of-qcx-realify
  (equal (cdr (qcx-realify xs))
         (qcx-realify (cdr xs)))
  :hints (("Goal" :in-theory (enable qcx-realify))))

(defthm len-of-qcx-realify
  (equal (len (qcx-realify xs)) (len xs))
  :hints (("Goal" :induct (qcx-realify xs))))

(defthm qcx-list-rationalp-of-realify
  (implies (rational-listp xs)
           (qcx-list-rationalp (qcx-realify xs)))
  :hints (("Goal"
           :induct (qcx-realify xs)
           :in-theory (enable qcx-realify qcx-list-rationalp
                              qcx-rationalp qcx qcx-re qcx-im))))

(defthm qcx-vectorp-of-realify
  (implies (and (rational-listp xs)
                (equal (len xs) (nfix n)))
           (qcx-vectorp n (qcx-realify xs)))
  :hints (("Goal"
           :in-theory (enable qcx-vectorp))))

(defthm rwd-fourier-row-is-unit-row-aux
  (equal (rwd-fourier-row-aux count j input-index output-index p)
         (rwd-unit-row-aux
          count j
          (mod (* (nfix input-index) (nfix output-index)) (nfix p))))
  :hints (("Goal"
           :induct (rwd-fourier-row-aux count j input-index output-index p)
           :in-theory (enable rwd-fourier-row-aux
                              rwd-unit-row-aux))))

(defthm qcx-mul-of-real-left
  (equal (qcx-mul (qcx x 0) z)
         (qcx-scale x z))
  :hints (("Goal"
           :in-theory (enable qcx-mul qcx-scale qcx qcx-re qcx-im))))

(defun rwd-unit-linear-induct (count index position table)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (endp table) (zp position))
      (list index)
    (rwd-unit-linear-induct (1- count) (1+ (nfix index))
                            (1- position) (cdr table))))

(defun rwd-unit-behind-induct (count index target table)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (endp table))
      (list index target)
    (rwd-unit-behind-induct (1- count) (1+ (nfix index))
                            target (cdr table))))

(defthm qcx-scale-of-zero-coefficient
  (equal (qcx-scale 0 z) (qcx-zero))
  :hints (("Goal"
           :in-theory (enable qcx-scale qcx-zero qcx qcx-re qcx-im))))

(defthm wbc-linear-of-unit-row-behind-index
  (implies (and (natp count)
                (natp index)
                (natp target)
                (< target index)
                (equal (len table) count)
                (qcx-list-rationalp table))
           (equal (wbc-linear
                   (rwd-unit-row-aux count index target)
                   table)
                  (qcx-zero)))
  :hints (("Goal"
           :induct (rwd-unit-behind-induct count index target table)
           :in-theory
           (e/d (rwd-unit-behind-induct rwd-unit-row-aux wbc-linear)
                (qcx qcx-add qcx-scale qcx-zero qcx-rationalp)))))

(defthm qcx-add-quoted-zero-left
  (implies (qcx-rationalp z)
           (equal (qcx-add '(0 . 0) z) z))
  :hints (("Goal"
           :use ((:instance qcx-add-left-identity (x z)))
           :in-theory (enable qcx-zero))))

(defthm qcx-add-zero-left-of-qcx-nth
  (implies (qcx-list-rationalp table)
           (equal (qcx-add '(0 . 0) (qcx-nth position table))
                  (qcx-nth position table)))
  :hints (("Goal"
           :use ((:instance qcx-rationalp-of-qcx-nth
                            (i position) (xs table))
                 (:instance qcx-add-quoted-zero-left
                            (z (qcx-nth position table))))
           :in-theory nil)))

(defthm wbc-linear-of-unit-row-at-index
  (implies (and (natp index)
                (consp table)
                (qcx-list-rationalp table))
           (equal (wbc-linear
                   (rwd-unit-row-aux (len table) index index)
                   table)
                  (car table)))
  :hints (("Goal"
           :use ((:instance wbc-linear-of-unit-row-behind-index
                            (count (len (cdr table)))
                            (index (1+ index))
                            (target index)
                            (table (cdr table))))
           :in-theory
           (e/d (rwd-unit-row-aux wbc-linear)
                (qcx qcx-add qcx-scale qcx-zero qcx-rationalp)))))

(defthm wbc-linear-of-shifted-unit-row
  (implies (and (natp count)
                (natp index)
                (natp position)
                (< position count)
                (equal (len table) count)
                (qcx-list-rationalp table))
           (equal
            (wbc-linear
             (rwd-unit-row-aux count index (+ index position))
             table)
            (qcx-nth position table)))
  :hints (("Goal"
           :induct (rwd-unit-linear-induct count index position table)
           :in-theory
           (e/d (rwd-unit-linear-induct
                 rwd-unit-row-aux wbc-linear qcx-nth)
                (qcx qcx-add qcx-scale qcx-zero qcx-rationalp)))))

(defthm wbc-linear-of-rwd-fourier-row
  (implies (and (posp p)
                (qcx-vectorp p table))
           (equal
            (wbc-linear
             (rwd-fourier-row-aux
              p 0 input-index output-index p)
             table)
            (qcx-nth
             (mod (* (nfix input-index) (nfix output-index)) (nfix p))
             table)))
  :hints (("Goal"
           :use ((:instance wbc-linear-of-shifted-unit-row
                            (count p)
                            (index 0)
                            (position
                             (mod (* (nfix input-index)
                                     (nfix output-index))
                                  (nfix p)))))
           :in-theory (enable qcx-vectorp))))

(defthm qcx-vectorp-implies-list-rationalp
  (implies (qcx-vectorp n table)
           (qcx-list-rationalp table))
  :hints (("Goal" :in-theory (enable qcx-vectorp))))

(defthm qcx-vectorp-implies-len
  (implies (qcx-vectorp n table)
           (equal (len table) (nfix n)))
  :hints (("Goal" :in-theory (enable qcx-vectorp))))

(defthm rational-rowp-implies-rational-listp
  (implies (rational-rowp n row)
           (rational-listp row))
  :hints (("Goal" :in-theory (enable rational-rowp))))

(defthm rational-rowp-implies-len
  (implies (rational-rowp n row)
           (equal (len row) (nfix n)))
  :hints (("Goal" :in-theory (enable rational-rowp))))

(defthm rwd-fourier-row-rational-rowp
  (rational-rowp
   p
   (rwd-fourier-row-aux p 0 input-index output-index p))
  :hints (("Goal"
           :use ((:instance rational-rowp-of-rwd-fourier-row-aux
                            (count p) (j 0))))))

(defthm wbc-row-eval-rwd-row-is-mul-linear
  (implies (and (qcx-vectorp p table)
                (rationalp x))
           (equal
            (wbc-row-eval
             (rwd-fourier-row-aux p 0 input-index output-index p)
             (qcx x 0)
             table)
            (qcx-mul
             (qcx x 0)
             (wbc-linear
              (rwd-fourier-row-aux p 0 input-index output-index p)
              table))))
  :hints (("Goal"
           :use ((:instance qcx-vectorp-implies-list-rationalp
                            (n p))
                 (:instance qcx-vectorp-implies-len (n p))
                 (:instance rwd-fourier-row-rational-rowp)
                 (:instance rational-rowp-implies-rational-listp
                            (n p)
                            (row (rwd-fourier-row-aux
                                  p 0 input-index output-index p)))
                 (:instance rational-rowp-implies-len
                            (n p)
                            (row (rwd-fourier-row-aux
                                  p 0 input-index output-index p)))
                 (:instance qcx-rationalp-of-qcx (re x) (im 0))
                 (:instance wbc-row-eval-is-mul-linear
                            (row (rwd-fourier-row-aux
                                  p 0 input-index output-index p))
                            (x (qcx x 0))
                            (ys table)))
           :in-theory nil)))

(defthm wbc-row-eval-of-rwd-fourier-row
  (implies (and (posp p)
                (rationalp x)
                (qcx-vectorp p table))
           (equal
            (wbc-row-eval
             (rwd-fourier-row-aux p 0 input-index output-index p)
             (qcx x 0)
             table)
            (qcx-scale
             x
             (qcx-nth
              (mod (* (nfix input-index) (nfix output-index)) (nfix p))
              table))))
  :hints (("Goal"
           :use ((:instance wbc-row-eval-rwd-row-is-mul-linear)
                 (:instance wbc-linear-of-rwd-fourier-row)
                 (:instance qcx-mul-of-real-left
                            (z (qcx-nth
                                (mod (* (nfix input-index)
                                        (nfix output-index))
                                     (nfix p))
                                table))))
           :in-theory nil)))

(defthm wbc-row-eval-of-rwd-fourier-row-by-table
  (implies (and (consp table)
                (qcx-list-rationalp table)
                (rationalp x))
           (equal
            (wbc-row-eval
             (rwd-fourier-row-aux (len table) 0
                                  input-index output-index (len table))
             (qcx x 0)
             table)
            (qcx-scale
             x
             (qcx-nth
              (mod (* (nfix input-index) (nfix output-index))
                   (len table))
              table))))
  :hints (("Goal"
           :use ((:instance wbc-row-eval-of-rwd-fourier-row
                            (p (len table))))
           :in-theory (enable qcx-vectorp posp))))

(defun rwd-matrix-dot-induct (count input-index xs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (list input-index xs)
    (rwd-matrix-dot-induct (1- count)
                           (1+ (nfix input-index))
                           (cdr xs))))

(defthm rwd-matrix-eval-aux-equals-qcx-dot
  (implies (and (posp p)
                (rational-listp xs)
                (equal (len xs) (nfix count))
                (qcx-vectorp p table))
           (equal
            (wbc-matrix-eval
             (rwd-fourier-matrix-aux count input-index output-index p)
             (qcx-realify xs)
             table)
            (qcx-dot
             xs
             (qcx-fourier-row-aux
              count input-index output-index p table))))
  :hints (("Goal"
           :induct (rwd-matrix-dot-induct count input-index xs)
           :in-theory
           (e/d (rwd-matrix-dot-induct
                 rwd-fourier-matrix-aux
                 qcx-realify qcx-dot qcx-fourier-row-aux
                 wbc-matrix-eval)
                (wbc-row-eval qcx qcx-add qcx-scale qcx-zero
                 rwd-fourier-row-is-unit-row-aux
                 wbc-row-eval-is-mul-linear)))))

(defthm rwd-direct-output-equals-original-direct-output
  (implies (and (posp p)
                (rational-listp xs)
                (equal (len xs) (nfix p))
                (qcx-vectorp p table))
           (equal
            (rwd-direct-output p output-index (qcx-realify xs) table)
            (qcx-direct-dft-output xs output-index table)))
  :hints (("Goal"
           :use ((:instance rwd-matrix-eval-aux-equals-qcx-dot
                            (count p) (input-index 0)))
           :in-theory (enable rwd-direct-output rwd-fourier-matrix
                              qcx-direct-dft-output qcx-fourier-row))))

(defthm rwd-direct-output-inherits-table-error-bound
  (implies (and (posp p)
                (rational-listp xs)
                (equal (len xs) (nfix p))
                (qcx-vectorp p a)
                (qcx-vectorp p b)
                (qcx-table-closep eps a b)
                (rationalp eps)
                (<= 0 eps))
           (<=
            (qcx-dist
             (rwd-direct-output p output-index (qcx-realify xs) a)
             (rwd-direct-output p output-index (qcx-realify xs) b))
            (* eps (rational-list-l1 xs))))
  :hints (("Goal"
           :use ((:instance qcx-direct-dft-output-error-bound
                            (k output-index)))
           :in-theory
           (disable qcx-direct-dft-output-error-bound)))
  :rule-classes :linear)
