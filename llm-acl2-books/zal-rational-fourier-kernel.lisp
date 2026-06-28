; Rational Fourier kernel tables and arbitrary-size direct DFTs.

(in-package "ACL2")

(include-book "zak-rational-dft-core")
(include-book "arithmetic-5/top" :dir :system)

(defun qcx-nth (i xs)
  (declare (xargs :measure (nfix i)))
  (if (or (zp i) (endp xs))
      (if (endp xs) (qcx-zero) (car xs))
    (qcx-nth (1- i) (cdr xs))))

(defthm qcx-rationalp-of-qcx-nth
  (implies (qcx-list-rationalp xs)
           (qcx-rationalp (qcx-nth i xs)))
  :hints (("Goal"
           :induct (qcx-nth i xs)
           :in-theory (e/d (qcx-nth qcx-list-rationalp)
                           (qcx-rationalp)))))

(defun qcx-paired-nth (i a b)
  (declare (xargs :measure (nfix i)))
  (if (or (zp i) (endp a) (endp b))
      (cons (qcx-nth i a) (qcx-nth i b))
    (qcx-paired-nth (1- i) (cdr a) (cdr b))))

(defthm qcx-paired-nth-first
  (equal (car (qcx-paired-nth i a b))
         (qcx-nth i a))
  :hints (("Goal" :induct (qcx-paired-nth i a b))))

(defthm qcx-paired-nth-second
  (equal (cdr (qcx-paired-nth i a b))
         (qcx-nth i b))
  :hints (("Goal" :induct (qcx-paired-nth i a b))))

(defthm qcx-dist-zero-zero
  (equal (qcx-dist (qcx-zero) (qcx-zero)) 0))

(defthm qcx-paired-nth-close
  (implies (and (qcx-table-closep eps a b)
                (natp i)
                (rationalp eps)
                (<= 0 eps))
           (<= (qcx-dist (car (qcx-paired-nth i a b))
                          (cdr (qcx-paired-nth i a b)))
               eps))
  :hints (("Goal"
           :induct (qcx-paired-nth i a b)
           :in-theory (e/d (qcx-paired-nth qcx-nth qcx-table-closep)
                           (qcx-dist qcx-sub qcx-add qcx-neg
                            qcx-l1 qcx-re qcx-im))))
  :rule-classes :linear)

(defthm qcx-table-closep-of-qcx-nth
  (implies (and (qcx-table-closep eps a b)
                (natp i)
                (rationalp eps)
                (<= 0 eps))
           (<= (qcx-dist (qcx-nth i a) (qcx-nth i b)) eps))
  :hints (("Goal"
           :use ((:instance qcx-paired-nth-close)
                 (:instance qcx-paired-nth-first)
                 (:instance qcx-paired-nth-second))
           :in-theory nil))
  :rule-classes :linear)

(defun qcx-fourier-row-aux (count j k n table)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (qcx-nth (mod (* (nfix j) (nfix k)) (nfix n)) table)
          (qcx-fourier-row-aux (1- count) (1+ (nfix j)) k n table))))

(defun qcx-fourier-row (k n table)
  (qcx-fourier-row-aux n 0 k n table))

(defthm len-of-qcx-fourier-row-aux
  (equal (len (qcx-fourier-row-aux count j k n table))
         (nfix count))
  :hints (("Goal" :induct (qcx-fourier-row-aux count j k n table))))

(defthm len-of-qcx-fourier-row
  (equal (len (qcx-fourier-row k n table))
         (nfix n)))

(defthm qcx-list-rationalp-of-fourier-row-aux
  (implies (qcx-list-rationalp table)
           (qcx-list-rationalp
            (qcx-fourier-row-aux count j k n table)))
  :hints (("Goal"
           :induct (qcx-fourier-row-aux count j k n table)
           :in-theory (e/d (qcx-fourier-row-aux qcx-list-rationalp)
                           (qcx-rationalp)))))

(defthm qcx-list-rationalp-of-fourier-row
  (implies (qcx-list-rationalp table)
           (qcx-list-rationalp (qcx-fourier-row k n table))))

(defthm natp-of-mod-of-nats
  (implies (and (natp x) (natp n))
           (natp (mod x n))))

(defthm qcx-table-closep-of-fourier-row-aux
  (implies (and (qcx-table-closep eps a b)
                (rationalp eps)
                (<= 0 eps))
           (qcx-table-closep
            eps
            (qcx-fourier-row-aux count j k n a)
            (qcx-fourier-row-aux count j k n b)))
  :hints (("Goal"
           :induct (qcx-fourier-row-aux count j k n a)
           :in-theory (e/d (qcx-fourier-row-aux qcx-table-closep)
                           (qcx-dist)))))

(defthm qcx-table-closep-of-fourier-row
  (implies (and (qcx-table-closep eps a b)
                (rationalp eps)
                (<= 0 eps))
           (qcx-table-closep
            eps
            (qcx-fourier-row k n a)
            (qcx-fourier-row k n b))))

(defun qcx-direct-dft-output (xs k table)
  (qcx-dot xs (qcx-fourier-row k (len xs) table)))

(defthm qcx-direct-dft-output-error-bound
  (implies (and (rational-listp xs)
                (qcx-list-rationalp a)
                (qcx-list-rationalp b)
                (qcx-table-closep eps a b)
                (rationalp eps)
                (<= 0 eps))
           (<= (qcx-dist (qcx-direct-dft-output xs k a)
                          (qcx-direct-dft-output xs k b))
               (* eps (rational-list-l1 xs))))
  :hints (("Goal"
           :use ((:instance qcx-dot-error-bound
                            (a (qcx-fourier-row k (len xs) a))
                            (b (qcx-fourier-row k (len xs) b))))
           :in-theory (enable qcx-direct-dft-output)))
  :rule-classes :linear)

(defun qcx-direct-dft-aux (count k xs table)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (qcx-direct-dft-output xs k table)
          (qcx-direct-dft-aux (1- count) (1+ (nfix k)) xs table))))

(defun qcx-direct-dft (xs table)
  (qcx-direct-dft-aux (len xs) 0 xs table))

(defthm len-of-qcx-direct-dft-aux
  (equal (len (qcx-direct-dft-aux count k xs table))
         (nfix count))
  :hints (("Goal" :induct (qcx-direct-dft-aux count k xs table))))

(defthm len-of-qcx-direct-dft
  (equal (len (qcx-direct-dft xs table))
         (len xs)))

