(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)
(include-book "std/lists/top" :dir :system)

; Explicit rational complex pairs.  No ACL2 complex object is exposed.

(defun qcx (re im) (cons re im))
(defun qcx-re (z) (if (consp z) (car z) 0))
(defun qcx-im (z) (if (consp z) (cdr z) 0))
(defun qcx-rationalp (z)
  (and (consp z)
       (rationalp (car z))
       (rationalp (cdr z))))

(defun qcx-zero () (qcx 0 0))
(defun qcx-one () (qcx 1 0))

(defun qcx-add (x y)
  (qcx (+ (qcx-re x) (qcx-re y))
       (+ (qcx-im x) (qcx-im y))))

(defun qcx-neg (x)
  (qcx (- (qcx-re x))
       (- (qcx-im x))))

(defun qcx-sub (x y)
  (qcx-add x (qcx-neg y)))

(defun qcx-mul (x y)
  (qcx (- (* (qcx-re x) (qcx-re y))
          (* (qcx-im x) (qcx-im y)))
       (+ (* (qcx-re x) (qcx-im y))
          (* (qcx-im x) (qcx-re y)))))

(defun qcx-scale (a z)
  (qcx (* a (qcx-re z))
       (* a (qcx-im z))))

(defun qcx-l1 (z)
  (+ (abs (qcx-re z))
     (abs (qcx-im z))))

(defun qcx-dist (x y)
  (qcx-l1 (qcx-sub x y)))

(defthm qcx-re-of-qcx
  (equal (qcx-re (qcx re im)) re))

(defthm qcx-im-of-qcx
  (equal (qcx-im (qcx re im)) im))

(defthm qcx-rationalp-of-qcx
  (implies (and (rationalp re) (rationalp im))
           (qcx-rationalp (qcx re im))))

(defthm qcx-add-associative
  (equal (qcx-add (qcx-add x y) z)
         (qcx-add x (qcx-add y z))))

(defthm qcx-add-commutative
  (equal (qcx-add x y) (qcx-add y x)))

(defthm qcx-mul-distributes-over-add
  (equal (qcx-mul x (qcx-add y z))
         (qcx-add (qcx-mul x y)
                  (qcx-mul x z))))

(defthm qcx-l1-nonnegative
  (<= 0 (qcx-l1 z))
  :rule-classes :linear)

(defthm rationalp-of-qcx-dist
  (implies (and (qcx-rationalp x)
                (qcx-rationalp y))
           (rationalp (qcx-dist x y))))

(defthm qcx-dist-nonnegative
  (<= 0 (qcx-dist x y))
  :rule-classes :linear)

(defthm qcx-l1-of-scale
  (implies (rationalp a)
           (equal (qcx-l1 (qcx-scale a z))
                  (* (abs a) (qcx-l1 z))))
  :hints (("Goal" :in-theory (enable abs))))

(defthm qcx-dist-of-scale
  (implies (rationalp a)
           (equal (qcx-dist (qcx-scale a x)
                            (qcx-scale a y))
                  (* (abs a) (qcx-dist x y))))
  :hints (("Goal" :in-theory (enable abs))))

(defthm qcx-dist-of-add-upper-bound
  (implies (and (qcx-rationalp a)
                (qcx-rationalp b)
                (qcx-rationalp c)
                (qcx-rationalp d))
           (<= (qcx-dist (qcx-add a b)
                         (qcx-add c d))
               (+ (qcx-dist a c)
                  (qcx-dist b d))))
  :hints (("Goal" :in-theory (enable abs)))
  :rule-classes :linear)

(defthm qcx-rationalp-of-add
  (implies (and (qcx-rationalp x)
                (qcx-rationalp y))
           (qcx-rationalp (qcx-add x y))))

(defthm qcx-rationalp-of-scale
  (implies (and (rationalp a)
                (qcx-rationalp z))
           (qcx-rationalp (qcx-scale a z))))

(defun qcx-list-rationalp (xs)
  (if (endp xs)
      t
    (and (qcx-rationalp (car xs))
         (qcx-list-rationalp (cdr xs)))))

(defun qcx-table-closep (eps xs ys)
  (if (or (endp xs) (endp ys))
      (and (endp xs) (endp ys))
    (and (<= (qcx-dist (car xs) (car ys)) eps)
         (qcx-table-closep eps (cdr xs) (cdr ys)))))

(defun rational-list-l1 (xs)
  (if (endp xs)
      0
    (+ (abs (car xs))
       (rational-list-l1 (cdr xs)))))

(defthm rational-list-l1-nonnegative
  (<= 0 (rational-list-l1 xs))
  :rule-classes :linear)

(defun qcx-dot (xs ws)
  (if (or (endp xs) (endp ws))
      (qcx-zero)
    (qcx-add (qcx-scale (car xs) (car ws))
             (qcx-dot (cdr xs) (cdr ws)))))

(defthm qcx-rationalp-of-dot
  (implies (and (rational-listp xs)
                (qcx-list-rationalp ws)
                (equal (len xs) (len ws)))
           (qcx-rationalp (qcx-dot xs ws))))

(defthm abs-times-monotone
  (implies (and (rationalp x)
                (rationalp a)
                (rationalp b)
                (<= 0 a)
                (<= a b))
           (<= (* (abs x) a)
               (* (abs x) b)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defthm qcx-weighted-step-raw-bound
  (implies (and (rationalp x)
                (qcx-rationalp wa)
                (qcx-rationalp wb)
                (qcx-rationalp ra)
                (qcx-rationalp rb))
           (<= (qcx-dist (qcx-add (qcx-scale x wa) ra)
                         (qcx-add (qcx-scale x wb) rb))
               (+ (* (abs x) (qcx-dist wa wb))
                  (qcx-dist ra rb))))
  :hints (("Goal"
           :use ((:instance qcx-dist-of-add-upper-bound
                            (a (qcx-scale x wa))
                            (b ra)
                            (c (qcx-scale x wb))
                            (d rb))
                 (:instance qcx-dist-of-scale
                            (a x) (x wa) (y wb)))
           :in-theory (disable qcx-dist-of-add-upper-bound
                               qcx-dist-of-scale
                               qcx-dist
                               qcx-add
                               qcx-scale)))
  :rule-classes :linear)

(defthm qcx-weighted-step-error-bound
  (implies (and (rationalp x)
                (qcx-rationalp wa)
                (qcx-rationalp wb)
                (qcx-rationalp ra)
                (qcx-rationalp rb)
                (rationalp eps)
                (rationalp rest)
                (<= 0 eps)
                (<= 0 rest)
                (<= (qcx-dist wa wb) eps)
                (<= (qcx-dist ra rb) rest))
           (<= (qcx-dist (qcx-add (qcx-scale x wa) ra)
                         (qcx-add (qcx-scale x wb) rb))
               (+ (* (abs x) eps) rest)))
  :hints (("Goal"
           :use ((:instance qcx-weighted-step-raw-bound)
                 (:instance abs-times-monotone
                            (x x)
                            (a (qcx-dist wa wb))
                            (b eps)))
           :in-theory (disable qcx-weighted-step-raw-bound
                               abs-times-monotone
                               abs
                               qcx-dist
                               qcx-add
                               qcx-scale)))
  :rule-classes :linear)

(defun qcx-dot-induct (xs a b)
  (if (or (endp xs) (endp a) (endp b))
      (list xs a b)
    (qcx-dot-induct (cdr xs) (cdr a) (cdr b))))

(defthm equal-len-cdrs-on-conses
  (implies (and (equal (len x) (len y))
                (consp x)
                (consp y))
           (equal (len (cdr x)) (len (cdr y))))
  :rule-classes nil)

(defun qcx-dot-error-sum (xs a b)
  (if (or (endp xs) (endp a) (endp b))
      0
    (+ (* (abs (car xs))
          (qcx-dist (car a) (car b)))
       (qcx-dot-error-sum (cdr xs) (cdr a) (cdr b)))))

(defun qcx-dot2 (xs a b)
  (if (or (endp xs) (endp a) (endp b))
      (list (qcx-zero) (qcx-zero))
    (let ((rest (qcx-dot2 (cdr xs) (cdr a) (cdr b))))
      (list (qcx-add (qcx-scale (car xs) (car a)) (car rest))
            (qcx-add (qcx-scale (car xs) (car b)) (cadr rest))))))

(defthm qcx-rationalp-of-dot2-first
  (implies (and (rational-listp xs)
                (qcx-list-rationalp a)
                (qcx-list-rationalp b))
           (qcx-rationalp (car (qcx-dot2 xs a b)))))

(defthm qcx-rationalp-of-dot2-second
  (implies (and (rational-listp xs)
                (qcx-list-rationalp a)
                (qcx-list-rationalp b))
           (qcx-rationalp (cadr (qcx-dot2 xs a b)))))

(defthm qcx-dot2-distance-bounded-by-error-sum
  (implies (and (rational-listp xs)
                (qcx-list-rationalp a)
                (qcx-list-rationalp b))
           (<= (qcx-dist (car (qcx-dot2 xs a b))
                         (cadr (qcx-dot2 xs a b)))
               (qcx-dot-error-sum xs a b)))
  :hints (("Goal"
           :induct (qcx-dot2 xs a b)
           :in-theory (e/d (qcx-dot2
                            qcx-dot-error-sum
                            rational-listp
                            qcx-list-rationalp)
                           (qcx-dist
                            qcx-add
                            qcx-scale
                            qcx-dist-of-add-upper-bound
                            qcx-dist-of-scale))))
  :rule-classes :linear)

(defthm qcx-dot2-first-is-qcx-dot
  (implies (and (equal (len xs) (len a))
                (equal (len xs) (len b)))
           (equal (car (qcx-dot2 xs a b))
                  (qcx-dot xs a)))
  :hints (("Goal" :induct (qcx-dot2 xs a b))))

(defthm qcx-dot2-second-is-qcx-dot
  (implies (and (equal (len xs) (len a))
                (equal (len xs) (len b)))
           (equal (cadr (qcx-dot2 xs a b))
                  (qcx-dot xs b)))
  :hints (("Goal" :induct (qcx-dot2 xs a b))))

(defthm qcx-dot-distance-is-dot2-distance
  (implies (and (equal (len xs) (len a))
                (equal (len xs) (len b)))
           (equal (qcx-dist (qcx-dot xs a)
                            (qcx-dot xs b))
                  (qcx-dist (car (qcx-dot2 xs a b))
                            (cadr (qcx-dot2 xs a b)))))
  :hints (("Goal"
           :use ((:instance qcx-dot2-first-is-qcx-dot)
                 (:instance qcx-dot2-second-is-qcx-dot))
           :in-theory nil)))

(defthm qcx-dot-error-sum-uniform-bound
  (implies (and (rational-listp xs)
                (qcx-list-rationalp a)
                (qcx-list-rationalp b)
                (qcx-table-closep eps a b)
                (rationalp eps)
                (<= 0 eps))
           (<= (qcx-dot-error-sum xs a b)
               (* eps (rational-list-l1 xs))))
  :hints (("Goal"
           :induct (qcx-dot2 xs a b)
           :in-theory (e/d (qcx-dot2
                            qcx-dot-error-sum
                            qcx-table-closep
                            rational-list-l1
                            rational-listp
                            qcx-list-rationalp)
                           (abs
                            qcx-dist))))
  :rule-classes :linear)

(defthm qcx-dot-error-bound
  (implies (and (rational-listp xs)
                (qcx-list-rationalp a)
                (qcx-list-rationalp b)
                (equal (len xs) (len a))
                (equal (len xs) (len b))
                (qcx-table-closep eps a b)
                (rationalp eps)
                (<= 0 eps))
           (<= (qcx-dist (qcx-dot xs a)
                         (qcx-dot xs b))
               (* eps (rational-list-l1 xs))))
  :hints (("Goal"
           :use ((:instance qcx-dot-distance-is-dot2-distance)
                 (:instance qcx-dot2-distance-bounded-by-error-sum)
                 (:instance qcx-dot-error-sum-uniform-bound))
           :in-theory nil))
  :rule-classes :linear)

; A rational Fourier approximation is just a rational complex matrix.  The
; separate generator book will construct the rows from rational twiddles.

(defun qcx-matrix-rationalp (m)
  (if (endp m)
      t
    (and (qcx-list-rationalp (car m))
         (qcx-matrix-rationalp (cdr m)))))

(defun qcx-matrix-closep (eps a b)
  (if (or (endp a) (endp b))
      (and (endp a) (endp b))
    (and (qcx-table-closep eps (car a) (car b))
         (qcx-matrix-closep eps (cdr a) (cdr b)))))

(defun qcx-matrix-widthp (n m)
  (if (endp m)
      t
    (and (equal (len (car m)) n)
         (qcx-matrix-widthp n (cdr m)))))

(defun rational-dft-matrix (xs matrix)
  (if (endp matrix)
      nil
    (cons (qcx-dot xs (car matrix))
          (rational-dft-matrix xs (cdr matrix)))))

(defun dft-output-closep (eps xs ys)
  (if (or (endp xs) (endp ys))
      (and (endp xs) (endp ys))
    (and (<= (qcx-dist (car xs) (car ys)) eps)
         (dft-output-closep eps (cdr xs) (cdr ys)))))

(defun rational-dft-matrix-closep (bound xs a b)
  (if (or (endp a) (endp b))
      (and (endp a) (endp b))
    (and (<= (qcx-dist (qcx-dot xs (car a))
                       (qcx-dot xs (car b)))
             bound)
         (rational-dft-matrix-closep bound xs (cdr a) (cdr b)))))

(defun qcx-matrix-approx-p (n eps a b)
  (if (or (endp a) (endp b))
      (and (endp a) (endp b))
    (and (qcx-list-rationalp (car a))
         (qcx-list-rationalp (car b))
         (equal (len (car a)) n)
         (equal (len (car b)) n)
         (qcx-table-closep eps (car a) (car b))
         (qcx-matrix-approx-p n eps (cdr a) (cdr b)))))

