; Extensional Rader output certificates from scalar Fourier entries.
(in-package "ACL2")
(include-book "zbi-rader-compact-output-bridge")

(defun rom-forward-nth-induct (count index position)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (zp position))
      (list count index position)
    (rom-forward-nth-induct
     (1- count) (1+ (nfix index)) (1- position))))

(defthm rom-zero-plus-natural
  (implies (natp x)
           (equal (+ 0 x) x)))

(defthm rom-natp-zero
  (natp 0))

(defthm rom-nfix-when-natp
  (implies (natp x)
           (equal (nfix x) x))
  :hints (("Goal" :in-theory (enable nfix natp))))

(defthm rom-natp-of-successor
  (implies (natp x)
           (natp (1+ (nfix x))))
  :hints (("Goal" :in-theory (enable nfix natp))))

(defthm rom-natp-of-one-plus
  (implies (natp x)
           (natp (1+ x)))
  :hints (("Goal" :in-theory (enable natp))))

(defthm rom-natp-of-predecessor
  (implies (and (natp x) (not (zp x)))
           (natp (1- x)))
  :hints (("Goal" :in-theory (enable zp natp))))

(defthm rom-forward-sum
  (implies (and (natp index)
                (natp position)
                (not (zp position)))
           (equal (+ (1+ (nfix index)) (1- position))
                  (+ index position)))
  :hints (("Goal" :in-theory (enable nfix zp natp))))

(defthm rom-bound-implies-not-zp-count
  (implies (and (natp position)
                (< position (nfix count)))
           (not (zp count)))
  :hints (("Goal" :in-theory (enable zp nfix natp))))

(defthm rom-sum-when-zp-natural
  (implies (and (natp index)
                (zp position) (natp position))
           (equal (+ index position) index))
  :hints (("Goal" :in-theory (enable zp natp))))

(defthm rom-forward-sum-normalized
  (implies (and (natp index) (natp position))
           (equal (+ (+ 1 index) -1 position)
                  (+ index position))))

(defthm rom-predecessor-bound
  (implies (and (natp position)
                (not (zp position))
                (< position (nfix count)))
           (< (1- position) (nfix (1- count))))
  :hints (("Goal"
           :use ((:instance rcb-nfix-of-predecessor))
           :in-theory (enable zp nfix natp))))

(defthm rom-consp-of-fourier-row-aux
  (implies (not (zp count))
           (consp (rwd-fourier-row-aux
                   count j input-index output-index p)))
  :hints (("Goal"
           :expand ((rwd-fourier-row-aux
                     count j input-index output-index p))
           :in-theory '(car-cons cdr-cons consp))))

(defthm rom-car-of-fourier-row-aux
  (implies (not (zp count))
           (equal
            (car (rwd-fourier-row-aux
                  count j input-index output-index p))
            (if (equal (nfix j)
                       (mod (* (nfix input-index)
                               (nfix output-index))
                            (nfix p)))
                1 0)))
  :hints (("Goal"
           :expand ((rwd-fourier-row-aux
                     count j input-index output-index p))
           :in-theory '(car-cons cdr-cons consp))))

(defthm rom-cdr-of-fourier-row-aux
  (implies (not (zp count))
           (equal
            (cdr (rwd-fourier-row-aux
                  count j input-index output-index p))
            (rwd-fourier-row-aux
             (1- count) (1+ (nfix j))
             input-index output-index p)))
  :hints (("Goal"
           :expand ((rwd-fourier-row-aux
                     count j input-index output-index p))
           :in-theory '(car-cons cdr-cons consp))))

(defthm rom-nth0-of-fourier-row-aux
  (implies (and (posp p)
                (natp input-index)
                (natp output-index)
                (natp j)
                (natp column)
                (< column (nfix count)))
           (equal
            (tc-nth0 column
                     (rwd-fourier-row-aux
                      count j input-index output-index p))
            (if (equal (+ j column)
                       (mod (* input-index output-index) p))
                1 0)))
  :hints
  (("Goal"
    :induct (rom-forward-nth-induct count j column)
    :in-theory '(rom-forward-nth-induct
                 tc-nth0
                 rom-consp-of-fourier-row-aux
                 rom-car-of-fourier-row-aux
                 rom-cdr-of-fourier-row-aux
                 rcb-nfix-of-predecessor
                 rcb-zp-no-bounded-nat
                 rom-nfix-when-natp
                 rom-natp-of-successor
                 rom-natp-of-one-plus
                 rom-natp-of-predecessor
                 rom-forward-sum
                 rom-forward-sum-normalized
                 rom-predecessor-bound
                 rom-bound-implies-not-zp-count
                 rom-sum-when-zp-natural
                 rgi-nfix-when-posp))))

(defthm rom-consp-of-fourier-matrix-aux
  (implies (not (zp count))
           (consp (rwd-fourier-matrix-aux
                   count input-index output-index p)))
  :hints (("Goal"
           :expand ((rwd-fourier-matrix-aux
                     count input-index output-index p))
           :in-theory '(car-cons cdr-cons consp))))

(defthm rom-car-of-fourier-matrix-aux
  (implies (not (zp count))
           (equal
            (car (rwd-fourier-matrix-aux
                  count input-index output-index p))
            (rwd-fourier-row-aux
             p 0 input-index output-index p)))
  :hints (("Goal"
           :expand ((rwd-fourier-matrix-aux
                     count input-index output-index p))
           :in-theory '(car-cons cdr-cons consp))))

(defthm rom-cdr-of-fourier-matrix-aux
  (implies (not (zp count))
           (equal
            (cdr (rwd-fourier-matrix-aux
                  count input-index output-index p))
            (rwd-fourier-matrix-aux
             (1- count) (1+ (nfix input-index))
             output-index p)))
  :hints (("Goal"
           :expand ((rwd-fourier-matrix-aux
                     count input-index output-index p))
           :in-theory '(car-cons cdr-cons consp))))

(defthm rom-nth0-of-fourier-matrix-aux
  (implies (and (posp p)
                (natp input-index)
                (natp output-index)
                (natp row)
                (< row (nfix count)))
           (equal
            (tc-nth0 row
                     (rwd-fourier-matrix-aux
                      count input-index output-index p))
            (rwd-fourier-row-aux
             p 0 (+ input-index row) output-index p)))
  :hints
  (("Goal"
    :induct (rom-forward-nth-induct count input-index row)
    :in-theory '(rom-forward-nth-induct
                 tc-nth0
                 rom-consp-of-fourier-matrix-aux
                 rom-car-of-fourier-matrix-aux
                 rom-cdr-of-fourier-matrix-aux
                 rcb-nfix-of-predecessor
                 rcb-zp-no-bounded-nat
                 rom-nfix-when-natp
                 rom-natp-of-successor
                 rom-natp-of-one-plus
                 rom-natp-of-predecessor
                 rom-forward-sum
                 rom-forward-sum-normalized
                 rom-predecessor-bound
                 rom-bound-implies-not-zp-count
                 rom-sum-when-zp-natural
                 rgi-nfix-when-posp))))

(defthm rom-nth0-entry-of-fourier-matrix
  (implies (and (posp p)
                (natp output)
                (natp row) (< row p)
                (natp column) (< column p))
           (equal
            (tc-nth0 column
                     (tc-nth0 row
                              (rwd-fourier-matrix p output)))
            (if (equal column (mod (* row output) p)) 1 0)))
  :hints
  (("Goal"
    :use ((:instance rom-nth0-of-fourier-matrix-aux
                     (count p) (input-index 0)
                     (output-index output))
          (:instance rom-nth0-of-fourier-row-aux
                     (count p) (j 0)
                     (input-index row)
                     (output-index output)))
    :in-theory '(rwd-fourier-matrix
                 rom-natp-zero
                 rom-zero-plus-natural
                 rom-nfix-when-natp
                 rgi-nfix-when-posp))))

(defthm rom-entry-of-fourier-matrix
  (implies (and (posp p)
                (natp output)
                (natp row) (< row p)
                (natp column) (< column p))
           (equal
            (tc-matrix-entry row column
                             (rwd-fourier-matrix p output))
            (rgi-fourier-entry p output row column)))
  :hints
  (("Goal"
    :use ((:instance rom-nth0-entry-of-fourier-matrix))
    :in-theory '(tc-matrix-entry rgi-fourier-entry
                 rom-nfix-when-natp
                 rgi-nfix-when-posp))))

(defthm rom-nth0-fourier-entry
  (implies (and (posp p)
                (natp output)
                (natp row) (< row p)
                (natp column) (< column p))
           (equal
            (tc-nth0 column
                     (tc-nth0 row
                              (rwd-fourier-matrix p output)))
            (rgi-fourier-entry p output row column)))
  :hints (("Goal"
           :use ((:instance rom-entry-of-fourier-matrix))
           :in-theory '(tc-matrix-entry))))

(defthm rom-rational-matrixp-of-full-plan
  (implies
   (and (tc-compact-post-certifiesp
         (1- (nfix p)) small-out post)
        (posp p))
   (rational-matrixp
    p p
    (wbc-plan-matrix
     (rwd-full-terms
      p inputs kernels (tc-plan-terms (1- (nfix p))))
     (rwd-nonzero-post post))))
  :hints
  (("Goal"
    :use ((:instance rgi-nonzero-full-plan-validp
                     (n (1- (nfix p)))
                     (out small-out))
          (:instance rational-matrixp-of-plan-matrix
                     (n p)
                     (terms
                      (rwd-full-terms
                       p inputs kernels
                       (tc-plan-terms (1- (nfix p)))))
                     (post (rwd-nonzero-post post))))
    :in-theory nil)))

(defun rom-proper-matrixp (matrix)
  (if (consp matrix)
      (and (true-listp (car matrix))
           (rom-proper-matrixp (cdr matrix)))
    (equal matrix nil)))

(defthm rom-true-listp-of-wbc-row-add
  (true-listp (wbc-row-add a b))
  :hints (("Goal" :induct (wbc-row-add a b)
           :in-theory (enable wbc-row-add))))

(defthm rom-true-listp-of-wbc-row-scale
  (true-listp (wbc-row-scale c row))
  :hints (("Goal" :induct (wbc-row-scale c row)
           :in-theory (enable wbc-row-scale))))

(defthm rom-proper-matrixp-of-wbc-outer
  (rom-proper-matrixp (wbc-outer a b))
  :hints (("Goal" :induct (wbc-outer a b)
           :in-theory (enable wbc-outer rom-proper-matrixp))))

(defthm rom-proper-matrixp-of-wbc-matrix-scale
  (rom-proper-matrixp (wbc-matrix-scale c matrix))
  :hints (("Goal" :induct (wbc-matrix-scale c matrix)
           :in-theory (enable wbc-matrix-scale rom-proper-matrixp))))

(defthm rom-proper-matrixp-of-wbc-matrix-add
  (rom-proper-matrixp (wbc-matrix-add a b))
  :hints (("Goal" :induct (wbc-matrix-add a b)
           :in-theory (enable wbc-matrix-add rom-proper-matrixp))))

(defthm rom-proper-matrixp-of-wbc-term-matrix
  (rom-proper-matrixp (wbc-term-matrix term coefficient))
  :hints (("Goal"
           :use ((:instance rom-proper-matrixp-of-wbc-outer
                            (a (car term)) (b (cdr term)))
                 (:instance rom-proper-matrixp-of-wbc-matrix-scale
                            (c coefficient)
                            (matrix (wbc-outer (car term) (cdr term)))))
           :in-theory '(wbc-term-matrix))))

(defthm rom-proper-matrixp-of-wbc-plan-matrix
  (rom-proper-matrixp (wbc-plan-matrix terms post))
  :hints (("Goal" :induct (wbc-plan-matrix terms post)
           :in-theory (enable wbc-plan-matrix rom-proper-matrixp))))

(defthm rom-true-listp-of-fourier-row-aux
  (true-listp
   (rwd-fourier-row-aux count j input-index output-index p))
  :hints (("Goal"
           :induct (rwd-fourier-row-aux
                    count j input-index output-index p)
           :in-theory (enable rwd-fourier-row-aux))))

(defthm rom-proper-matrixp-of-fourier-matrix-aux
  (rom-proper-matrixp
   (rwd-fourier-matrix-aux count input-index output-index p))
  :hints (("Goal"
           :induct (rwd-fourier-matrix-aux
                    count input-index output-index p)
           :in-theory (enable rwd-fourier-matrix-aux
                              rom-proper-matrixp))))

(defthm rom-proper-matrixp-of-fourier-matrix
  (rom-proper-matrixp (rwd-fourier-matrix p output))
  :hints (("Goal"
           :use ((:instance rom-proper-matrixp-of-fourier-matrix-aux
                            (count p) (input-index 0)
                            (output-index output)))
           :in-theory '(rwd-fourier-matrix))))

(defthm rom-proper-matrixp-car
  (implies (and (rom-proper-matrixp matrix)
                (consp matrix))
           (true-listp (car matrix)))
  :hints (("Goal"
           :expand ((rom-proper-matrixp matrix))
           :in-theory nil)))

(defthm rom-proper-matrixp-cdr
  (implies (and (rom-proper-matrixp matrix)
                (consp matrix))
           (rom-proper-matrixp (cdr matrix)))
  :hints (("Goal"
           :expand ((rom-proper-matrixp matrix))
           :in-theory nil)))

(defthm rom-positive-index-bound-implies-consp
  (implies (and (natp row)
                (< row (len matrix)))
           (consp matrix))
  :hints (("Goal" :in-theory (enable len natp))))

(defthm rom-cdr-index-bound
  (implies (and (consp matrix)
                (natp row)
                (not (zp row))
                (< row (len matrix)))
           (< (1- row) (len (cdr matrix))))
  :hints (("Goal"
           :expand ((len matrix))
           :in-theory '(zp natp))))

(defun rom-nth-induct (row matrix)
  (declare (xargs :measure (nfix row)))
  (if (or (zp row) (endp matrix))
      (list row matrix)
    (rom-nth-induct (1- row) (cdr matrix))))

(defthm rom-true-listp-of-nth-proper-matrix
  (implies (and (rom-proper-matrixp matrix)
                (natp row)
                (< row (len matrix)))
           (true-listp (nth row matrix)))
  :hints
  (("Goal"
    :induct (rom-nth-induct row matrix)
    :in-theory '(rom-nth-induct nth
                 rom-proper-matrixp-car
                 rom-proper-matrixp-cdr
                 rom-positive-index-bound-implies-consp
                 rom-cdr-index-bound
                 rom-natp-of-predecessor))))

(defthm rom-true-listp-of-proper-matrix-row
  (implies (and (rom-proper-matrixp matrix)
                (natp row)
                (< row (len matrix)))
           (true-listp (tc-nth0 row matrix)))
  :hints (("Goal"
           :use ((:instance rom-true-listp-of-nth-proper-matrix)
                 (:instance tc-nth0-is-nth-when-in-bounds
                            (k row) (xs matrix)))
           :in-theory nil)))

(defthm rom-full-plan-row-length
  (implies
   (and (tc-compact-post-certifiesp
         (1- (nfix p)) small-out post)
        (posp p)
        (natp row) (< row p))
   (equal
    (len
     (tc-nth0
      row
      (wbc-plan-matrix
       (rwd-full-terms
        p inputs kernels (tc-plan-terms (1- (nfix p))))
       (rwd-nonzero-post post))))
    p))
  :hints
  (("Goal"
    :use ((:instance rom-rational-matrixp-of-full-plan)
          (:instance len-of-tc-nth0-of-rational-matrixp
                     (rows p) (cols p)
                     (matrix
                      (wbc-plan-matrix
                       (rwd-full-terms
                        p inputs kernels
                        (tc-plan-terms (1- (nfix p))))
                       (rwd-nonzero-post post)))))
    :in-theory '(rgi-nfix-when-posp))))

(defthm rom-fourier-row-length
  (implies (and (posp p)
                (natp row) (< row p))
           (equal
            (len (tc-nth0 row (rwd-fourier-matrix p output)))
            p))
  :hints
  (("Goal"
    :use ((:instance rational-matrixp-of-rwd-fourier-matrix
                     (output-index output))
          (:instance len-of-tc-nth0-of-rational-matrixp
                     (rows p) (cols p)
                     (matrix (rwd-fourier-matrix p output))))
    :in-theory '(rgi-nfix-when-posp))))

(defthm rom-full-plan-row-true-listp
  (implies
   (and (tc-compact-post-certifiesp
         (1- (nfix p)) small-out post)
        (posp p)
        (natp row) (< row p))
   (true-listp
    (tc-nth0
     row
     (wbc-plan-matrix
      (rwd-full-terms
       p inputs kernels (tc-plan-terms (1- (nfix p))))
      (rwd-nonzero-post post)))))
  :hints
  (("Goal"
    :use ((:instance rom-proper-matrixp-of-wbc-plan-matrix
                     (terms
                      (rwd-full-terms
                       p inputs kernels
                       (tc-plan-terms (1- (nfix p)))))
                     (post (rwd-nonzero-post post)))
          (:instance rom-true-listp-of-proper-matrix-row
                     (matrix
                      (wbc-plan-matrix
                       (rwd-full-terms
                        p inputs kernels
                        (tc-plan-terms (1- (nfix p))))
                       (rwd-nonzero-post post))))
          (:instance tc-len-of-rational-matrixp
                     (rows p) (cols p)
                     (matrix
                      (wbc-plan-matrix
                       (rwd-full-terms
                        p inputs kernels
                        (tc-plan-terms (1- (nfix p))))
                       (rwd-nonzero-post post))))
          (:instance rom-rational-matrixp-of-full-plan))
    :in-theory '(rgi-nfix-when-posp))))

(defthm rom-fourier-row-true-listp
  (implies (and (posp p)
                (natp row) (< row p))
           (true-listp
            (tc-nth0 row (rwd-fourier-matrix p output))))
  :hints
  (("Goal"
    :use ((:instance rom-proper-matrixp-of-fourier-matrix)
          (:instance rom-true-listp-of-proper-matrix-row
                     (matrix (rwd-fourier-matrix p output)))
          (:instance tc-len-of-rational-matrixp
                     (rows p) (cols p)
                     (matrix (rwd-fourier-matrix p output)))
          (:instance rational-matrixp-of-rwd-fourier-matrix
                     (output-index output)))
    :in-theory '(rgi-nfix-when-posp))))

(defthm rom-nth0-entry-of-full-plan
  (implies
   (and (tc-compact-post-certifiesp
         (1- (nfix p)) small-out post)
        (rgi-compact-outputp
         p small-out output inputs kernels)
        (natp small-out)
        (posp p)
        (natp row) (< row p)
        (natp column) (< column p))
   (equal
    (tc-nth0
     column
     (tc-nth0
      row
      (wbc-plan-matrix
       (rwd-full-terms
        p inputs kernels (tc-plan-terms (1- (nfix p))))
       (rwd-nonzero-post post))))
    (rgi-fourier-entry p output row column)))
  :hints
  (("Goal"
    :use ((:instance rcb-full-nonzero-fourier-entry))
    :in-theory '(tc-matrix-entry))))

(defthm rom-nth-of-full-plan-row-equals-fourier
  (implies
   (and (tc-compact-post-certifiesp
         (1- (nfix p)) small-out post)
        (rgi-compact-outputp
         p small-out output inputs kernels)
        (natp small-out)
        (natp output)
        (posp p)
        (natp row) (< row p)
        (natp column) (< column p))
   (equal
    (nth
     column
     (tc-nth0
      row
      (wbc-plan-matrix
       (rwd-full-terms
        p inputs kernels (tc-plan-terms (1- (nfix p))))
       (rwd-nonzero-post post))))
    (nth column
         (tc-nth0 row (rwd-fourier-matrix p output)))))
  :hints
  (("Goal"
    :use
    ((:instance tc-equality-chain-5
                (a (nth
                    column
                    (tc-nth0
                     row
                     (wbc-plan-matrix
                      (rwd-full-terms
                       p inputs kernels
                       (tc-plan-terms (1- (nfix p))))
                      (rwd-nonzero-post post)))))
                (b (tc-nth0
                    column
                    (tc-nth0
                     row
                     (wbc-plan-matrix
                      (rwd-full-terms
                       p inputs kernels
                       (tc-plan-terms (1- (nfix p))))
                      (rwd-nonzero-post post)))))
                (c (rgi-fourier-entry p output row column))
                (d (tc-nth0
                    column
                    (tc-nth0 row
                             (rwd-fourier-matrix p output))))
                (e (nth column
                        (tc-nth0 row
                                 (rwd-fourier-matrix p output)))))
     (:instance rom-nth0-entry-of-full-plan)
     (:instance rom-nth0-fourier-entry)
     (:instance tc-nth0-is-nth-when-in-bounds
                (k column)
                (xs
                 (tc-nth0
                  row
                  (wbc-plan-matrix
                   (rwd-full-terms
                    p inputs kernels
                    (tc-plan-terms (1- (nfix p))))
                   (rwd-nonzero-post post)))))
     (:instance tc-nth0-is-nth-when-in-bounds
                (k column)
                (xs (tc-nth0 row
                             (rwd-fourier-matrix p output))))
     (:instance rom-full-plan-row-length)
     (:instance rom-fourier-row-length))
    :in-theory nil)))

(defthm rom-full-plan-row-equals-fourier-row
  (implies
   (and (tc-compact-post-certifiesp
         (1- (nfix p)) small-out post)
        (rgi-compact-outputp
         p small-out output inputs kernels)
        (natp small-out)
        (natp output)
        (posp p)
        (natp row) (< row p))
   (equal
    (tc-nth0
     row
     (wbc-plan-matrix
      (rwd-full-terms
       p inputs kernels (tc-plan-terms (1- (nfix p))))
      (rwd-nonzero-post post)))
    (tc-nth0 row (rwd-fourier-matrix p output))))
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
           (rwd-full-terms
            p inputs kernels (tc-plan-terms (1- (nfix p))))
           (rwd-nonzero-post post)))))
      (equal-by-nths-rhs
       (lambda ()
         (tc-nth0 row (rwd-fourier-matrix p output))))
      (equal-by-nths-hyp
       (lambda ()
         (and
          (tc-compact-post-certifiesp
           (1- (nfix p)) small-out post)
          (rgi-compact-outputp
           p small-out output inputs kernels)
          (natp small-out)
          (natp output)
          (posp p)
          (natp row) (< row p))))))
    :in-theory
    '((:rewrite rom-full-plan-row-true-listp)
      (:rewrite rom-fourier-row-true-listp)
      (:rewrite rom-full-plan-row-length)
      (:rewrite rom-fourier-row-length)
      (:rewrite rom-nth-of-full-plan-row-equals-fourier)))))

(defthm rom-true-listp-of-fourier-matrix-aux
  (true-listp
   (rwd-fourier-matrix-aux count input-index output-index p))
  :hints (("Goal"
           :induct (rwd-fourier-matrix-aux
                    count input-index output-index p)
           :in-theory (enable rwd-fourier-matrix-aux))))

(defthm rom-true-listp-of-fourier-matrix
  (true-listp (rwd-fourier-matrix p output))
  :hints (("Goal"
           :use ((:instance rom-true-listp-of-fourier-matrix-aux
                            (count p) (input-index 0)
                            (output-index output)))
           :in-theory '(rwd-fourier-matrix))))

(defthm rom-full-plan-matrix-length
  (implies
   (and (tc-compact-post-certifiesp
         (1- (nfix p)) small-out post)
        (posp p))
   (equal
    (len
     (wbc-plan-matrix
      (rwd-full-terms
       p inputs kernels (tc-plan-terms (1- (nfix p))))
      (rwd-nonzero-post post)))
    p))
  :hints
  (("Goal"
    :use ((:instance rom-rational-matrixp-of-full-plan)
          (:instance tc-len-of-rational-matrixp
                     (rows p) (cols p)
                     (matrix
                      (wbc-plan-matrix
                       (rwd-full-terms
                        p inputs kernels
                        (tc-plan-terms (1- (nfix p))))
                       (rwd-nonzero-post post)))))
    :in-theory '(rgi-nfix-when-posp))))

(defthm rom-fourier-matrix-length
  (implies (posp p)
           (equal (len (rwd-fourier-matrix p output)) p))
  :hints
  (("Goal"
    :use ((:instance rational-matrixp-of-rwd-fourier-matrix
                     (output-index output))
          (:instance tc-len-of-rational-matrixp
                     (rows p) (cols p)
                     (matrix (rwd-fourier-matrix p output))))
    :in-theory '(rgi-nfix-when-posp))))

(defthm rom-nth-of-full-plan-matrix-equals-fourier
  (implies
   (and (tc-compact-post-certifiesp
         (1- (nfix p)) small-out post)
        (rgi-compact-outputp
         p small-out output inputs kernels)
        (natp small-out)
        (natp output)
        (posp p)
        (natp row) (< row p))
   (equal
    (nth
     row
     (wbc-plan-matrix
      (rwd-full-terms
       p inputs kernels (tc-plan-terms (1- (nfix p))))
      (rwd-nonzero-post post)))
    (nth row (rwd-fourier-matrix p output))))
  :hints
  (("Goal"
    :use
    ((:instance tc-equality-chain-3
                (a (nth
                    row
                    (wbc-plan-matrix
                     (rwd-full-terms
                      p inputs kernels
                      (tc-plan-terms (1- (nfix p))))
                     (rwd-nonzero-post post))))
                (b (tc-nth0
                    row
                    (wbc-plan-matrix
                     (rwd-full-terms
                      p inputs kernels
                      (tc-plan-terms (1- (nfix p))))
                     (rwd-nonzero-post post))))
                (c (tc-nth0 row
                            (rwd-fourier-matrix p output)))
                (d (nth row
                        (rwd-fourier-matrix p output))))
     (:instance tc-nth0-is-nth-when-in-bounds
                (k row)
                (xs
                 (wbc-plan-matrix
                  (rwd-full-terms
                   p inputs kernels
                   (tc-plan-terms (1- (nfix p))))
                  (rwd-nonzero-post post))))
     (:instance tc-nth0-is-nth-when-in-bounds
                (k row)
                (xs (rwd-fourier-matrix p output)))
     (:instance rom-full-plan-matrix-length)
     (:instance rom-fourier-matrix-length)
     (:instance rom-full-plan-row-equals-fourier-row))
    :in-theory nil)))

(defthm rom-full-plan-matrix-equals-fourier
  (implies
   (and (tc-compact-post-certifiesp
         (1- (nfix p)) small-out post)
        (rgi-compact-outputp
         p small-out output inputs kernels)
        (natp small-out)
        (natp output)
        (posp p))
   (equal
    (wbc-plan-matrix
     (rwd-full-terms
      p inputs kernels (tc-plan-terms (1- (nfix p))))
     (rwd-nonzero-post post))
    (rwd-fourier-matrix p output)))
  :hints
  (("Goal"
    :use
    ((:functional-instance
      equal-by-nths
      (equal-by-nths-lhs
       (lambda ()
         (wbc-plan-matrix
          (rwd-full-terms
           p inputs kernels (tc-plan-terms (1- (nfix p))))
          (rwd-nonzero-post post))))
      (equal-by-nths-rhs
       (lambda () (rwd-fourier-matrix p output)))
      (equal-by-nths-hyp
       (lambda ()
         (and
          (tc-compact-post-certifiesp
           (1- (nfix p)) small-out post)
          (rgi-compact-outputp
           p small-out output inputs kernels)
          (natp small-out)
          (natp output)
          (posp p))))))
    :in-theory
    '((:rewrite tc-true-listp-of-wbc-plan-matrix)
      (:rewrite rom-true-listp-of-fourier-matrix)
      (:rewrite rom-full-plan-matrix-length)
      (:rewrite rom-fourier-matrix-length)
      (:rewrite rom-nth-of-full-plan-matrix-equals-fourier)))))

(defthm rom-compact-output-implies-plan-certificate
  (implies
   (and (tc-compact-post-certifiesp
         (1- (nfix p)) small-out post)
        (rgi-compact-outputp
         p small-out output inputs kernels)
        (natp small-out)
        (natp output)
        (posp p))
   (rwd-plan-certifies-outputp
    p output
    (rwd-full-terms
     p inputs kernels (tc-plan-terms (1- (nfix p))))
    (rwd-nonzero-post post)))
  :hints
  (("Goal"
    :use ((:instance rgi-nonzero-full-plan-validp
                     (n (1- (nfix p)))
                     (out small-out))
          (:instance rom-full-plan-matrix-equals-fourier))
    :in-theory '(rwd-plan-certifies-outputp))))
