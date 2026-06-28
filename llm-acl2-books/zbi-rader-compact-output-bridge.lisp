; Indexed Fourier correctness from the compact Rader certificate.
(in-package "ACL2")
(include-book "zbh-rader-fourier-bridge")

(defun rcb-countdown-induct (count index)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count)
          (equal index (1- (nfix count))))
      (list count index)
    (rcb-countdown-induct (1- count) index)))

(defthm rcb-nfix-of-predecessor
  (implies (not (zp count))
           (equal (nfix (1- count))
                  (1- (nfix count))))
  :hints (("Goal" :in-theory (enable zp nfix))))

(defthm rcb-index-below-predecessor
  (implies (and (natp index)
                (< index (nfix count))
                (not (equal index (1- (nfix count)))))
           (< index (1- (nfix count)))))

(defthm rcb-zp-no-bounded-nat
  (implies (and (zp count) (natp index))
           (not (< index (nfix count))))
  :hints (("Goal" :in-theory (enable zp nfix natp))))

(defthm rcb-last-index-implies-not-zp
  (implies (and (natp (1- (nfix count)))
                (< (1- (nfix count)) (nfix count)))
           (not (zp count)))
  :hints (("Goal" :in-theory (enable zp nfix natp))))

(defthm rcb-compact-output-rowp-head
  (implies
   (and (rgi-compact-output-rowp
         count column p small-out output inputs kernels)
        (not (zp count)))
   (equal
    (+ (rgi-base-entry (1- (nfix count)) column)
       (rgi-lifted-entry (1- (nfix p)) small-out
                         (1- (nfix count)) column inputs kernels))
    (rgi-fourier-entry p output (1- (nfix count)) column)))
  :hints (("Goal" :in-theory '(rgi-compact-output-rowp))))

(defthm rcb-compact-output-rowp-tail
  (implies
   (and (rgi-compact-output-rowp
         count column p small-out output inputs kernels)
        (not (zp count)))
   (rgi-compact-output-rowp
    (1- count) column p small-out output inputs kernels))
  :hints (("Goal" :in-theory '(rgi-compact-output-rowp))))

(defthm rcb-compact-output-rowp-entry
  (implies
   (and (rgi-compact-output-rowp
         count column p small-out output inputs kernels)
        (natp row)
        (< row (nfix count)))
   (equal
    (+ (rgi-base-entry row column)
       (rgi-lifted-entry (1- (nfix p)) small-out
                         row column inputs kernels))
    (rgi-fourier-entry p output row column)))
  :hints
  (("Goal"
    :induct (rcb-countdown-induct count row)
    :in-theory '(rcb-countdown-induct
                 rcb-nfix-of-predecessor
                 rcb-index-below-predecessor
                 rcb-zp-no-bounded-nat
                 rcb-last-index-implies-not-zp
                 rcb-compact-output-rowp-head
                 rcb-compact-output-rowp-tail))))

(defthm rcb-compact-outputp-aux-head
  (implies
   (and (rgi-compact-outputp-aux
         count p small-out output inputs kernels)
        (not (zp count)))
   (rgi-compact-output-rowp
    p (1- (nfix count)) p small-out output inputs kernels))
  :hints (("Goal" :in-theory '(rgi-compact-outputp-aux))))

(defthm rcb-compact-outputp-aux-head-entry
  (implies
   (and (rgi-compact-outputp-aux
         count p small-out output inputs kernels)
        (not (zp count))
        (natp row)
        (< row (nfix p)))
   (equal
    (+ (rgi-base-entry row (1- (nfix count)))
       (rgi-lifted-entry (1- (nfix p)) small-out
                         row (1- (nfix count)) inputs kernels))
    (rgi-fourier-entry p output row (1- (nfix count)))))
  :hints
  (("Goal"
    :use ((:instance rcb-compact-outputp-aux-head)
          (:instance rcb-compact-output-rowp-entry
                     (count p)
                     (column (1- (nfix count)))))
    :in-theory nil)))

(defthm rcb-compact-outputp-aux-tail
  (implies
   (and (rgi-compact-outputp-aux
         count p small-out output inputs kernels)
        (not (zp count)))
   (rgi-compact-outputp-aux
    (1- count) p small-out output inputs kernels))
  :hints (("Goal" :in-theory '(rgi-compact-outputp-aux))))

(defthm rcb-compact-outputp-aux-entry
  (implies
   (and (rgi-compact-outputp-aux
         count p small-out output inputs kernels)
        (natp column)
        (< column (nfix count))
        (natp row)
        (< row (nfix p)))
   (equal
    (+ (rgi-base-entry row column)
       (rgi-lifted-entry (1- (nfix p)) small-out
                         row column inputs kernels))
    (rgi-fourier-entry p output row column)))
  :hints
  (("Goal"
    :induct (rcb-countdown-induct count column)
    :in-theory '(rcb-countdown-induct
                 rcb-nfix-of-predecessor
                 rcb-index-below-predecessor
                 rcb-zp-no-bounded-nat
                 rcb-last-index-implies-not-zp
                 rcb-compact-outputp-aux-head-entry
                 rcb-compact-outputp-aux-tail))))

(defthm rcb-compact-outputp-entry
  (implies
   (and (rgi-compact-outputp
         p small-out output inputs kernels)
        (natp row)
        (< row (nfix p))
        (natp column)
        (< column (nfix p)))
   (equal
    (+ (rgi-base-entry row column)
       (rgi-lifted-entry (1- (nfix p)) small-out
                         row column inputs kernels))
    (rgi-fourier-entry p output row column)))
  :hints
  (("Goal"
    :use ((:instance rcb-compact-outputp-aux-entry
                     (count p)))
    :in-theory '(rgi-compact-outputp))))

(defthm rcb-posp-excludes-zp
  (implies (posp p)
           (not (zp p)))
  :hints (("Goal" :in-theory (enable posp zp))))

(defthm rcb-nfix-of-len
  (equal (nfix (len xs)) (len xs)))

(defthm rcb-compact-outputp-input-length
  (implies (rgi-compact-outputp
            p small-out output inputs kernels)
           (equal (len inputs) (1- (nfix p))))
  :hints (("Goal" :in-theory '(rgi-compact-outputp))))

(defthm rcb-compact-outputp-kernel-length
  (implies (rgi-compact-outputp
            p small-out output inputs kernels)
           (equal (len kernels) (1- (nfix p))))
  :hints (("Goal" :in-theory '(rgi-compact-outputp))))

(defthm rcb-full-nonzero-fourier-entry
  (implies
   (and (tc-compact-post-certifiesp
         (1- (nfix p)) small-out post)
        (rgi-compact-outputp
         p small-out output inputs kernels)
        (natp small-out)
        (posp p)
        (natp row)
        (< row p)
        (natp column)
        (< column p))
   (equal
    (tc-matrix-entry
     row column
     (wbc-plan-matrix
      (rwd-full-terms
       p inputs kernels (tc-plan-terms (1- (nfix p))))
      (rwd-nonzero-post post)))
    (rgi-fourier-entry p output row column)))
  :hints
  (("Goal"
    :use ((:instance rfb-full-nonzero-entry
                     (n (1- p))
                     (out small-out))
          (:instance rcb-compact-outputp-entry)
          (:instance rcb-compact-outputp-input-length)
          (:instance rcb-compact-outputp-kernel-length)
          (:instance rcb-nfix-of-predecessor
                     (count p))
          (:instance rgi-nfix-when-posp
                     (n p))
          (:instance rcb-posp-excludes-zp)
          (:instance rcb-nfix-of-len
                     (xs inputs))
          (:instance rcb-nfix-of-len
                     (xs kernels)))
    :in-theory nil)))
