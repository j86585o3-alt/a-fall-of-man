; Generated Rader index systems and their finite algebraic certificate.
(in-package "ACL2")
(include-book "zar-rader-winograd-dft")
(include-book "std/lists/top" :dir :system)

(defun rgi-orbit-aux (count value generator modulus)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (mod (nfix value) (nfix modulus))
          (rgi-orbit-aux (1- count)
                         (mod (* (nfix value) (nfix generator))
                              (nfix modulus))
                         generator modulus))))

(defun rgi-orbit (p generator)
  (rgi-orbit-aux (1- (nfix p)) 1 generator p))

(defun rgi-inverse-orbit (p generator)
  (let ((orbit (rgi-orbit p generator)))
    (if (endp orbit)
        nil
      (cons 1 (reverse (cdr orbit))))))

(defun rgi-positive-residuesp (p xs)
  (if (endp xs)
      t
    (and (posp (car xs))
         (< (car xs) (nfix p))
         (rgi-positive-residuesp p (cdr xs)))))

(defun rgi-permutationp (p xs)
  (and (equal (len xs) (1- (nfix p)))
       (rgi-positive-residuesp p xs)
       (no-duplicatesp-equal xs)))

(defun rgi-relation-rowp (count a p inputs kernels outputs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let* ((n (1- (nfix p)))
           (m (1- (nfix count))))
      (and (equal (nth (mod (- m (nfix a)) n) kernels)
                  (mod (* (nth (nfix a) inputs)
                          (nth m outputs))
                       (nfix p)))
           (rgi-relation-rowp (1- count) a p
                              inputs kernels outputs)))))

(defun rgi-relationp-aux (count p inputs kernels outputs)
  (declare (xargs :measure (nfix count)
                  :hints (("Goal" :in-theory (enable nfix)))))
  (if (zp count)
      t
    (let ((a (1- (nfix count))))
      (and (rgi-relation-rowp (1- (nfix p)) a p
                              inputs kernels outputs)
           (rgi-relationp-aux (1- count) p
                              inputs kernels outputs)))))

(defun rgi-index-certificatep (p inputs kernels outputs)
  (and (< 2 (nfix p))
       (rgi-permutationp p inputs)
       (rgi-permutationp p kernels)
       (rgi-permutationp p outputs)
       (rgi-relationp-aux (1- (nfix p)) p
                          inputs kernels outputs)))

(defun rgi-generated-inputs (p generator)
  (rgi-inverse-orbit p generator))

(defun rgi-generated-kernels (p generator)
  (rgi-orbit p generator))

(defun rgi-generated-outputs (p generator)
  (rgi-orbit p generator))

(defun rgi-generated-index-certificatep (p generator)
  (rgi-index-certificatep
   p
   (rgi-generated-inputs p generator)
   (rgi-generated-kernels p generator)
   (rgi-generated-outputs p generator)))

(defthm len-of-rgi-orbit-aux
  (equal (len (rgi-orbit-aux count value generator modulus))
         (nfix count)))

(defthm len-of-rgi-orbit
  (equal (len (rgi-orbit p generator))
         (nfix (1- (nfix p)))))

(defthm rgi-index-certificate-implies-input-permutation
  (implies (rgi-index-certificatep p inputs kernels outputs)
           (rgi-permutationp p inputs))
  :hints (("Goal" :in-theory (enable rgi-index-certificatep))))

(defthm rgi-index-certificate-implies-kernel-permutation
  (implies (rgi-index-certificatep p inputs kernels outputs)
           (rgi-permutationp p kernels))
  :hints (("Goal" :in-theory (enable rgi-index-certificatep))))

(defthm rgi-index-certificate-implies-output-permutation
  (implies (rgi-index-certificatep p inputs kernels outputs)
           (rgi-permutationp p outputs))
  :hints (("Goal" :in-theory (enable rgi-index-certificatep))))

(defthm rgi-index-certificate-implies-relation
  (implies (rgi-index-certificatep p inputs kernels outputs)
           (rgi-relationp-aux (1- (nfix p)) p
                              inputs kernels outputs))
  :hints (("Goal" :in-theory (enable rgi-index-certificatep))))
