; Total rational inverse-form WFTA for odd prime orders.
;
; The inverse-form transform uses the conjugated generated twiddle table and
; the conventional rational factor 1/p.  Since the generated twiddles are
; rational pairs, conjugation and scaling stay entirely inside ordinary ACL2.
(in-package "ACL2")

(include-book "zcw-total-rational-wfta")

(defun zcx-qcx-conjugate (z)
  (qcx (qcx-re z) (- (qcx-im z))))

(defun zcx-qcx-conjugate-list (xs)
  (if (endp xs)
      nil
    (cons (zcx-qcx-conjugate (car xs))
          (zcx-qcx-conjugate-list (cdr xs)))))

(defun zcx-qcx-scale-list (a xs)
  (if (endp xs)
      nil
    (cons (qcx-scale a (car xs))
          (zcx-qcx-scale-list a (cdr xs)))))

(defun zcx-inverse-scale (p)
  (/ (nfix p)))

(defun zcx-total-inverse-table (p epsilon)
  (zcx-qcx-conjugate-list (zcw-total-twiddle-table p epsilon)))

(defun zcx-total-inverse-wfta-run (p epsilon xs)
  (let ((generator (zcw-total-generator p)))
    (zcx-qcx-scale-list
     (zcx-inverse-scale p)
     (rwd-rational-input-run
      p
      (rgi-generated-inputs p generator)
      (rgi-generated-kernels p generator)
      (tc-plan-terms (1- (nfix p)))
      (tc-plan-posts (1- (nfix p)))
      xs
      (zcx-total-inverse-table p epsilon)))))

(defun zcx-total-direct-inverse-run (p epsilon xs)
  (let ((generator (zcw-total-generator p)))
    (zcx-qcx-scale-list
     (zcx-inverse-scale p)
     (rwd-direct-outputs
      (rwd-output-order (rgi-generated-outputs p generator))
      p
      (qcx-realify xs)
      (zcx-total-inverse-table p epsilon)))))

(defthm zcx-qcx-rationalp-of-conjugate
  (implies (qcx-rationalp z)
           (qcx-rationalp (zcx-qcx-conjugate z)))
  :hints (("Goal"
           :in-theory (enable zcx-qcx-conjugate qcx-rationalp
                              qcx qcx-re qcx-im))))

(defthm len-of-zcx-qcx-conjugate-list
  (equal (len (zcx-qcx-conjugate-list xs))
         (len xs))
  :hints (("Goal"
           :induct (zcx-qcx-conjugate-list xs)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(zcx-qcx-conjugate-list len endp car-cons cdr-cons))))
)

(defthm qcx-list-rationalp-of-zcx-qcx-conjugate-list
  (implies (qcx-list-rationalp xs)
           (qcx-list-rationalp (zcx-qcx-conjugate-list xs)))
  :hints (("Goal"
           :induct (zcx-qcx-conjugate-list xs)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(zcx-qcx-conjugate-list
                         qcx-list-rationalp endp car-cons cdr-cons
                         zcx-qcx-rationalp-of-conjugate))))
)

(defthm qcx-vectorp-of-zcx-qcx-conjugate-list
  (implies (qcx-vectorp n xs)
           (qcx-vectorp n (zcx-qcx-conjugate-list xs)))
  :hints
  (("Goal"
    :use ((:instance len-of-zcx-qcx-conjugate-list)
          (:instance qcx-list-rationalp-of-zcx-qcx-conjugate-list))
    :in-theory
    (union-theories (theory 'minimal-theory) '(qcx-vectorp)))))

(defthm len-of-zcx-qcx-scale-list
  (equal (len (zcx-qcx-scale-list a xs))
         (len xs))
  :hints (("Goal"
           :induct (zcx-qcx-scale-list a xs)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(zcx-qcx-scale-list len endp car-cons cdr-cons))))
)

(defthm qcx-list-rationalp-of-zcx-qcx-scale-list
  (implies (and (rationalp a)
                (qcx-list-rationalp xs))
           (qcx-list-rationalp (zcx-qcx-scale-list a xs)))
  :hints (("Goal"
           :induct (zcx-qcx-scale-list a xs)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(zcx-qcx-scale-list qcx-list-rationalp endp car-cons cdr-cons
                         qcx-rationalp-of-scale))))
)

(defthm zcx-total-inverse-table-is-qcx-vector
  (implies (and (integerp p)
                (< 2 p)
                (rationalp epsilon)
                (< 0 epsilon))
           (qcx-vectorp p (zcx-total-inverse-table p epsilon)))
  :hints
  (("Goal"
    :use ((:instance zcw-odd-prime-is-posp)
          (:instance zcu-small-tangent-rational
                     (n p))
          (:instance qcx-vectorp-of-rct-twiddle-table
                     (n p)
                     (other-chart nil)
                     (tangent (zcw-total-tangent p epsilon)))
          (:instance qcx-vectorp-of-zcx-qcx-conjugate-list
                     (n p)
                     (xs (zcw-total-twiddle-table p epsilon))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcx-total-inverse-table
       zcw-total-twiddle-table
       zcw-total-tangent)))))

(defthm zcx-total-rational-inverse-wfta-correct
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p)
        (rationalp epsilon)
        (< 0 epsilon)
        (rational-listp xs)
        (equal (len xs) (nfix p)))
   (equal (zcx-total-inverse-wfta-run p epsilon xs)
          (zcx-total-direct-inverse-run p epsilon xs)))
  :hints
  (("Goal"
    :use
    ((:instance zcw-odd-prime-is-posp)
     (:instance zcw-total-generated-compiler-certificate)
     (:instance zcx-total-inverse-table-is-qcx-vector)
     (:instance rwd-rational-input-run-correct
                (input-indices
                 (rgi-generated-inputs p (zcw-total-generator p)))
                (kernel-indices
                 (rgi-generated-kernels p (zcw-total-generator p)))
                (output-indices
                 (rgi-generated-outputs p (zcw-total-generator p)))
                (small-terms (tc-plan-terms (1- (nfix p))))
                (small-posts (tc-plan-posts (1- (nfix p))))
                (table (zcx-total-inverse-table p epsilon))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcx-total-inverse-wfta-run
       zcx-total-direct-inverse-run
       rwd-compile-outputs)))))
