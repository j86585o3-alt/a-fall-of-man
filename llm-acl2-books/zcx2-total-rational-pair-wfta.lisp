; Native rational-pair forward and inverse WFTA interfaces.
;
; The certified compiler has always been a rational-pair transformer.  This
; book exposes that native interface, and proves that the older rational-scalar
; wrappers are precisely its restriction along QCX-REALIFY.
(in-package "ACL2")

(include-book "zcx-total-rational-inverse-wfta")

(defun zcx2-total-forward-pair-wfta-run (p epsilon xs)
  (let ((generator (zcw-total-generator p)))
    (rwd-run
     p
     (rgi-generated-inputs p generator)
     (rgi-generated-kernels p generator)
     (tc-plan-terms (1- (nfix p)))
     (tc-plan-posts (1- (nfix p)))
     xs
     (zcw-total-twiddle-table p epsilon))))

(defun zcx2-total-direct-forward-pair-run (p epsilon xs)
  (let ((generator (zcw-total-generator p)))
    (rwd-direct-outputs
     (rwd-output-order (rgi-generated-outputs p generator))
     p xs
     (zcw-total-twiddle-table p epsilon))))

(defun zcx2-total-inverse-pair-wfta-run (p epsilon xs)
  (let ((generator (zcw-total-generator p)))
    (zcx-qcx-scale-list
     (zcx-inverse-scale p)
     (rwd-run
      p
      (rgi-generated-inputs p generator)
      (rgi-generated-kernels p generator)
      (tc-plan-terms (1- (nfix p)))
      (tc-plan-posts (1- (nfix p)))
      xs
      (zcx-total-inverse-table p epsilon)))))

(defun zcx2-total-direct-inverse-pair-run (p epsilon xs)
  (let ((generator (zcw-total-generator p)))
    (zcx-qcx-scale-list
     (zcx-inverse-scale p)
     (rwd-direct-outputs
      (rwd-output-order (rgi-generated-outputs p generator))
      p xs
      (zcx-total-inverse-table p epsilon)))))

(defun zcx2-qcx-real-parts (xs)
  (if (endp xs)
      nil
    (cons (qcx-re (car xs))
          (zcx2-qcx-real-parts (cdr xs)))))

(defun zcx2-qcx-imag-parts (xs)
  (if (endp xs)
      nil
    (cons (qcx-im (car xs))
          (zcx2-qcx-imag-parts (cdr xs)))))

(defthm zcx2-total-forward-table-is-qcx-vector
  (implies (and (integerp p)
                (< 2 p)
                (rationalp epsilon)
                (< 0 epsilon))
           (qcx-vectorp p (zcw-total-twiddle-table p epsilon)))
  :hints
  (("Goal"
    :use ((:instance zcw-odd-prime-is-posp)
          (:instance zcu-small-tangent-rational
                     (n p))
          (:instance qcx-vectorp-of-rct-twiddle-table
                     (n p)
                     (other-chart nil)
                     (tangent (zcw-total-tangent p epsilon))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcw-total-twiddle-table zcw-total-tangent)))))

(defthm zcx2-total-rational-pair-forward-wfta-correct
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p)
        (rationalp epsilon)
        (< 0 epsilon)
        (qcx-vectorp p xs))
   (equal (zcx2-total-forward-pair-wfta-run p epsilon xs)
          (zcx2-total-direct-forward-pair-run p epsilon xs)))
  :hints
  (("Goal"
    :use
    ((:instance zcw-total-generated-compiler-certificate)
     (:instance zcx2-total-forward-table-is-qcx-vector)
     (:instance rwd-compiled-transform-correct
                (input-indices
                 (rgi-generated-inputs p (zcw-total-generator p)))
                (kernel-indices
                 (rgi-generated-kernels p (zcw-total-generator p)))
                (output-indices
                 (rgi-generated-outputs p (zcw-total-generator p)))
                (small-terms (tc-plan-terms (1- (nfix p))))
                (small-posts (tc-plan-posts (1- (nfix p))))
                (table (zcw-total-twiddle-table p epsilon))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcx2-total-forward-pair-wfta-run
       zcx2-total-direct-forward-pair-run
       rwd-compile-outputs)))))

(defthm zcx2-total-rational-pair-inverse-wfta-correct
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p)
        (rationalp epsilon)
        (< 0 epsilon)
        (qcx-vectorp p xs))
   (equal (zcx2-total-inverse-pair-wfta-run p epsilon xs)
          (zcx2-total-direct-inverse-pair-run p epsilon xs)))
  :hints
  (("Goal"
    :use
    ((:instance zcw-total-generated-compiler-certificate)
     (:instance zcx-total-inverse-table-is-qcx-vector)
     (:instance rwd-compiled-transform-correct
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
     '(zcx2-total-inverse-pair-wfta-run
       zcx2-total-direct-inverse-pair-run
       rwd-compile-outputs)))))

(defthm zcw-scalar-forward-is-pair-forward-of-realify
  (equal (zcw-total-wfta-run p epsilon xs)
         (zcx2-total-forward-pair-wfta-run
          p epsilon (qcx-realify xs)))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcw-total-wfta-run
              rwd-rational-input-run
              zcx2-total-forward-pair-wfta-run)))))

(defthm zcx-scalar-inverse-is-pair-inverse-of-realify
  (equal (zcx-total-inverse-wfta-run p epsilon xs)
         (zcx2-total-inverse-pair-wfta-run
          p epsilon (qcx-realify xs)))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcx-total-inverse-wfta-run
              rwd-rational-input-run
              zcx2-total-inverse-pair-wfta-run)))))

(defthm len-of-zcx2-qcx-real-parts
  (equal (len (zcx2-qcx-real-parts xs))
         (len xs))
  :hints (("Goal"
           :induct (zcx2-qcx-real-parts xs)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcx2-qcx-real-parts len endp car-cons cdr-cons)))))

(defthm len-of-zcx2-qcx-imag-parts
  (equal (len (zcx2-qcx-imag-parts xs))
         (len xs))
  :hints (("Goal"
           :induct (zcx2-qcx-imag-parts xs)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcx2-qcx-imag-parts len endp car-cons cdr-cons)))))

(defthm rational-listp-of-zcx2-qcx-real-parts
  (implies (qcx-list-rationalp xs)
           (rational-listp (zcx2-qcx-real-parts xs)))
  :hints (("Goal"
           :induct (zcx2-qcx-real-parts xs)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcx2-qcx-real-parts qcx-list-rationalp rational-listp
              qcx-rationalp qcx-re endp car-cons cdr-cons)))))

(defthm rational-listp-of-zcx2-qcx-imag-parts
  (implies (qcx-list-rationalp xs)
           (rational-listp (zcx2-qcx-imag-parts xs)))
  :hints (("Goal"
           :induct (zcx2-qcx-imag-parts xs)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcx2-qcx-imag-parts qcx-list-rationalp rational-listp
              qcx-rationalp qcx-im endp car-cons cdr-cons)))))

(defthm zcx2-real-parts-of-realify
  (equal (zcx2-qcx-real-parts (qcx-realify xs))
         (true-list-fix xs))
  :hints (("Goal"
           :induct (qcx-realify xs)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcx2-qcx-real-parts qcx-realify true-list-fix
              qcx-re qcx endp car-cons cdr-cons)))))
