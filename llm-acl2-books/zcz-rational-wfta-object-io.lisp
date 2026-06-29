; Object-stream front end for total rational forward/inverse WFTAs.
;
; Legacy scalar requests remain accepted:
;
;   (:wfta :forward P EPSILON)
;   (X0 X1 ... X{P-1})
;
; The native rational-pair interface is:
;
;   (:wfta-pairs :forward P EPSILON)
;   ((R0 . I0) (R1 . I1) ... (R{P-1} . I{P-1}))
;
; Either direction may be :FORWARD or :INVERSE.  On success the I/O entry
; points print one ACL2-readable list of rational pairs.  The output order is
; (0 . generated-Rader-output-order).
;
; The mathematics and request validation are logical.  Only the final reader
; and formatter use ACL2's built-in STATE stobj.
(in-package "ACL2")

(include-book "zcx2-total-rational-pair-wfta")

(defun zcz-directionp (x)
  (or (eq x :forward)
      (eq x :inverse)))

(defun zcz-spec-tag (spec)
  (car spec))

(defun zcz-scalar-spec-p (spec)
  (eq (zcz-spec-tag spec) :wfta))

(defun zcz-pair-spec-p (spec)
  (eq (zcz-spec-tag spec) :wfta-pairs))

(defun zcz-spec-direction (spec)
  (cadr spec))

(defun zcz-spec-order (spec)
  (nfix (caddr spec)))

(defun zcz-spec-epsilon (spec)
  (cadddr spec))

(defun zcz-generation-spec-p (spec)
  (and (true-listp spec)
       (equal (len spec) 4)
       (or (zcz-scalar-spec-p spec)
           (zcz-pair-spec-p spec))
       (zcz-directionp (zcz-spec-direction spec))
       (integerp (caddr spec))
       (< 2 (caddr spec))
       (dm::primep (caddr spec))
       (rationalp (zcz-spec-epsilon spec))
       (< 0 (zcz-spec-epsilon spec))))

(defun zcz-input-vector-p (spec xs)
  (and (if (zcz-pair-spec-p spec)
           (qcx-list-rationalp xs)
         (rational-listp xs))
       (equal (len xs) (zcz-spec-order spec))))

(defun zcz-request-p (spec xs)
  (and (zcz-generation-spec-p spec)
       (zcz-input-vector-p spec xs)))

(defun zcz-generated-output-order (spec)
  (let* ((p (zcz-spec-order spec))
         (generator (zcw-total-generator p)))
    (rwd-output-order (rgi-generated-outputs p generator))))

(defun zcz-transform-values (spec xs)
  (let ((p (zcz-spec-order spec))
        (epsilon (zcz-spec-epsilon spec)))
    (if (zcz-pair-spec-p spec)
        (if (eq (zcz-spec-direction spec) :inverse)
            (zcx2-total-inverse-pair-wfta-run p epsilon xs)
          (zcx2-total-forward-pair-wfta-run p epsilon xs))
      (if (eq (zcz-spec-direction spec) :inverse)
          (zcx-total-inverse-wfta-run p epsilon xs)
        (zcw-total-wfta-run p epsilon xs)))))

(defun zcz-evaluate-request (spec xs)
  (if (zcz-request-p spec xs)
      (zcz-transform-values spec xs)
    nil))

(defthm zcz-positive-integer-nfix
  (implies (and (integerp x)
                (< 2 x))
           (equal (nfix x) x))
  :hints (("Goal"
           :use ((:instance rgi-nfix-when-natp (x x))))))

(defthm zcz-generation-spec-p-implies-odd-prime-order
  (implies (zcz-generation-spec-p spec)
           (and (dm::primep (zcz-spec-order spec))
                (integerp (zcz-spec-order spec))
                (< 2 (zcz-spec-order spec))))
  :hints (("Goal"
           :use ((:instance zcz-positive-integer-nfix
                            (x (caddr spec))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcz-generation-spec-p zcz-spec-order)))))

(defthm zcz-generation-spec-p-implies-positive-rational-epsilon
  (implies (zcz-generation-spec-p spec)
           (and (rationalp (zcz-spec-epsilon spec))
                (< 0 (zcz-spec-epsilon spec))))
  :hints (("Goal"
           :in-theory (enable zcz-generation-spec-p))))

(defthm zcz-request-p-implies-generation-spec-p
  (implies (zcz-request-p spec xs)
           (zcz-generation-spec-p spec))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcz-request-p)))))

(defthm zcz-scalar-request-p-implies-rational-input-vector
  (implies (and (zcz-request-p spec xs)
                (zcz-scalar-spec-p spec))
           (and (rational-listp xs)
                (equal (len xs) (zcz-spec-order spec))))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcz-request-p zcz-input-vector-p
              zcz-scalar-spec-p zcz-pair-spec-p zcz-spec-tag)))))

(defthm zcz-pair-request-p-implies-qcx-input-list
  (implies (and (zcz-request-p spec xs)
                (zcz-pair-spec-p spec))
           (and (qcx-list-rationalp xs)
                (equal (len xs) (zcz-spec-order spec))))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcz-request-p zcz-input-vector-p zcz-pair-spec-p)))))

(defthm zcz-nfix-of-spec-order
  (equal (nfix (zcz-spec-order spec))
         (zcz-spec-order spec))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcz-spec-order nfix)))))

(defthm zcz-pair-request-p-implies-qcx-input-vector
  (implies (and (zcz-request-p spec xs)
                (zcz-pair-spec-p spec))
           (qcx-vectorp (zcz-spec-order spec) xs))
  :hints (("Goal"
           :use ((:instance zcz-pair-request-p-implies-qcx-input-list))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(qcx-vectorp zcz-nfix-of-spec-order)))))

(defthm zcz-nfix-of-len
  (equal (nfix (len xs)) (len xs))
  :hints (("Goal"
           :use ((:instance rgi-nfix-when-natp
                            (x (len xs)))))))

(defthm zcz-transform-values-of-scalar-forward-spec
  (implies (and (zcz-scalar-spec-p spec)
                (eq (zcz-spec-direction spec) :forward))
           (equal (zcz-transform-values spec xs)
                  (zcw-total-wfta-run
                   (zcz-spec-order spec)
                   (zcz-spec-epsilon spec)
                   xs)))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcz-transform-values zcz-scalar-spec-p zcz-pair-spec-p
              zcz-spec-direction zcz-spec-order zcz-spec-epsilon eq)))))

(defthm zcz-transform-values-of-scalar-inverse-spec
  (implies (and (zcz-scalar-spec-p spec)
                (eq (zcz-spec-direction spec) :inverse))
           (equal (zcz-transform-values spec xs)
                  (zcx-total-inverse-wfta-run
                   (zcz-spec-order spec)
                   (zcz-spec-epsilon spec)
                   xs)))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcz-transform-values zcz-scalar-spec-p zcz-pair-spec-p
              zcz-spec-direction zcz-spec-order zcz-spec-epsilon eq)))))

(defthm zcz-transform-values-of-pair-forward-spec
  (implies (and (zcz-pair-spec-p spec)
                (eq (zcz-spec-direction spec) :forward))
           (equal (zcz-transform-values spec xs)
                  (zcx2-total-forward-pair-wfta-run
                   (zcz-spec-order spec)
                   (zcz-spec-epsilon spec)
                   xs)))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcz-transform-values zcz-pair-spec-p
              zcz-spec-direction zcz-spec-order zcz-spec-epsilon eq)))))

(defthm zcz-transform-values-of-pair-inverse-spec
  (implies (and (zcz-pair-spec-p spec)
                (eq (zcz-spec-direction spec) :inverse))
           (equal (zcz-transform-values spec xs)
                  (zcx2-total-inverse-pair-wfta-run
                   (zcz-spec-order spec)
                   (zcz-spec-epsilon spec)
                   xs)))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcz-transform-values zcz-pair-spec-p
              zcz-spec-direction zcz-spec-order zcz-spec-epsilon eq)))))

(defthm zcz-evaluate-request-is-transform-on-valid-request
  (implies (zcz-request-p spec xs)
           (equal (zcz-evaluate-request spec xs)
                  (zcz-transform-values spec xs)))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(zcz-evaluate-request)))))

(defthm zcz-scalar-forward-request-inherits-wfta-correctness
  (implies
   (and (zcz-request-p spec xs)
        (zcz-scalar-spec-p spec)
        (eq (zcz-spec-direction spec) :forward))
   (equal
    (zcz-transform-values spec xs)
    (zcw-total-direct-run
     (zcz-spec-order spec)
     (zcz-spec-epsilon spec)
     xs)))
  :hints
  (("Goal"
    :use
    ((:instance zcz-transform-values-of-scalar-forward-spec)
     (:instance zcz-request-p-implies-generation-spec-p)
     (:instance zcz-generation-spec-p-implies-odd-prime-order)
     (:instance zcz-generation-spec-p-implies-positive-rational-epsilon)
     (:instance zcz-scalar-request-p-implies-rational-input-vector)
     (:instance zcw-total-rational-wfta-correct
                (p (zcz-spec-order spec))
                (epsilon (zcz-spec-epsilon spec))))
    :in-theory
    (union-theories (theory 'minimal-theory) '(zcz-nfix-of-len)))))

(defthm zcz-scalar-inverse-request-inherits-wfta-correctness
  (implies
   (and (zcz-request-p spec xs)
        (zcz-scalar-spec-p spec)
        (eq (zcz-spec-direction spec) :inverse))
   (equal
    (zcz-transform-values spec xs)
    (zcx-total-direct-inverse-run
     (zcz-spec-order spec)
     (zcz-spec-epsilon spec)
     xs)))
  :hints
  (("Goal"
    :use
    ((:instance zcz-transform-values-of-scalar-inverse-spec)
     (:instance zcz-request-p-implies-generation-spec-p)
     (:instance zcz-generation-spec-p-implies-odd-prime-order)
     (:instance zcz-generation-spec-p-implies-positive-rational-epsilon)
     (:instance zcz-scalar-request-p-implies-rational-input-vector)
     (:instance zcx-total-rational-inverse-wfta-correct
                (p (zcz-spec-order spec))
                (epsilon (zcz-spec-epsilon spec))))
    :in-theory
    (union-theories (theory 'minimal-theory) '(zcz-nfix-of-len)))))

(defthm zcz-pair-forward-request-inherits-wfta-correctness
  (implies
   (and (zcz-request-p spec xs)
        (zcz-pair-spec-p spec)
        (eq (zcz-spec-direction spec) :forward))
   (equal
    (zcz-transform-values spec xs)
    (zcx2-total-direct-forward-pair-run
     (zcz-spec-order spec)
     (zcz-spec-epsilon spec)
     xs)))
  :hints
  (("Goal"
    :use
    ((:instance zcz-transform-values-of-pair-forward-spec)
     (:instance zcz-request-p-implies-generation-spec-p)
     (:instance zcz-generation-spec-p-implies-odd-prime-order)
     (:instance zcz-generation-spec-p-implies-positive-rational-epsilon)
     (:instance zcz-pair-request-p-implies-qcx-input-vector)
     (:instance zcx2-total-rational-pair-forward-wfta-correct
                (p (zcz-spec-order spec))
                (epsilon (zcz-spec-epsilon spec))))
    :in-theory (theory 'minimal-theory))))

(defthm zcz-pair-inverse-request-inherits-wfta-correctness
  (implies
   (and (zcz-request-p spec xs)
        (zcz-pair-spec-p spec)
        (eq (zcz-spec-direction spec) :inverse))
   (equal
    (zcz-transform-values spec xs)
    (zcx2-total-direct-inverse-pair-run
     (zcz-spec-order spec)
     (zcz-spec-epsilon spec)
     xs)))
  :hints
  (("Goal"
    :use
    ((:instance zcz-transform-values-of-pair-inverse-spec)
     (:instance zcz-request-p-implies-generation-spec-p)
     (:instance zcz-generation-spec-p-implies-odd-prime-order)
     (:instance zcz-generation-spec-p-implies-positive-rational-epsilon)
     (:instance zcz-pair-request-p-implies-qcx-input-vector)
     (:instance zcx2-total-rational-pair-inverse-wfta-correct
                (p (zcz-spec-order spec))
                (epsilon (zcz-spec-epsilon spec))))
    :in-theory (theory 'minimal-theory))))

(program)
(set-state-ok t)

(defun zcz-fmt-object-line (obj channel state)
  (declare (xargs :stobjs state))
  (mv-let (col state)
    (fmt "~x0~%" (list (cons #\0 obj)) channel state nil)
    (declare (ignore col))
    state))

(defun zcz-fmt-error (kind object channel state)
  (declare (xargs :stobjs state))
  (zcz-fmt-object-line (list :error kind object) channel state))

(defun zcz-run-object-channel (input-channel output-channel state)
  (declare (xargs :stobjs state))
  (mv-let (spec-eofp spec state)
    (read-object input-channel state)
    (if spec-eofp
        (zcz-fmt-error :missing-spec nil output-channel state)
      (mv-let (data-eofp xs state)
        (read-object input-channel state)
        (cond
         (data-eofp
          (zcz-fmt-error :missing-input-vector spec output-channel state))
         ((not (zcz-generation-spec-p spec))
          (zcz-fmt-error :bad-generation-spec spec output-channel state))
         ((and (zcz-pair-spec-p spec)
               (not (qcx-list-rationalp xs)))
          (zcz-fmt-error :non-rational-pair-input xs output-channel state))
         ((and (zcz-scalar-spec-p spec)
               (not (rational-listp xs)))
          (zcz-fmt-error :non-rational-input xs output-channel state))
         ((not (equal (len xs) (zcz-spec-order spec)))
          (zcz-fmt-error
           :wrong-input-length
           (list :expected (zcz-spec-order spec) :received (len xs))
           output-channel state))
         (t
          (zcz-fmt-object-line
           (zcz-transform-values spec xs)
           output-channel state)))))))

(defun zcz-main (state)
  (declare (xargs :stobjs state))
  (zcz-run-object-channel *standard-oi* *standard-co* state))

(defun zcz-run-file (filename state)
  (declare (xargs :stobjs state))
  (mv-let (channel state)
    (open-input-channel filename :object state)
    (if channel
        (let* ((state (zcz-run-object-channel
                       channel *standard-co* state))
               (state (close-input-channel channel state)))
          state)
      (zcz-fmt-error :cannot-open-file filename *standard-co* state))))
