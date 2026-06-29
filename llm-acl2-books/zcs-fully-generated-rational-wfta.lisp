; Fully searched rational WFTA interface: finite-field generator, nonzero
; stereographic sign bracket, and bisection precision are all computed.
; Resource bounds remain explicit, and every successful result carries the
; existing universal ACL2 correctness theorem.
(in-package "ACL2")

(include-book "zcr-primitive-root-certificate-search")

(defun zcs-generated-wfta-object
  (p epsilon grid-depth precision-fuel)
  (let ((generator (zcr-generated-primitive-root p)))
    (list
     p
     generator
     (zcq-sector-bracket grid-depth p)
     (zcq-generated-precision precision-fuel grid-depth p epsilon)
     (zcq-generated-tangent precision-fuel grid-depth p epsilon)
     (zcq-generated-separation precision-fuel grid-depth p epsilon)
     (zcq-generated-twiddle-table precision-fuel grid-depth p epsilon)
     (rgi-generated-inputs p generator)
     (rgi-generated-kernels p generator)
     (rgi-generated-outputs p generator)
     (tc-plan-terms (1- (nfix p)))
     (tc-plan-posts (1- (nfix p))))))

(defun zcs-generated-wfta-certificatep
  (p epsilon grid-depth precision-fuel)
  (and (zcr-generated-primitive-rootp p)
       (zcq-generated-certificatep
        precision-fuel grid-depth p epsilon)))

(defun zcs-generated-wfta-run
  (p epsilon grid-depth precision-fuel xs)
  (zcq-rational-wfta-run
   p
   (zcr-generated-primitive-root p)
   epsilon grid-depth precision-fuel xs))

(defun zcs-generated-direct-run
  (p epsilon grid-depth precision-fuel xs)
  (zcq-rational-direct-run
   p
   (zcr-generated-primitive-root p)
   epsilon grid-depth precision-fuel xs))

(defthm true-listp-of-zcs-generated-wfta-object
  (true-listp
   (zcs-generated-wfta-object p epsilon grid-depth precision-fuel))
  :hints (("Goal" :in-theory (enable zcs-generated-wfta-object))))

(defthm zcs-fully-generated-rational-wfta-correct
  (implies
   (and
    (dm::primep p)
    (integerp p)
    (< 2 p)
    (zcs-generated-wfta-certificatep
     p epsilon grid-depth precision-fuel)
    (rational-listp xs)
    (equal (len xs) (nfix p)))
   (and
    (rct-twiddle-systemp
     p epsilon
     (zcq-generated-separation
      precision-fuel grid-depth p epsilon)
     (rct-rational-unit
      nil
      (zcq-generated-tangent
       precision-fuel grid-depth p epsilon))
     (zcq-generated-twiddle-table
      precision-fuel grid-depth p epsilon))
    (equal
     (zcs-generated-wfta-run
      p epsilon grid-depth precision-fuel xs)
     (zcs-generated-direct-run
      p epsilon grid-depth precision-fuel xs))))
  :hints
  (("Goal"
    :use
    ((:instance zcr-generated-primitive-root-is-field-element)
     (:instance zcr-generated-primitive-root-is-nonzero)
     (:instance zcr-generated-primitive-root-has-full-order)
     (:instance zcq-generated-primitive-root-wfta-correct
                (generator (zcr-generated-primitive-root p))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcs-generated-wfta-certificatep
       zcs-generated-wfta-run
       zcs-generated-direct-run)))))
