; The generated length-67 WFTA over generated rational cyclic twiddle tables.
(in-package "ACL2")
(include-book "zbl-generated-rader67")
(include-book "zbb-rational-cyclic-twiddle-system")

(defthm gr67-nfix-is-67
  (equal (nfix 67) 67))

(defthm gr67-rational-table-run-is-compiled-dft
  (implies
   (and (rational-listp xs)
        (equal (len xs) 67)
        (rationalp tangent))
   (equal
    (rwd-rational-input-run
     67
     (gr67-input-indices)
     (gr67-kernel-indices)
     (gr67-small-terms)
     (gr67-small-posts)
     xs
     (rct-twiddle-table 67 other-chart tangent))
    (rwd-direct-outputs
     (rwd-compile-outputs (gr67-output-indices))
     67
     (qcx-realify xs)
     (rct-twiddle-table 67 other-chart tangent))))
  :hints
  (("Goal"
    :use
    ((:instance gr67-generated-wfta-certificate)
     (:instance gr67-positive-lengths)
     (:instance rct-rwd-generated-table-correct
                (p 67)
                (input-indices (gr67-input-indices))
                (kernel-indices (gr67-kernel-indices))
                (output-indices (gr67-output-indices))
                (small-terms (gr67-small-terms))
                (small-posts (gr67-small-posts))))
    :in-theory '(gr67-nfix-is-67))))

(defthm gr67-rational-table-run-is-length-67-dft
  (implies
   (and (rational-listp xs)
        (equal (len xs) 67)
        (rationalp tangent))
   (equal
    (rwd-rational-input-run
     67
     (gr67-input-indices)
     (gr67-kernel-indices)
     (gr67-small-terms)
     (gr67-small-posts)
     xs
     (rct-twiddle-table 67 other-chart tangent))
    (rwd-direct-outputs
     (rwd-output-order (gr67-output-indices))
     67
     (qcx-realify xs)
     (rct-twiddle-table 67 other-chart tangent))))
  :hints
  (("Goal"
    :use ((:instance gr67-rational-table-run-is-compiled-dft))
    :in-theory '(gr67-compiled-output-order))))

(defthm gr67-rational-parameter-builds-twiddle-system
  (implies
   (rct-parameter-certificatep
    67 epsilon separation other-chart tangent)
   (rct-twiddle-systemp
    67 epsilon separation
    (rct-rational-unit other-chart tangent)
    (rct-twiddle-table 67 other-chart tangent)))
  :hints
  (("Goal"
    :use
    ((:instance rct-rational-parameter-builder-correct
                (n 67)))
    :in-theory nil)))

(defthm gr67-certified-rational-wfta-is-length-67-dft
  (implies
   (and
    (rct-parameter-certificatep
     67 epsilon separation other-chart tangent)
    (rational-listp xs)
    (equal (len xs) 67))
   (and
    (rct-twiddle-systemp
     67 epsilon separation
     (rct-rational-unit other-chart tangent)
     (rct-twiddle-table 67 other-chart tangent))
    (equal
     (rwd-rational-input-run
      67
      (gr67-input-indices)
      (gr67-kernel-indices)
      (gr67-small-terms)
      (gr67-small-posts)
      xs
      (rct-twiddle-table 67 other-chart tangent))
     (rwd-direct-outputs
      (rwd-output-order (gr67-output-indices))
      67
      (qcx-realify xs)
      (rct-twiddle-table 67 other-chart tangent)))))
  :hints
  (("Goal"
    :use
    ((:instance gr67-rational-parameter-builds-twiddle-system)
     (:instance gr67-rational-table-run-is-length-67-dft))
    :in-theory '(rct-parameter-certificatep))))
