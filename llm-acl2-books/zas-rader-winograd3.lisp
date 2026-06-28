; A fully checked three-point Rader/Winograd rational DFT.
(in-package "ACL2")
(include-book "zap-winograd-cyclic2")
(include-book "zar-rader-winograd-dft")

(defconst *rw3-input-indices* '(1 2))
(defconst *rw3-kernel-indices* '(1 2))
(defconst *rw3-output-indices* '(1 2))
(defconst *rw3-small-posts* (list *wbc2-post0* *wbc2-post1*))

(defthm rw3-compiler-certificate
  (rwd-compiled-certifiesp
   3
   *rw3-input-indices*
   *rw3-kernel-indices*
   *rw3-output-indices*
   *wbc2-terms*
   *rw3-small-posts*)
  :hints (("Goal"
           :in-theory
           (enable rwd-compiled-certifiesp
                   rwd-bank-certifiesp rwd-bank-certifies-aux
                   rwd-plan-certifies-outputp
                   rwd-compile-outputs rwd-output-order
                   rwd-compile-terms rwd-full-terms
                   rwd-dc-term rwd-base-term rwd-lift-terms
                   rwd-lift-row rwd-lift-row-aux rwd-coefficient-at
                   rwd-constant-row-aux rwd-unit-row rwd-unit-row-aux
                   rwd-compile-posts rwd-full-posts rwd-dc-post
                   rwd-zero-row rwd-nonzero-posts rwd-nonzero-post
                   wbc-plan-validp wbc-terms-validp rational-rowp
                   wbc-plan-matrix wbc-term-matrix wbc-matrix-scale
                   wbc-outer wbc-row-scale wbc-matrix-add wbc-row-add
                   rwd-fourier-matrix rwd-fourier-matrix-aux
                   rwd-fourier-row-aux))))

(defthm rw3-output-order
  (equal (rwd-compile-outputs *rw3-output-indices*)
         '(0 1 2))
  :hints (("Goal"
           :in-theory (enable rwd-compile-outputs rwd-output-order))))

(defthm rw3-transform-correct
  (implies (and (qcx-vectorp 3 xs)
                (qcx-vectorp 3 table))
           (equal
            (rwd-run 3
                     *rw3-input-indices*
                     *rw3-kernel-indices*
                     *wbc2-terms*
                     *rw3-small-posts*
                     xs table)
            (rwd-direct-outputs '(0 1 2) 3 xs table)))
  :hints (("Goal"
           :use ((:instance rw3-compiler-certificate)
                 (:instance rw3-output-order)
                 (:instance rwd-compiled-transform-correct
                            (p 3)
                            (input-indices *rw3-input-indices*)
                            (kernel-indices *rw3-kernel-indices*)
                            (output-indices *rw3-output-indices*)
                            (small-terms *wbc2-terms*)
                            (small-posts *rw3-small-posts*)))
           :in-theory nil)))

(defthm rw3-complex-product-count-is-five
  (equal (rwd-complex-product-count *wbc2-terms*) 5)
  :hints (("Goal" :in-theory (enable rwd-complex-product-count))))

(defthm rw3-beats-naive-bilinear-product-count
  (< (rwd-complex-product-count *wbc2-terms*) (* 3 3))
  :hints (("Goal" :in-theory (enable rwd-complex-product-count))))
