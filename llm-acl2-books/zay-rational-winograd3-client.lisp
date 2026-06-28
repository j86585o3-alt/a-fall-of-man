; A compact rational-only client for the certified three-point Winograd DFT.
;
; Samples are ACL2 rationals.  Twiddles and outputs are rational pairs.
; The client requests an output tolerance and obtains a sufficient rational
; pointwise tolerance for the supplied twiddle table.

(in-package "ACL2")
(include-book "zax-rational-winograd-interface")

(defun rw3-rational-winograd (xs table)
  (rwd-rational-input-run
   3
   *rw3-input-indices*
   *rw3-kernel-indices*
   *wbc2-terms*
   *rw3-small-posts*
   xs table))

(defun rw3-rational-adp (xs table)
  (qwb-rational-input-run
   3
   *rw3-input-indices*
   *rw3-kernel-indices*
   *wbc2-terms*
   *rw3-small-posts*
   xs table))

(defthm rw3-rational-winograd-correct
  (implies (and (rational-listp xs)
                (equal (len xs) 3)
                (qcx-vectorp 3 table))
           (equal
            (rw3-rational-winograd xs table)
            (rwd-direct-outputs '(0 1 2) 3 (qcx-realify xs) table)))
  :hints (("Goal"
           :use ((:instance rw3-compiler-certificate)
                 (:instance rw3-output-order)
                 (:instance rwd-rational-input-run-correct
                            (p 3)
                            (input-indices *rw3-input-indices*)
                            (kernel-indices *rw3-kernel-indices*)
                            (output-indices *rw3-output-indices*)
                            (small-terms *wbc2-terms*)
                            (small-posts *rw3-small-posts*)))
           :in-theory '(rw3-rational-winograd nfix posp))))

(defthm rw3-rational-adp-equals-winograd
  (implies (and (rational-listp xs)
                (equal (len xs) 3)
                (qcx-vectorp 3 table))
           (equal (rw3-rational-adp xs table)
                  (rw3-rational-winograd xs table)))
  :hints (("Goal"
           :use ((:instance rw3-compiled-terms-valid)
                 (:instance rw3-compiled-posts-rational)
                 (:instance qwb-rational-input-run-equals-rwd-rational-input-run
                            (p 3)
                            (input-indices *rw3-input-indices*)
                            (kernel-indices *rw3-kernel-indices*)
                            (small-terms *wbc2-terms*)
                            (small-posts *rw3-small-posts*)))
           :in-theory '(rw3-rational-adp rw3-rational-winograd nfix posp))))

(defthm rw3-rational-adp-correct
  (implies (and (rational-listp xs)
                (equal (len xs) 3)
                (qcx-vectorp 3 table))
           (equal
            (rw3-rational-adp xs table)
            (rwd-direct-outputs '(0 1 2) 3 (qcx-realify xs) table)))
  :hints (("Goal"
           :use ((:instance rw3-rational-adp-equals-winograd)
                 (:instance rw3-rational-winograd-correct))
           :in-theory nil)))

(defthm rw3-rational-winograd-requested-output-tolerance
  (implies
   (and (rational-listp xs)
        (equal (len xs) 3)
        (qcx-vectorp 3 a)
        (qcx-vectorp 3 b)
        (rationalp output-eps)
        (<= 0 output-eps)
        (qcx-table-closep
         (rw-table-epsilon-for-output output-eps xs) a b))
   (dft-output-closep
    output-eps
    (rw3-rational-winograd xs a)
    (rw3-rational-winograd xs b)))
  :hints (("Goal"
           :use ((:instance rw3-compiler-certificate)
                 (:instance rwd-rational-input-run-requested-output-tolerance
                            (p 3)
                            (input-indices *rw3-input-indices*)
                            (kernel-indices *rw3-kernel-indices*)
                            (output-indices *rw3-output-indices*)
                            (small-terms *wbc2-terms*)
                            (small-posts *rw3-small-posts*)))
           :in-theory '(rw3-rational-winograd nfix posp))))

(defthm rw3-rational-adp-requested-output-tolerance
  (implies
   (and (rational-listp xs)
        (equal (len xs) 3)
        (qcx-vectorp 3 a)
        (qcx-vectorp 3 b)
        (rationalp output-eps)
        (<= 0 output-eps)
        (qcx-table-closep
         (rw-table-epsilon-for-output output-eps xs) a b))
   (dft-output-closep
    output-eps
    (rw3-rational-adp xs a)
    (rw3-rational-adp xs b)))
  :hints (("Goal"
           :use ((:instance rw3-compiler-certificate)
                 (:instance rw3-compiled-terms-valid)
                 (:instance rw3-compiled-posts-rational)
                 (:instance qwb-rational-input-run-requested-output-tolerance
                            (p 3)
                            (input-indices *rw3-input-indices*)
                            (kernel-indices *rw3-kernel-indices*)
                            (output-indices *rw3-output-indices*)
                            (small-terms *wbc2-terms*)
                            (small-posts *rw3-small-posts*)))
           :in-theory '(rw3-rational-adp nfix posp))))

(defthm rw3-rational-client-uses-five-complex-products
  (equal (rwd-complex-product-count *wbc2-terms*) 5)
  :hints (("Goal" :use ((:instance rw3-complex-product-count-is-five))
           :in-theory nil)))
