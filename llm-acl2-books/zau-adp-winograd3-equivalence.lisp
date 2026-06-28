; The ADP-built three-point Winograd transform equals the standalone compiler.
(in-package "ACL2")
(include-book "zas-rader-winograd3")
(include-book "zat-adp-winograd-bank")

(defthm rw3-compiled-terms-valid
  (wbc-terms-validp
   3
   (rwd-compile-terms 3
                      *rw3-input-indices*
                      *rw3-kernel-indices*
                      *wbc2-terms*))
  :hints (("Goal"
           :in-theory
           (enable rwd-compile-terms rwd-full-terms
                   rwd-dc-term rwd-base-term rwd-lift-terms
                   rwd-lift-row rwd-lift-row-aux rwd-coefficient-at
                   rwd-constant-row-aux rwd-unit-row rwd-unit-row-aux
                   wbc-terms-validp rational-rowp))))

(defthm rw3-compiled-posts-rational
  (qwb-posts-rationalp
   (rwd-compile-posts *wbc2-terms* *rw3-small-posts*))
  :hints (("Goal"
           :in-theory
           (enable rwd-compile-posts rwd-full-posts
                   rwd-dc-post rwd-zero-row rwd-constant-row-aux
                   rwd-nonzero-posts rwd-nonzero-post
                   qwb-posts-rationalp))))

(defthm adp-rw3-equals-standalone-rw3
  (implies (and (qcx-vectorp 3 xs)
                (qcx-vectorp 3 table))
           (equal
            (qwb-rwd-run 3
                         *rw3-input-indices*
                         *rw3-kernel-indices*
                         *wbc2-terms*
                         *rw3-small-posts*
                         xs table)
            (rwd-run 3
                     *rw3-input-indices*
                     *rw3-kernel-indices*
                     *wbc2-terms*
                     *rw3-small-posts*
                     xs table)))
  :hints (("Goal"
           :use ((:instance rw3-compiled-terms-valid)
                 (:instance rw3-compiled-posts-rational)
                 (:instance qwb-rwd-run-equals-rwd-run
                            (p 3)
                            (input-indices *rw3-input-indices*)
                            (kernel-indices *rw3-kernel-indices*)
                            (small-terms *wbc2-terms*)
                            (small-posts *rw3-small-posts*)))
           :in-theory nil)))

(defthm adp-rw3-equals-canonical-rational-dft
  (implies (and (qcx-vectorp 3 xs)
                (qcx-vectorp 3 table))
           (equal
            (qwb-rwd-run 3
                         *rw3-input-indices*
                         *rw3-kernel-indices*
                         *wbc2-terms*
                         *rw3-small-posts*
                         xs table)
            (rwd-direct-outputs '(0 1 2) 3 xs table)))
  :hints (("Goal"
           :use ((:instance adp-rw3-equals-standalone-rw3)
                 (:instance rw3-transform-correct))
           :in-theory nil)))
