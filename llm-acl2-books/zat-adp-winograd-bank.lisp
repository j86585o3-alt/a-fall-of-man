; Compile a shared Winograd product bank into the generic ADP evaluator.
(in-package "ACL2")
(include-book "zam-qcx-adp-linear")
(include-book "zar-rader-winograd-dft")

(defun qwb-rules (products post)
  (if (or (endp products) (endp post))
      nil
    (cons (list (qcx-scale (car post) (car products)))
          (qwb-rules (cdr products) (cdr post)))))

(defun qwb-output-program (products post)
  (list (cons (qcx-zero) (qwb-rules products post))))

(defun qwb-output (products post)
  (qap-fast-value 0 (qwb-output-program products post)))

(defthm qap-rules-validp-of-qwb-rules
  (implies (and (qcx-list-rationalp products)
                (rational-listp post))
           (qap-rules-validp (qwb-rules products post) 0))
  :hints (("Goal"
           :induct (qwb-rules products post)
           :in-theory (enable qwb-rules qap-rules-validp
                              qap-rule-validp adp-premises-belowp
                              qap-valuep))))

(defthm qap-program-validp-of-qwb-output-program
  (implies (and (qcx-list-rationalp products)
                (rational-listp post))
           (qap-program-validp (qwb-output-program products post)))
  :hints (("Goal"
           :use ((:instance qap-rules-validp-of-qwb-rules))
           :in-theory (e/d (qwb-output-program qap-program-validp
                                               qap-prefix-validp
                                               qap-item-validp
                                               qap-valuep qap-zero)
                              (qwb-rules qap-rules-validp
                               qap-rules-validp-of-qwb-rules)))))

(defthm qap-denote-rules-of-qwb-rules
  (implies (and (qcx-list-rationalp products)
                (rational-listp post))
           (equal (qap-denote-rules (qwb-rules products post)
                                    bound program)
                  (wbc-linear post products)))
  :hints (("Goal"
           :induct (qwb-rules products post)
           :in-theory (enable qwb-rules qap-denote-rules
                              qap-denote-rule qap-denote-premises
                              qap-plus qap-times qap-one qap-zero
                              wbc-linear))))

(defthm qap-denote-item-of-qwb-output-program
  (implies (and (qcx-list-rationalp products)
                (rational-listp post))
           (equal (qap-denote-item 0 (qwb-output-program products post))
                  (wbc-linear post products)))
  :hints (("Goal"
           :use ((:instance qap-denote-rules-of-qwb-rules
                            (bound 0)
                            (program (qwb-output-program products post))))
           :in-theory (enable qap-denote-item qwb-output-program
                              qap-plus qap-zero))))

(defthm qwb-output-equals-wbc-post-output
  (implies (and (qcx-list-rationalp products)
                (rational-listp post))
           (equal (qwb-output products post)
                  (wbc-post-output post products)))
  :hints (("Goal"
           :use ((:instance qap-fast-value-correct
                            (index 0)
                            (program (qwb-output-program products post)))
                 (:instance qap-program-validp-of-qwb-output-program)
                 (:instance qap-denote-item-of-qwb-output-program))
           :in-theory (enable qwb-output wbc-post-output))))

(defun qwb-posts-rationalp (posts)
  (if (endp posts)
      t
    (and (rational-listp (car posts))
         (qwb-posts-rationalp (cdr posts)))))

(defun qwb-bank-outputs (posts products)
  (if (endp posts)
      nil
    (cons (qwb-output products (car posts))
          (qwb-bank-outputs (cdr posts) products))))

(defthm qwb-bank-outputs-equal-post-bank-output
  (implies (and (qcx-list-rationalp products)
                (qwb-posts-rationalp posts))
           (equal (qwb-bank-outputs posts products)
                  (wbc-post-bank-output posts products)))
  :hints (("Goal"
           :induct (qwb-bank-outputs posts products)
           :in-theory (enable qwb-bank-outputs
                              wbc-post-bank-output
                              qwb-posts-rationalp))))

(defthm qcx-list-rationalp-of-wbc-product-bank
  (implies (and (wbc-terms-validp n terms)
                (qcx-vectorp n xs)
                (qcx-vectorp n ys))
           (qcx-list-rationalp (wbc-product-bank terms xs ys)))
  :hints (("Goal"
           :induct (wbc-product-bank terms xs ys)
           :in-theory (e/d (wbc-product-bank wbc-terms-validp
                                              qcx-list-rationalp)
                            (qcx-rationalp wbc-linear qcx-mul)))))

(defun qwb-winograd-output (terms posts xs ys)
  (let ((products (wbc-product-bank terms xs ys)))
    (qwb-bank-outputs posts products)))

(defthm qwb-winograd-output-equals-wbc-bank-output
  (implies (and (wbc-terms-validp n terms)
                (qwb-posts-rationalp posts)
                (qcx-vectorp n xs)
                (qcx-vectorp n ys))
           (equal (qwb-winograd-output terms posts xs ys)
                  (wbc-bank-output terms posts xs ys)))
  :hints (("Goal"
           :use ((:instance qwb-bank-outputs-equal-post-bank-output
                            (products (wbc-product-bank terms xs ys)))
                 (:instance qcx-list-rationalp-of-wbc-product-bank))
           :in-theory (enable qwb-winograd-output wbc-bank-output))))

(defun qwb-rwd-run
  (p input-indices kernel-indices small-terms small-posts xs table)
  (qwb-winograd-output
   (rwd-compile-terms p input-indices kernel-indices small-terms)
   (rwd-compile-posts small-terms small-posts)
   xs table))

(defthm qwb-rwd-run-is-winograd-output
  (equal
   (qwb-rwd-run p input-indices kernel-indices
                small-terms small-posts xs table)
   (qwb-winograd-output
    (rwd-compile-terms p input-indices kernel-indices small-terms)
    (rwd-compile-posts small-terms small-posts)
    xs table))
  :hints (("Goal" :in-theory (enable qwb-rwd-run))))

(defthm qwb-rwd-run-equals-rwd-run
  (implies
   (and (wbc-terms-validp
         p (rwd-compile-terms p input-indices kernel-indices small-terms))
        (qwb-posts-rationalp (rwd-compile-posts small-terms small-posts))
        (qcx-vectorp p xs)
        (qcx-vectorp p table))
   (equal (qwb-rwd-run p input-indices kernel-indices
                       small-terms small-posts xs table)
          (rwd-run p input-indices kernel-indices
                   small-terms small-posts xs table)))
  :hints (("Goal"
           :use ((:instance qwb-rwd-run-is-winograd-output)
                 (:instance rwd-run-is-bank-output
                            (p p)
                            (input-indices input-indices)
                            (kernel-indices kernel-indices)
                            (small-terms small-terms)
                            (small-posts small-posts)
                            (xs xs) (table table))
                 (:instance qwb-winograd-output-equals-wbc-bank-output
                            (n p)
                            (terms (rwd-compile-terms
                                    p input-indices kernel-indices small-terms))
                            (posts (rwd-compile-posts
                                    small-terms small-posts))
                            (ys table)))
           :in-theory nil)))
