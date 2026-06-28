; Compile a rational Fourier dot product into the generic ADP engine.
(in-package "ACL2")
(include-book "zam-qcx-adp-linear")
(include-book "zal-rational-fourier-kernel")

(defun qad-rules (xs weights)
  (if (or (endp xs) (endp weights))
      nil
    (cons (list (qcx-scale (car xs) (car weights)))
          (qad-rules (cdr xs) (cdr weights)))))

(defun qad-output-program (xs weights)
  (list (cons (qcx-zero) (qad-rules xs weights))))

(defun qad-output (xs weights)
  (qap-fast-value 0 (qad-output-program xs weights)))

(defthm qap-rules-validp-of-qad-rules
  (implies (and (rational-listp xs)
                (qcx-list-rationalp weights))
           (qap-rules-validp (qad-rules xs weights) 0))
  :hints (("Goal"
           :induct (qad-rules xs weights)
           :in-theory (enable qad-rules qap-rules-validp qap-rule-validp
                              adp-premises-belowp qap-valuep))))

(defthm qap-program-validp-of-qad-output-program
  (implies (and (rational-listp xs)
                (qcx-list-rationalp weights))
           (qap-program-validp (qad-output-program xs weights)))
  :hints (("Goal"
           :use ((:instance qap-rules-validp-of-qad-rules))
           :in-theory (e/d (qad-output-program qap-program-validp
                                               qap-prefix-validp
                                               qap-item-validp
                                               qap-valuep qap-zero)
                              (qad-rules
                               qap-rules-validp
                               qap-rules-validp-of-qad-rules)))))

(defthm qap-denote-rules-of-qad-rules-general
  (implies (and (rational-listp xs)
                (qcx-list-rationalp weights))
           (equal (qap-denote-rules (qad-rules xs weights) bound program)
                  (qcx-dot xs weights)))
  :hints (("Goal"
           :induct (qad-rules xs weights)
           :in-theory (enable qad-rules qap-denote-rules
                              qap-denote-rule qap-denote-premises qap-plus
                              qap-times qap-one qap-zero qcx-dot))))

(defthm qap-denote-rules-of-qad-rules
  (implies (and (rational-listp xs)
                (qcx-list-rationalp weights))
           (equal (qap-denote-rules (qad-rules xs weights) 0
                                    (qad-output-program xs weights))
                  (qcx-dot xs weights)))
  :hints (("Goal"
           :use ((:instance qap-denote-rules-of-qad-rules-general
                            (bound 0)
                            (program (qad-output-program xs weights))))
           :in-theory nil)))

(defthm qap-denote-item-of-qad-output-program
  (implies (and (rational-listp xs)
                (qcx-list-rationalp weights))
           (equal (qap-denote-item 0 (qad-output-program xs weights))
                  (qcx-dot xs weights)))
  :hints (("Goal"
           :use ((:instance qap-denote-rules-of-qad-rules))
           :in-theory (enable qap-denote-item qad-output-program
                              qap-plus qap-zero))))

(defthm qad-output-equals-qcx-dot
  (implies (and (rational-listp xs)
                (qcx-list-rationalp weights))
           (equal (qad-output xs weights) (qcx-dot xs weights)))
  :hints (("Goal"
           :use ((:instance qap-fast-value-correct
                            (index 0)
                            (program (qad-output-program xs weights)))
                 (:instance qap-program-validp-of-qad-output-program)
                 (:instance qap-denote-item-of-qad-output-program))
           :in-theory (enable qad-output))))

(defun qad-dft-output (xs k table)
  (qad-output xs (qcx-fourier-row k (len xs) table)))

(defthm qad-dft-output-equals-direct
  (implies (and (rational-listp xs)
                (qcx-list-rationalp table))
           (equal (qad-dft-output xs k table)
                  (qcx-direct-dft-output xs k table)))
  :hints (("Goal"
           :use ((:instance qad-output-equals-qcx-dot
                            (weights (qcx-fourier-row k (len xs) table))))
           :in-theory (enable qad-dft-output qcx-direct-dft-output))))

(defun qad-dft-aux (count k xs table)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (qad-dft-output xs k table)
          (qad-dft-aux (1- count) (1+ (nfix k)) xs table))))

(defun qad-dft (xs table)
  (qad-dft-aux (len xs) 0 xs table))

(defthm qad-dft-aux-equals-direct-aux
  (implies (and (rational-listp xs)
                (qcx-list-rationalp table))
           (equal (qad-dft-aux count k xs table)
                  (qcx-direct-dft-aux count k xs table)))
  :hints (("Goal"
           :induct (qad-dft-aux count k xs table)
           :in-theory (enable qad-dft-aux qcx-direct-dft-aux))))

(defthm qad-dft-equals-direct-dft
  (implies (and (rational-listp xs)
                (qcx-list-rationalp table))
           (equal (qad-dft xs table) (qcx-direct-dft xs table)))
  :hints (("Goal"
           :use ((:instance qad-dft-aux-equals-direct-aux
                            (count (len xs)) (k 0)))
           :in-theory (enable qad-dft qcx-direct-dft))))

(defthm qad-dft-output-error-bound
  (implies (and (rational-listp xs)
                (qcx-list-rationalp a)
                (qcx-list-rationalp b)
                (qcx-table-closep eps a b)
                (rationalp eps)
                (<= 0 eps))
           (<= (qcx-dist (qad-dft-output xs k a)
                          (qad-dft-output xs k b))
               (* eps (rational-list-l1 xs))))
  :hints (("Goal"
           :use ((:instance qcx-direct-dft-output-error-bound))
           :in-theory (disable qcx-direct-dft-output-error-bound)))
  :rule-classes :linear)
