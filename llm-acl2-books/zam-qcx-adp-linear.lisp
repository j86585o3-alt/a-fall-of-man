; Rational-complex specialization of algebraic dynamic programming.

(in-package "ACL2")

(include-book "zaa-algebraic-dynamic-programming")
(include-book "zak-rational-dft-core")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Rational complex numbers form a commutative semiring.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun qap-valuep (x) (qcx-rationalp x))
(defun qap-zero () (qcx-zero))
(defun qap-one () (qcx-one))
(defun qap-plus (x y) (qcx-add x y))
(defun qap-times (x y) (qcx-mul x y))

(defthm qcx-rationalp-of-zero
  (qcx-rationalp (qcx-zero)))

(defthm qcx-rationalp-of-one
  (qcx-rationalp (qcx-one)))

(defthm qcx-rationalp-of-mul
  (implies (and (qcx-rationalp x)
                (qcx-rationalp y))
           (qcx-rationalp (qcx-mul x y))))

(defthm qcx-add-left-identity
  (implies (qcx-rationalp x)
           (equal (qcx-add (qcx-zero) x) x)))

(defthm qcx-add-right-identity
  (implies (qcx-rationalp x)
           (equal (qcx-add x (qcx-zero)) x)))

(defthm qcx-mul-commutative
  (equal (qcx-mul x y)
         (qcx-mul y x)))

(defthm qcx-mul-associative
  (equal (qcx-mul (qcx-mul x y) z)
         (qcx-mul x (qcx-mul y z))))

(defthm qcx-mul-left-identity
  (implies (qcx-rationalp x)
           (equal (qcx-mul (qcx-one) x) x)))

(defthm qcx-mul-right-identity
  (implies (qcx-rationalp x)
           (equal (qcx-mul x (qcx-one)) x)))

(defthm qcx-mul-zero-left
  (equal (qcx-mul (qcx-zero) x)
         (qcx-zero)))

(defthm qcx-mul-zero-right
  (equal (qcx-mul x (qcx-zero))
         (qcx-zero)))

(defthm qcx-add-distributes-over-mul-right
  (equal (qcx-mul (qcx-add x y) z)
         (qcx-add (qcx-mul x z)
                  (qcx-mul y z)))
  :hints (("Goal"
           :use ((:instance qcx-mul-distributes-over-add
                            (x z) (y x) (z y))
                 (:instance qcx-mul-commutative
                            (x z) (y (qcx-add x y)))
                 (:instance qcx-mul-commutative (x z) (y x))
                 (:instance qcx-mul-commutative (x z) (y y))))))

(defthm qap-valuep-of-zero
  (qap-valuep (qap-zero)))
(defthm qap-valuep-of-one
  (qap-valuep (qap-one)))
(defthm qap-valuep-of-plus
  (implies (and (qap-valuep x) (qap-valuep y))
           (qap-valuep (qap-plus x y))))
(defthm qap-valuep-of-times
  (implies (and (qap-valuep x) (qap-valuep y))
           (qap-valuep (qap-times x y))))
(defthm qap-plus-associative
  (equal (qap-plus (qap-plus x y) z)
         (qap-plus x (qap-plus y z))))
(defthm qap-plus-commutative
  (equal (qap-plus x y) (qap-plus y x)))
(defthm qap-plus-left-identity
  (implies (qap-valuep x)
           (equal (qap-plus (qap-zero) x) x)))
(defthm qap-plus-right-identity
  (implies (qap-valuep x)
           (equal (qap-plus x (qap-zero)) x)))
(defthm qap-times-associative
  (equal (qap-times (qap-times x y) z)
         (qap-times x (qap-times y z))))
(defthm qap-times-commutative
  (equal (qap-times x y) (qap-times y x)))
(defthm qap-times-left-identity
  (implies (qap-valuep x)
           (equal (qap-times (qap-one) x) x)))
(defthm qap-times-right-identity
  (implies (qap-valuep x)
           (equal (qap-times x (qap-one)) x)))
(defthm qap-times-zero-left
  (equal (qap-times (qap-zero) x) (qap-zero)))
(defthm qap-times-zero-right
  (equal (qap-times x (qap-zero)) (qap-zero)))
(defthm qap-times-distributes-over-plus-left
  (equal (qap-times x (qap-plus y z))
         (qap-plus (qap-times x y)
                   (qap-times x z))))
(defthm qap-times-distributes-over-plus-right
  (equal (qap-times (qap-plus x y) z)
         (qap-plus (qap-times x z)
                   (qap-times y z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Concrete forward chart evaluator.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun qap-fast-chart-ref (index chart)
  (let ((look (hons-get (nfix index) chart)))
    (if look (cdr look) (qap-zero))))

(defun qap-fast-eval-premises (premises chart)
  (if (endp premises)
      (qap-one)
    (qap-times (qap-fast-chart-ref (car premises) chart)
               (qap-fast-eval-premises (cdr premises) chart))))

(defun qap-fast-eval-rule (rule chart)
  (qap-times (car rule)
             (qap-fast-eval-premises (cdr rule) chart)))

(defun qap-fast-eval-rules (rules chart)
  (if (endp rules)
      (qap-zero)
    (qap-plus (qap-fast-eval-rule (car rules) chart)
              (qap-fast-eval-rules (cdr rules) chart))))

(defun qap-fast-eval-item (item chart)
  (qap-plus (car item)
            (qap-fast-eval-rules (cdr item) chart)))

(defun qap-fast-run-aux (items index chart)
  (if (endp items)
      chart
    (let ((value (qap-fast-eval-item (car items) chart)))
      (qap-fast-run-aux
       (cdr items)
       (1+ (nfix index))
       (hons-acons (nfix index) value chart)))))

(defun qap-fast-run (program)
  (qap-fast-run-aux program 0 nil))

(defun qap-fast-value (index program)
  (let* ((chart (qap-fast-run program))
         (value (qap-fast-chart-ref index chart)))
    (prog2$ (fast-alist-free chart) value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Concrete validity and derivation-tree semantics.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun qap-rule-validp (rule bound)
  (and (consp rule)
       (qap-valuep (car rule))
       (adp-premises-belowp (cdr rule) bound)))

(defun qap-rules-validp (rules bound)
  (if (endp rules)
      t
    (and (qap-rule-validp (car rules) bound)
         (qap-rules-validp (cdr rules) bound))))

(defun qap-item-validp (item bound)
  (and (consp item)
       (qap-valuep (car item))
       (qap-rules-validp (cdr item) bound)))

(defun qap-prefix-validp (n program)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (and (qap-prefix-validp (1- n) program)
         (qap-item-validp (nth (1- n) program) (1- n)))))

(defun qap-program-validp (program)
  (qap-prefix-validp (len program) program))

(mutual-recursion
 (defun qap-denote-item (index program)
   (declare
    (xargs
     :measure
     (two-nats-measure
      (nfix index)
      (+ 1 (acl2-count (nth (nfix index) program))))))
   (let ((item (nth (nfix index) program)))
     (if (consp item)
         (qap-plus (car item)
                   (qap-denote-rules (cdr item) (nfix index) program))
       (qap-zero))))

 (defun qap-denote-rules (rules bound program)
   (declare
    (xargs
     :measure
     (two-nats-measure (nfix bound) (+ 1 (acl2-count rules)))))
   (if (endp rules)
       (qap-zero)
     (qap-plus (qap-denote-rule (car rules) bound program)
               (qap-denote-rules (cdr rules) bound program))))

 (defun qap-denote-rule (rule bound program)
   (declare
    (xargs
     :measure
     (two-nats-measure (nfix bound) (+ 1 (acl2-count rule)))))
   (if (consp rule)
       (qap-times (car rule)
                  (qap-denote-premises (cdr rule) bound program))
     (qap-zero)))

 (defun qap-denote-premises (premises bound program)
   (declare
    (xargs
     :measure
     (two-nats-measure (nfix bound) (+ 1 (acl2-count premises)))))
   (if (endp premises)
       (qap-one)
     (if (and (natp (car premises))
              (< (car premises) (nfix bound)))
         (qap-times
          (qap-denote-item (car premises) program)
          (qap-denote-premises (cdr premises) bound program))
       (qap-zero)))))

(defthm qap-denote-item-when-not-consp
  (implies (not (consp (nth index program)))
           (equal (qap-denote-item index program)
                  (qap-zero)))
  :hints (("Goal" :in-theory (enable qap-denote-item))))

(defthm qap-fast-value-correct
  (implies (and (qap-program-validp program)
                (natp index)
                (< index (len program)))
           (equal (qap-fast-value index program)
                  (qap-denote-item index program)))
  :hints
  (("Goal"
    :in-theory nil
    :use
    ((:functional-instance
      adp-fast-value-correct
      (adp-valuep qap-valuep)
      (adp-zero qap-zero)
      (adp-one qap-one)
      (adp-plus qap-plus)
      (adp-times qap-times)
      (adp-rule-validp qap-rule-validp)
      (adp-rules-validp qap-rules-validp)
      (adp-item-validp qap-item-validp)
      (adp-prefix-validp qap-prefix-validp)
      (adp-program-validp qap-program-validp)
      (adp-fast-chart-ref qap-fast-chart-ref)
      (adp-fast-eval-premises qap-fast-eval-premises)
      (adp-fast-eval-rule qap-fast-eval-rule)
      (adp-fast-eval-rules qap-fast-eval-rules)
      (adp-fast-eval-item qap-fast-eval-item)
      (adp-fast-run-aux qap-fast-run-aux)
      (adp-fast-run qap-fast-run)
      (adp-fast-value qap-fast-value)
      (adp-denote-item qap-denote-item)
      (adp-denote-rules qap-denote-rules)
      (adp-denote-rule qap-denote-rule)
      (adp-denote-premises qap-denote-premises))))
   (and stable-under-simplificationp
        '(:in-theory
          (enable qap-rule-validp
                  qap-rules-validp
                  qap-item-validp
                  qap-prefix-validp
                  qap-program-validp
                  qap-fast-chart-ref
                  qap-fast-eval-premises
                  qap-fast-eval-rule
                  qap-fast-eval-rules
                  qap-fast-eval-item
                  qap-fast-run-aux
                  qap-fast-run
                  qap-fast-value
                  qap-denote-item
                  qap-denote-rules
                  qap-denote-rule
                  qap-denote-premises
                  qap-valuep qap-zero qap-one qap-plus qap-times)))))
