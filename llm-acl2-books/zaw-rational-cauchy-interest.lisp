; An optional rational-only regular-Cauchy sketch.
;
; This book is intentionally not part of the Winograd interface.  It records
; reusable facts about finite towers of rational-pair approximants, without
; claiming that ACL2 contains a completed real or complex number.

(in-package "ACL2")
(include-book "zav-winograd-direct-equivalence")

(defun rcf-radius (level)
  (declare (xargs :measure (nfix level)))
  (if (zp level)
      1
    (* 1/2 (rcf-radius (1- level)))))

(defthm rationalp-of-rcf-radius
  (rationalp (rcf-radius level))
  :rule-classes :type-prescription)

(defthm rcf-radius-positive
  (< 0 (rcf-radius level))
  :rule-classes :linear)

(defthm rcf-radius-of-successor
  (implies (natp level)
           (equal (rcf-radius (1+ level))
                  (* 1/2 (rcf-radius level))))
  :hints (("Goal" :expand ((rcf-radius (1+ level))))))

(defthm twice-rcf-radius-of-successor
  (implies (natp level)
           (equal (+ (rcf-radius (1+ level))
                     (rcf-radius (1+ level)))
                  (rcf-radius level)))
  :hints (("Goal" :use ((:instance rcf-radius-of-successor)))))

(defthm qcx-dist-triangle
  (implies (and (qcx-rationalp a)
                (qcx-rationalp b)
                (qcx-rationalp c))
           (<= (qcx-dist a c)
               (+ (qcx-dist a b)
                  (qcx-dist b c))))
  :hints (("Goal"
           :in-theory (enable qcx-dist qcx-l1 qcx-sub qcx-add qcx-neg
                              qcx-re qcx-im abs)))
  :rule-classes :linear)

(defthm qcx-table-closep-reflexive
  (implies (and (qcx-list-rationalp xs)
                (rationalp eps)
                (<= 0 eps))
           (qcx-table-closep eps xs xs))
  :hints (("Goal"
           :induct (qcx-list-rationalp xs)
           :in-theory (enable qcx-table-closep qcx-dist qcx-sub qcx-add
                              qcx-neg qcx-l1 qcx-re qcx-im))))

(defun rcf-three-list-induct (xs ys zs)
  (if (or (endp xs) (endp ys) (endp zs))
      (list xs ys zs)
    (rcf-three-list-induct (cdr xs) (cdr ys) (cdr zs))))

(defthm qcx-table-closep-transitive
  (implies (and (qcx-list-rationalp xs)
                (qcx-list-rationalp ys)
                (qcx-list-rationalp zs)
                (qcx-table-closep eps xs ys)
                (qcx-table-closep delta ys zs)
                (rationalp eps)
                (rationalp delta)
                (<= 0 eps)
                (<= 0 delta))
           (qcx-table-closep (+ eps delta) xs zs))
  :hints (("Goal"
           :induct (rcf-three-list-induct xs ys zs)
           :in-theory (enable rcf-three-list-induct qcx-table-closep))))

(defun rcf-towerp (n level tower)
  (declare (xargs :measure (len tower)))
  (if (endp tower)
      t
    (and (qcx-vectorp n (car tower))
         (or (endp (cdr tower))
             (and (qcx-table-closep
                   (rcf-radius (1+ (nfix level)))
                   (car tower)
                   (cadr tower))
                  (rcf-towerp n (1+ (nfix level)) (cdr tower)))))))

(defun rcf-stage (stage tower)
  (if (zp stage)
      (car tower)
    (rcf-stage (1- stage) (cdr tower))))

(defthm rcf-stage-zero
  (equal (rcf-stage 0 tower) (car tower)))

(defun rcf-tower-stage-induct (stage level tower)
  (declare (xargs :measure (nfix stage)))
  (if (zp stage)
      (list level tower)
    (rcf-tower-stage-induct (1- stage)
                            (1+ (nfix level))
                            (cdr tower))))

(defthm qcx-vectorp-of-rcf-stage
  (implies (and (rcf-towerp n level tower)
                (natp stage)
                (< stage (len tower)))
           (qcx-vectorp n (rcf-stage stage tower)))
  :hints (("Goal"
           :induct (rcf-tower-stage-induct stage level tower)
           :in-theory (enable rcf-tower-stage-induct rcf-stage rcf-towerp))))

(defthm qcx-list-rationalp-of-rcf-stage
  (implies (and (rcf-towerp n level tower)
                (natp stage)
                (< stage (len tower)))
           (qcx-list-rationalp (rcf-stage stage tower)))
  :hints (("Goal"
           :use ((:instance qcx-vectorp-of-rcf-stage)
                 (:instance qcx-vectorp-implies-list-rationalp
                            (table (rcf-stage stage tower))))
           :in-theory nil)))
