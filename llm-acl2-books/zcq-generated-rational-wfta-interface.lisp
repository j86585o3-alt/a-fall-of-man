; Resource-bounded proof-producing rational WFTA interface.
; The initial stereographic sign bracket and the bisection precision are
; searched rather than supplied as mathematical witnesses.
(in-package "ACL2")

(include-book "zcp-stereographic-sector-bracket")
(include-book "zcn-bisected-generated-rational-wfta")

(defun zcq-precision-search (remaining current n epsilon lo hi radius)
  (declare (xargs :measure (nfix remaining)
                  :hints (("Goal"
                           :in-theory
                           (union-theories
                            (theory 'minimal-theory)
                            '(nfix zp natp o-p o< o-finp
                              default-less-than-1
                              default-less-than-2
                              default-plus-1
                              default-plus-2))))))
  (if (zp remaining)
      nil
    (if (rts-bisected-twiddle-certificatep
         n epsilon current lo hi radius)
        (cons current t)
      (zcq-precision-search
       (1- remaining) (1+ (nfix current))
       n epsilon lo hi radius))))

(defun zcq-sector-bracket (grid-depth n)
  (rts-sector-bracket-search grid-depth n))

(defun zcq-sector-lo (grid-depth n)
  (rpb-lo (zcq-sector-bracket grid-depth n)))

(defun zcq-sector-hi (grid-depth n)
  (rpb-hi (zcq-sector-bracket grid-depth n)))

(defun zcq-sector-radius (grid-depth n)
  (rts-sector-radius grid-depth n))

(defun zcq-precision-witness
  (precision-fuel grid-depth n epsilon)
  (zcq-precision-search
   precision-fuel 0 n epsilon
   (zcq-sector-lo grid-depth n)
   (zcq-sector-hi grid-depth n)
   (zcq-sector-radius grid-depth n)))

(defun zcq-generated-precision
  (precision-fuel grid-depth n epsilon)
  (if (consp (zcq-precision-witness
              precision-fuel grid-depth n epsilon))
      (car (zcq-precision-witness
            precision-fuel grid-depth n epsilon))
    0))

(defun zcq-generated-certificatep
  (precision-fuel grid-depth n epsilon)
  (and (consp (zcq-sector-bracket grid-depth n))
       (consp (zcq-precision-witness
               precision-fuel grid-depth n epsilon))))

(defun zcq-generated-tangent
  (precision-fuel grid-depth n epsilon)
  (rts-bisected-tangent
   (zcq-generated-precision precision-fuel grid-depth n epsilon)
   n
   (zcq-sector-lo grid-depth n)
   (zcq-sector-hi grid-depth n)))

(defun zcq-generated-twiddle-table
  (precision-fuel grid-depth n epsilon)
  (rct-twiddle-table
   n nil
   (zcq-generated-tangent precision-fuel grid-depth n epsilon)))

(defun zcq-generated-separation
  (precision-fuel grid-depth n epsilon)
  (rts-generated-separation
   n
   (rct-rational-unit
    nil
    (zcq-generated-tangent precision-fuel grid-depth n epsilon))))

(defun zcq-rational-wfta-run
  (p generator epsilon grid-depth precision-fuel xs)
  (rwd-rational-input-run
   p
   (rgi-generated-inputs p generator)
   (rgi-generated-kernels p generator)
   (tc-plan-terms (1- (nfix p)))
   (tc-plan-posts (1- (nfix p)))
   xs
   (zcq-generated-twiddle-table
    precision-fuel grid-depth p epsilon)))

(defun zcq-rational-direct-run
  (p generator epsilon grid-depth precision-fuel xs)
  (rwd-direct-outputs
   (rwd-output-order (rgi-generated-outputs p generator))
   p
   (qcx-realify xs)
   (zcq-generated-twiddle-table
    precision-fuel grid-depth p epsilon)))

(defthm zcq-precision-search-open
  (implies (not (zp remaining))
           (equal
            (zcq-precision-search
             remaining current n epsilon lo hi radius)
            (if (rts-bisected-twiddle-certificatep
                 n epsilon current lo hi radius)
                (cons current t)
              (zcq-precision-search
               (1- remaining) (1+ (nfix current))
               n epsilon lo hi radius))))
  :hints (("Goal"
           :expand ((zcq-precision-search
                     remaining current n epsilon lo hi radius))
           :in-theory (theory 'minimal-theory))))

(defthm zcq-precision-search-when-zp
  (implies (zp remaining)
           (equal (zcq-precision-search
                   remaining current n epsilon lo hi radius)
                  nil))
  :hints (("Goal"
           :expand ((zcq-precision-search
                     remaining current n epsilon lo hi radius))
           :in-theory (theory 'minimal-theory))))

(defthm zcq-precision-search-sound
  (implies
   (consp (zcq-precision-search
           remaining current n epsilon lo hi radius))
   (rts-bisected-twiddle-certificatep
    n epsilon
    (car (zcq-precision-search
          remaining current n epsilon lo hi radius))
    lo hi radius))
  :hints
  (("Goal"
    :induct (zcq-precision-search
             remaining current n epsilon lo hi radius)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcq-precision-search
       nfix car-cons)))))

(defthm zcq-generated-certificate-is-bisected-certificate
  (implies
   (zcq-generated-certificatep
    precision-fuel grid-depth n epsilon)
   (rts-bisected-twiddle-certificatep
    n epsilon
    (zcq-generated-precision precision-fuel grid-depth n epsilon)
    (zcq-sector-lo grid-depth n)
    (zcq-sector-hi grid-depth n)
    (zcq-sector-radius grid-depth n)))
  :hints
  (("Goal"
    :use
    ((:instance zcq-precision-search-sound
                (remaining precision-fuel)
                (current 0)
                (lo (zcq-sector-lo grid-depth n))
                (hi (zcq-sector-hi grid-depth n))
                (radius (zcq-sector-radius grid-depth n))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcq-generated-certificatep
       zcq-precision-witness
       zcq-generated-precision)))))

(defthm zcq-generated-twiddle-system
  (implies
   (zcq-generated-certificatep
    precision-fuel grid-depth n epsilon)
   (rct-twiddle-systemp
    n epsilon
    (zcq-generated-separation
     precision-fuel grid-depth n epsilon)
    (rct-rational-unit
     nil (zcq-generated-tangent
          precision-fuel grid-depth n epsilon))
    (zcq-generated-twiddle-table
     precision-fuel grid-depth n epsilon)))
  :hints
  (("Goal"
    :use
    ((:instance zcq-generated-certificate-is-bisected-certificate)
     (:instance zcn-bisected-generated-twiddle-system
                (p n)
                (precision
                 (zcq-generated-precision
                  precision-fuel grid-depth n epsilon))
                (lo (zcq-sector-lo grid-depth n))
                (hi (zcq-sector-hi grid-depth n))
                (radius (zcq-sector-radius grid-depth n))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcq-generated-tangent
       zcq-generated-twiddle-table
       zcq-generated-separation)))))

(defthm zcq-generated-primitive-root-wfta-correct
  (implies
   (and
    (dm::primep p)
    (integerp p)
    (< 2 p)
    (pfield::fep generator p)
    (not (equal generator 0))
    (equal (pfield::order generator p) (1- p))
    (zcq-generated-certificatep
     precision-fuel grid-depth p epsilon)
    (rational-listp xs)
    (equal (len xs) (nfix p)))
   (and
    (rct-twiddle-systemp
     p epsilon
     (zcq-generated-separation
      precision-fuel grid-depth p epsilon)
     (rct-rational-unit
      nil (zcq-generated-tangent
           precision-fuel grid-depth p epsilon))
     (zcq-generated-twiddle-table
      precision-fuel grid-depth p epsilon))
    (equal
     (zcq-rational-wfta-run
      p generator epsilon grid-depth precision-fuel xs)
     (zcq-rational-direct-run
      p generator epsilon grid-depth precision-fuel xs))))
  :hints
  (("Goal"
    :use
    ((:instance zcq-generated-certificate-is-bisected-certificate
                (n p))
     (:instance zcn-bisected-generated-primitive-root-wfta-correct
                (precision
                 (zcq-generated-precision
                  precision-fuel grid-depth p epsilon))
                (lo (zcq-sector-lo grid-depth p))
                (hi (zcq-sector-hi grid-depth p))
                (radius (zcq-sector-radius grid-depth p))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcq-generated-tangent
       zcq-generated-twiddle-table
       zcq-generated-separation
       zcq-rational-wfta-run
       zcq-rational-direct-run)))))
