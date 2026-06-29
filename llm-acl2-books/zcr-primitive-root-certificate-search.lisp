; Resource-bounded search for a finite-field element of full multiplicative
; order.  Soundness is unconditional; total success for every prime is kept
; as a separate finite-group theorem rather than hidden in the search loop.
(in-package "ACL2")

(include-book "zcq-generated-rational-wfta-interface")

(defun zcr-primitive-root-candidatep (candidate p)
  (and (pfield::fep candidate p)
       (not (equal candidate 0))
       (equal (pfield::order candidate p) (1- p))))

(defun zcr-primitive-root-search-aux (remaining candidate p)
  (declare
   (xargs
    :measure (nfix remaining)
    :hints
    (("Goal"
      :in-theory
      (union-theories
       (theory 'minimal-theory)
       '(nfix zp natp o-p o< o-finp
         default-less-than-1 default-less-than-2
         default-plus-1 default-plus-2))))))
  (if (zp remaining)
      nil
    (if (zcr-primitive-root-candidatep candidate p)
        (cons candidate t)
      (zcr-primitive-root-search-aux
       (1- remaining) (1+ (nfix candidate)) p))))

(defun zcr-primitive-root-search (p)
  (zcr-primitive-root-search-aux (nfix p) 1 p))

(defun zcr-generated-primitive-root (p)
  (if (consp (zcr-primitive-root-search p))
      (car (zcr-primitive-root-search p))
    0))

(defun zcr-generated-primitive-rootp (p)
  (consp (zcr-primitive-root-search p)))

(defthm booleanp-of-zcr-primitive-root-candidatep
  (booleanp (zcr-primitive-root-candidatep candidate p))
  :hints (("Goal"
           :in-theory (enable zcr-primitive-root-candidatep))))

(defthm zcr-primitive-root-search-aux-sound
  (implies
   (consp (zcr-primitive-root-search-aux remaining candidate p))
   (zcr-primitive-root-candidatep
    (car (zcr-primitive-root-search-aux remaining candidate p)) p))
  :hints
  (("Goal"
    :induct (zcr-primitive-root-search-aux remaining candidate p)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcr-primitive-root-search-aux car-cons nfix)))))

(defthm zcr-generated-primitive-root-is-candidate
  (implies (zcr-generated-primitive-rootp p)
           (zcr-primitive-root-candidatep
            (zcr-generated-primitive-root p) p))
  :hints
  (("Goal"
    :use ((:instance zcr-primitive-root-search-aux-sound
                     (remaining (nfix p))
                     (candidate 1)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcr-primitive-root-search
       zcr-generated-primitive-root
       zcr-generated-primitive-rootp)))))

(defthm zcr-generated-primitive-root-is-field-element
  (implies (zcr-generated-primitive-rootp p)
           (pfield::fep (zcr-generated-primitive-root p) p))
  :hints (("Goal"
           :use ((:instance zcr-generated-primitive-root-is-candidate))
           :in-theory (enable zcr-primitive-root-candidatep))))

(defthm zcr-generated-primitive-root-is-nonzero
  (implies (zcr-generated-primitive-rootp p)
           (not (equal (zcr-generated-primitive-root p) 0)))
  :hints (("Goal"
           :use ((:instance zcr-generated-primitive-root-is-candidate))
           :in-theory (enable zcr-primitive-root-candidatep))))

(defthm zcr-generated-primitive-root-has-full-order
  (implies (zcr-generated-primitive-rootp p)
           (equal (pfield::order
                   (zcr-generated-primitive-root p) p)
                  (1- p)))
  :hints (("Goal"
           :use ((:instance zcr-generated-primitive-root-is-candidate))
           :in-theory (enable zcr-primitive-root-candidatep))))
