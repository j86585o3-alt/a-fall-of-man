; zgs-complementary-clause-processor.lisp
; A verified clause processor for duplicate elimination and complementary
; literal detection.

(in-package "ACL2")

(include-book "std/lists/top" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc zgs-complementary-clause-processor
  :parents (acl2::top)
  :short "A verified clause processor for duplicate and complementary literals."
  :long "<p>The processor removes duplicate literals from ordinary ACL2
  clauses.  When a clause contains both a literal and its syntactic complement,
  it returns no subgoals.  Its evaluator theorem is registered as a genuine
  clause-processor correctness rule, so the executable normalizer may be used
  directly in hints without an additional trusted event.</p>")

(defevaluator vtc-ev vtc-ev-list
  ((if x y z)
   (not x)))

(defun vtc-not-form-p (term)
  (and (consp term)
       (equal (car term) 'not)
       (consp (cdr term))
       (endp (cddr term))))

(defun vtc-complement (literal)
  (if (vtc-not-form-p literal)
      (cadr literal)
    (list 'not literal)))

(defun vtc-complementaryp (clause)
  (if (endp clause)
      nil
    (or (member-equal (vtc-complement (car clause))
                      (cdr clause))
        (vtc-complementaryp (cdr clause)))))

(defun vtc-dedup (clause)
  (if (endp clause)
      nil
    (if (member-equal (car clause) (cdr clause))
        (vtc-dedup (cdr clause))
      (cons (car clause)
            (vtc-dedup (cdr clause))))))

(defun vtc-clause-processor (clause)
  (if (vtc-complementaryp clause)
      nil
    (list (vtc-dedup clause))))

(defthm vtc-ev-of-complement
  (iff (vtc-ev (vtc-complement literal) a)
       (not (vtc-ev literal a)))
  :hints (("Goal"
           :in-theory (enable vtc-complement vtc-not-form-p))))

(defthm vtc-ev-of-disjoin2
  (iff (vtc-ev (disjoin2 left right) a)
       (or (vtc-ev left a)
           (vtc-ev right a)))
  :hints (("Goal"
           :in-theory (enable disjoin2))))

(defthm vtc-ev-disjoin-when-member
  (implies (and (member-equal literal clause)
                (vtc-ev literal a))
           (vtc-ev (disjoin clause) a))
  :hints (("Goal"
           :induct (len clause)
           :in-theory (enable disjoin))))

(defthm vtc-complementaryp-is-true
  (implies (vtc-complementaryp clause)
           (vtc-ev (disjoin clause) a))
  :hints (("Goal"
           :induct (vtc-complementaryp clause)
           :in-theory (enable vtc-complementaryp disjoin))))

(defthm vtc-ev-of-disjoin-dedup
  (iff (vtc-ev (disjoin (vtc-dedup clause)) a)
       (vtc-ev (disjoin clause) a))
  :hints (("Goal"
           :induct (vtc-dedup clause)
           :in-theory (enable vtc-dedup disjoin))))

(defthm vtc-ev-of-conjoin-singleton
  (iff (vtc-ev (conjoin (list term)) a)
       (vtc-ev term a))
  :hints (("Goal" :in-theory (enable conjoin))))

(defthm vtc-clause-processor-correct-when-not-complementary
  (implies
   (and (not (vtc-complementaryp clause))
        (vtc-ev
         (conjoin-clauses (vtc-clause-processor clause))
         a))
   (vtc-ev (disjoin clause) a))
  :hints
  (("Goal"
    :use ((:instance vtc-ev-of-conjoin-singleton
                     (term (disjoin (vtc-dedup clause))))
          (:instance vtc-ev-of-disjoin-dedup))
    :in-theory
    (e/d (vtc-clause-processor
          conjoin-clauses
          disjoin-lst)
         (vtc-ev-of-conjoin-singleton
          vtc-ev-of-disjoin-dedup)))))

(defthm vtc-clause-processor-correct
  (implies
   (and (pseudo-term-listp clause)
        (alistp a)
        (vtc-ev
         (conjoin-clauses (vtc-clause-processor clause))
         a))
   (vtc-ev (disjoin clause) a))
  :rule-classes :clause-processor
  :hints (("Goal"
           :cases ((vtc-complementaryp clause))
           :use ((:instance vtc-complementaryp-is-true)
                 (:instance vtc-clause-processor-correct-when-not-complementary))
           :in-theory
           (disable vtc-complementaryp-is-true
                    vtc-clause-processor-correct-when-not-complementary))))

(defthm vtc-ground-witness
  (implies p p)
  :hints (("Goal"
           :clause-processor vtc-clause-processor))
  :rule-classes nil)

(defxdoc vtc-user-interface
  :parents (zgs-complementary-clause-processor)
  :short "Public interface for verified clause normalization."
  :long "<p>Use <tt>VTC-CLAUSE-PROCESSOR</tt> in a
  <tt>:CLAUSE-PROCESSOR</tt> hint.  <tt>VTC-CLAUSE-PROCESSOR-CORRECT</tt> is the
  evaluator-backed soundness theorem registered with ACL2.</p>")
