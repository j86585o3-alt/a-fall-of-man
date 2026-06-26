; zoq-proof-carrying-horn-closure.lisp
;
; Forward Horn closure with independently checkable derivation traces.

(in-package "ACL2")

(include-book "std/lists/top" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc zoq-proof-carrying-horn-closure
  :parents (acl2::top)
  :short "A certified Horn-closure engine with replayable proof traces."
  :long
  "<p>A rule is a cons whose car is its conclusion and whose cdr is its finite
  premise list.  The executable engine repeatedly sweeps a theory, adding the
  conclusions of enabled rules.  Independently, a derivation trace is checked
  by replaying named rules against the facts accumulated so far.</p>

  <p>Accepted traces are proved sound in every model of the axioms and theory.
  Conversely, every accepted trace is covered by the saturation engine after
  at most one sweep per trace element.  Thus traces are proof certificates,
  while saturation is a complete bounded proof search for those certificates.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Finite-set and Horn-rule semantics
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun vhc-subsetp (xs ys)
  (subsetp-equal xs ys))

(defun vhc-rule-conclusion (rule)
  (car rule))

(defun vhc-rule-premises (rule)
  (cdr rule))

(defun vhc-rule-enabledp (rule facts)
  (vhc-subsetp (vhc-rule-premises rule) facts))

(defun vhc-fire-rule (rule facts)
  (if (vhc-rule-enabledp rule facts)
      (add-to-set-equal (vhc-rule-conclusion rule) facts)
    facts))

(defun vhc-sweep (theory facts)
  (if (endp theory)
      facts
    (vhc-sweep (cdr theory)
               (vhc-fire-rule (car theory) facts))))

(defun vhc-close (fuel theory facts)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      facts
    (vhc-close (1- fuel)
               theory
               (vhc-sweep theory facts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Monotonicity algebra
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm vhc-subsetp-reflexive
  (vhc-subsetp xs xs)
  :hints (("Goal" :in-theory (enable vhc-subsetp))))

(defthm vhc-subsetp-transitive
  (implies (and (vhc-subsetp xs ys)
                (vhc-subsetp ys zs))
           (vhc-subsetp xs zs))
  :hints (("Goal" :in-theory (enable vhc-subsetp))))

(defthm vhc-member-when-subsetp
  (implies (and (vhc-subsetp xs ys)
                (member-equal x xs))
           (member-equal x ys))
  :hints (("Goal" :in-theory (enable vhc-subsetp))))

(defthm vhc-subsetp-of-add-right
  (implies (vhc-subsetp xs ys)
           (vhc-subsetp xs (add-to-set-equal x ys)))
  :hints (("Goal" :in-theory (enable vhc-subsetp))))

(defthm vhc-subsetp-add-self
  (vhc-subsetp facts (add-to-set-equal x facts))
  :hints (("Goal" :in-theory (enable vhc-subsetp))))

(defthm vhc-facts-subset-of-fire
  (vhc-subsetp facts (vhc-fire-rule rule facts))
  :hints
  (("Goal"
    :in-theory (enable vhc-fire-rule))))

(defthm vhc-facts-subset-of-sweep
  (vhc-subsetp facts (vhc-sweep theory facts))
  :hints
  (("Goal"
    :induct (vhc-sweep theory facts)
    :in-theory (enable vhc-sweep))))

(defthm vhc-enabledp-monotone
  (implies (and (vhc-rule-enabledp rule facts)
                (vhc-subsetp facts more-facts))
           (vhc-rule-enabledp rule more-facts))
  :hints
  (("Goal"
    :in-theory (enable vhc-rule-enabledp)
    :use ((:instance vhc-subsetp-transitive
                     (xs (vhc-rule-premises rule))
                     (ys facts)
                     (zs more-facts))))))

(defthm vhc-fire-rule-monotone
  (implies (vhc-subsetp facts more-facts)
           (vhc-subsetp (vhc-fire-rule rule facts)
                        (vhc-fire-rule rule more-facts)))
  :hints
  (("Goal"
    :cases ((vhc-rule-enabledp rule facts)
            (vhc-rule-enabledp rule more-facts))
    :in-theory (enable vhc-fire-rule vhc-subsetp))))

(defun vhc-sweep-pair-induction (theory facts more-facts)
  (if (endp theory)
      (list facts more-facts)
    (vhc-sweep-pair-induction
     (cdr theory)
     (vhc-fire-rule (car theory) facts)
     (vhc-fire-rule (car theory) more-facts))))

(defthm vhc-sweep-monotone
  (implies (vhc-subsetp facts more-facts)
           (vhc-subsetp (vhc-sweep theory facts)
                        (vhc-sweep theory more-facts)))
  :hints
  (("Goal"
    :induct (vhc-sweep-pair-induction theory facts more-facts)
    :in-theory (enable vhc-sweep vhc-sweep-pair-induction))))

(defun vhc-close-pair-induction (fuel theory facts more-facts)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (list facts more-facts)
    (vhc-close-pair-induction
     (1- fuel)
     theory
     (vhc-sweep theory facts)
     (vhc-sweep theory more-facts))))

(defthm vhc-close-monotone
  (implies (vhc-subsetp facts more-facts)
           (vhc-subsetp (vhc-close fuel theory facts)
                        (vhc-close fuel theory more-facts)))
  :hints
  (("Goal"
    :induct (vhc-close-pair-induction fuel theory facts more-facts)
    :in-theory (e/d (vhc-close vhc-close-pair-induction)
                    (vhc-subsetp)))
   ("Subgoal *1/2"
    :use ((:instance vhc-sweep-monotone)))))

(defthm vhc-facts-subset-of-close
  (vhc-subsetp facts (vhc-close fuel theory facts))
  :hints
  (("Goal"
    :induct (vhc-close fuel theory facts)
    :in-theory (e/d (vhc-close) (vhc-subsetp)))
   ("Subgoal *1/2"
    :use ((:instance vhc-subsetp-transitive
                     (xs facts)
                     (ys (vhc-sweep theory facts))
                     (zs (vhc-close (1- fuel)
                                    theory
                                    (vhc-sweep theory facts))))
          (:instance vhc-facts-subset-of-sweep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Trace certificates and replay
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun vhc-trace-validp (trace theory facts)
  (if (endp trace)
      t
    (and (member-equal (car trace) theory)
         (vhc-rule-enabledp (car trace) facts)
         (vhc-trace-validp
          (cdr trace)
          theory
          (vhc-fire-rule (car trace) facts)))))

(defun vhc-replay (trace facts)
  (if (endp trace)
      facts
    (vhc-replay (cdr trace)
                (vhc-fire-rule (car trace) facts))))

(defun vhc-certifiedp (atom trace theory axioms)
  (and (vhc-trace-validp trace theory axioms)
       (member-equal atom (vhc-replay trace axioms))))

(defthm vhc-replay-of-cons
  (equal (vhc-replay (cons rule trace) facts)
         (vhc-replay trace (vhc-fire-rule rule facts)))
  :hints (("Goal" :in-theory (enable vhc-replay))))

(defthm vhc-facts-subset-of-replay
  (vhc-subsetp facts (vhc-replay trace facts))
  :hints
  (("Goal"
    :induct (vhc-replay trace facts)
    :in-theory (enable vhc-replay))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Model-theoretic soundness
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun vhc-theory-modelp (theory model)
  (if (endp theory)
      t
    (and (or (not (vhc-rule-enabledp (car theory) model))
             (member-equal (vhc-rule-conclusion (car theory)) model))
         (vhc-theory-modelp (cdr theory) model))))

(defun vhc-modelp (theory axioms model)
  (and (vhc-subsetp axioms model)
       (vhc-theory-modelp theory model)))

(defthm vhc-member-conclusion-when-rule-in-model
  (implies (and (vhc-theory-modelp theory model)
                (member-equal rule theory)
                (vhc-rule-enabledp rule model))
           (member-equal (vhc-rule-conclusion rule) model))
  :hints
  (("Goal"
    :induct (len theory)
    :in-theory (enable vhc-theory-modelp))))

(defthm vhc-fire-rule-subset-of-model
  (implies (and (vhc-subsetp facts model)
                (vhc-theory-modelp theory model)
                (member-equal rule theory))
           (vhc-subsetp (vhc-fire-rule rule facts) model))
  :hints
  (("Goal"
    :cases ((vhc-rule-enabledp rule facts))
    :use ((:instance vhc-enabledp-monotone
                     (more-facts model))
          (:instance vhc-member-conclusion-when-rule-in-model))
    :in-theory (enable vhc-fire-rule vhc-subsetp))))

(defthm vhc-replay-subset-of-every-model
  (implies (and (vhc-trace-validp trace theory facts)
                (vhc-subsetp facts model)
                (vhc-theory-modelp theory model))
           (vhc-subsetp (vhc-replay trace facts) model))
  :hints
  (("Goal"
    :induct (vhc-replay trace facts)
    :in-theory
    (e/d (vhc-replay vhc-trace-validp)
         (vhc-fire-rule
          vhc-subsetp
          vhc-theory-modelp)))
   ("Subgoal *1/2"
    :use ((:instance vhc-fire-rule-subset-of-model
                     (rule (car trace)))))))

(defthm vhc-certifiedp-sound
  (implies (and (vhc-certifiedp atom trace theory axioms)
                (vhc-modelp theory axioms model))
           (member-equal atom model))
  :hints
  (("Goal"
    :use ((:instance vhc-replay-subset-of-every-model
                     (facts axioms)))
    :in-theory (enable vhc-certifiedp vhc-modelp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Bounded completeness of saturation for certificates
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm vhc-member-preserved-by-fire
  (implies (member-equal atom facts)
           (member-equal atom (vhc-fire-rule rule facts)))
  :hints (("Goal" :in-theory (enable vhc-fire-rule))))

(defthm vhc-member-preserved-by-sweep
  (implies (member-equal atom facts)
           (member-equal atom (vhc-sweep theory facts)))
  :hints
  (("Goal"
    :induct (vhc-sweep theory facts)
    :in-theory (enable vhc-sweep))))

(defthm vhc-sweep-covers-enabled-member-rule
  (implies (and (member-equal rule theory)
                (vhc-rule-enabledp rule facts))
           (member-equal (vhc-rule-conclusion rule)
                         (vhc-sweep theory facts)))
  :hints
  (("Goal"
    :induct (vhc-sweep theory facts)
    :in-theory (enable vhc-sweep))))

(defthm vhc-fire-subset-of-sweep-under-simulation
  (implies (and (vhc-subsetp facts engine-facts)
                (member-equal rule theory)
                (vhc-rule-enabledp rule facts))
           (vhc-subsetp (vhc-fire-rule rule facts)
                        (vhc-sweep theory engine-facts)))
  :hints
  (("Goal"
    :use ((:instance vhc-enabledp-monotone
                     (more-facts engine-facts))
          (:instance vhc-sweep-covers-enabled-member-rule
                     (facts engine-facts))
          (:instance vhc-subsetp-transitive
                     (xs facts)
                     (ys engine-facts)
                     (zs (vhc-sweep theory engine-facts))))
    :in-theory (enable vhc-fire-rule vhc-subsetp))))

(defun vhc-replay-close-induction (trace theory facts engine-facts)
  (if (endp trace)
      (list theory facts engine-facts)
    (vhc-replay-close-induction
     (cdr trace)
     theory
     (vhc-fire-rule (car trace) facts)
     (vhc-sweep theory engine-facts))))

(defthm vhc-replay-subset-of-bounded-close
  (implies (and (vhc-trace-validp trace theory facts)
                (vhc-subsetp facts engine-facts))
           (vhc-subsetp
            (vhc-replay trace facts)
            (vhc-close (len trace) theory engine-facts)))
  :hints
  (("Goal"
    :induct (vhc-replay-close-induction
             trace theory facts engine-facts)
    :in-theory
    (e/d (vhc-replay-close-induction
          vhc-replay
          vhc-trace-validp
          vhc-close)
         (vhc-fire-rule
          vhc-sweep
          vhc-subsetp)))
   ("Subgoal *1/2"
    :use ((:instance vhc-fire-subset-of-sweep-under-simulation
                     (rule (car trace)))))))

(defthm vhc-certifiedp-found-by-bounded-close
  (implies (vhc-certifiedp atom trace theory axioms)
           (member-equal atom
                         (vhc-close (len trace) theory axioms)))
  :hints
  (("Goal"
    :use ((:instance vhc-replay-subset-of-bounded-close
                     (facts axioms)
                     (engine-facts axioms)))
    :in-theory (enable vhc-certifiedp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 6. Stability
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun vhc-stablep (theory facts)
  (equal (vhc-sweep theory facts) facts))

(defthm vhc-close-when-stable
  (implies (vhc-stablep theory facts)
           (equal (vhc-close fuel theory facts)
                  facts))
  :hints
  (("Goal"
    :induct (vhc-close fuel theory facts)
    :in-theory (enable vhc-close vhc-stablep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 7. Ground witness
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *vhc-theory*
  '((b a)
    (c b)
    (d a c)))

(defconst *vhc-trace*
  '((b a)
    (c b)
    (d a c)))

(assert-event
 (and (vhc-certifiedp 'd *vhc-trace* *vhc-theory* '(a))
      (member-equal 'd
                    (vhc-close (len *vhc-trace*)
                               *vhc-theory*
                               '(a)))))

(defxdoc vhc-user-interface
  :parents (zoq-proof-carrying-horn-closure)
  :short "Public interface for proof-carrying Horn closure."
  :long
  "<p><tt>VHC-CLOSE</tt> performs bounded saturation.
  <tt>VHC-CERTIFIEDP</tt> checks a derivation trace.  The principal laws are
  <tt>VHC-CERTIFIEDP-SOUND</tt> and
  <tt>VHC-CERTIFIEDP-FOUND-BY-BOUNDED-CLOSE</tt>.</p>")
