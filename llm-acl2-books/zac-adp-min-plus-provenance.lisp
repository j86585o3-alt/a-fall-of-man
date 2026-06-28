; zac-adp-min-plus-provenance.lisp
;
; A min-plus instance of algebraic dynamic programming that carries a compact
; path witness in the low bits of each tropical weight.  A feasible potential
; then turns the emitted path into a globally checkable optimality certificate.

(in-package "ACL2")

(include-book "zaa-algebraic-dynamic-programming")
(include-book "zkx-weighted-path-certificates")
(include-book "arithmetic-5/top" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc zac-adp-min-plus-provenance
  :parents (zaa-algebraic-dynamic-programming
            zkx-weighted-path-certificates)
  :short "Min-plus ADP with radix-packed provenance and optimality certificates."
  :long
  "<p>A finite value is a natural number and <tt>NIL</tt> is infinity.  Tropical
  addition chooses the smaller finite value, while tropical multiplication is
  ordinary addition.  Edge weights are packed as <tt>cost * base + bit</tt>.
  Hence a shortest-path calculation simultaneously accumulates its ordinary
  cost in the high radix digit and a compact edge-set witness in the low
  digit.</p>

  <p>The ADP engine therefore emits a path witness without a second search.
  Decoding the low bits produces a path accepted by the weighted-path
  certificate checker.  A feasible potential whose target value equals the
  emitted path cost proves that every competing accepted path is at least as
  expensive.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Extended-natural min-plus semiring
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mwp-valuep (x)
  (or (null x) (natp x)))

(defun mwp-zero () nil)
(defun mwp-one () 0)

(defun mwp-plus (x y)
  (cond ((null x) y)
        ((null y) x)
        ((<= (nfix x) (nfix y)) x)
        (t y)))

(defun mwp-times (x y)
  (if (or (null x) (null y))
      nil
    (+ (nfix x) (nfix y))))

(verify-guards mwp-valuep)
(verify-guards mwp-zero)
(verify-guards mwp-one)
(verify-guards mwp-plus)
(verify-guards mwp-times)

(defthm mwp-valuep-of-zero
  (mwp-valuep (mwp-zero)))

(defthm mwp-valuep-of-one
  (mwp-valuep (mwp-one)))

(defthm mwp-valuep-of-plus
  (implies (and (mwp-valuep x)
                (mwp-valuep y))
           (mwp-valuep (mwp-plus x y)))
  :hints (("Goal" :in-theory (enable mwp-valuep mwp-plus))))

(defthm mwp-valuep-of-times
  (implies (and (mwp-valuep x)
                (mwp-valuep y))
           (mwp-valuep (mwp-times x y)))
  :hints (("Goal" :in-theory (enable mwp-valuep mwp-times))))

(defthm mwp-plus-commutative
  (implies (and (mwp-valuep x)
                (mwp-valuep y))
           (equal (mwp-plus x y)
                  (mwp-plus y x)))
  :hints (("Goal" :in-theory (enable mwp-valuep mwp-plus))))

(defthm mwp-plus-associative
  (implies (and (mwp-valuep x)
                (mwp-valuep y)
                (mwp-valuep z))
           (equal (mwp-plus (mwp-plus x y) z)
                  (mwp-plus x (mwp-plus y z))))
  :hints (("Goal" :in-theory (enable mwp-valuep mwp-plus))))

(defthm mwp-plus-left-identity
  (implies (mwp-valuep x)
           (equal (mwp-plus (mwp-zero) x) x))
  :hints (("Goal" :in-theory (enable mwp-zero mwp-plus))))

(defthm mwp-plus-right-identity
  (implies (mwp-valuep x)
           (equal (mwp-plus x (mwp-zero)) x))
  :hints (("Goal" :in-theory (enable mwp-zero mwp-plus))))

(defthm mwp-times-commutative
  (implies (and (mwp-valuep x)
                (mwp-valuep y))
           (equal (mwp-times x y)
                  (mwp-times y x)))
  :hints (("Goal" :in-theory (enable mwp-valuep mwp-times))))

(defthm mwp-times-associative
  (implies (and (mwp-valuep x)
                (mwp-valuep y)
                (mwp-valuep z))
           (equal (mwp-times (mwp-times x y) z)
                  (mwp-times x (mwp-times y z))))
  :hints (("Goal" :in-theory (enable mwp-valuep mwp-times))))

(defthm mwp-times-left-identity
  (implies (mwp-valuep x)
           (equal (mwp-times (mwp-one) x) x))
  :hints (("Goal" :in-theory (enable mwp-valuep mwp-one mwp-times))))

(defthm mwp-times-right-identity
  (implies (mwp-valuep x)
           (equal (mwp-times x (mwp-one)) x))
  :hints (("Goal" :in-theory (enable mwp-valuep mwp-one mwp-times))))

(defthm mwp-times-zero-left
  (implies (mwp-valuep x)
           (equal (mwp-times (mwp-zero) x) (mwp-zero)))
  :hints (("Goal" :in-theory (enable mwp-zero mwp-times))))

(defthm mwp-times-zero-right
  (implies (mwp-valuep x)
           (equal (mwp-times x (mwp-zero)) (mwp-zero)))
  :hints (("Goal" :in-theory (enable mwp-zero mwp-times))))

(defthm mwp-translate-min
  (implies (and (natp x) (natp y) (natp z))
           (equal (+ z (if (<= x y) x y))
                  (if (<= (+ z x) (+ z y))
                      (+ z x)
                    (+ z y)))))

(defthm mwp-times-distributes-over-plus-left
  (implies (and (mwp-valuep x)
                (mwp-valuep y)
                (mwp-valuep z))
           (equal (mwp-times x (mwp-plus y z))
                  (mwp-plus (mwp-times x y)
                            (mwp-times x z))))
  :hints (("Goal"
           :use ((:instance mwp-translate-min
                            (x (nfix y))
                            (y (nfix z))
                            (z (nfix x))))
           :in-theory (enable mwp-valuep mwp-plus mwp-times))))

(defthm mwp-times-distributes-over-plus-right
  (implies (and (mwp-valuep x)
                (mwp-valuep y)
                (mwp-valuep z))
           (equal (mwp-times (mwp-plus x y) z)
                  (mwp-plus (mwp-times x z)
                            (mwp-times y z))))
  :hints (("Goal"
           :use ((:instance mwp-times-distributes-over-plus-left
                            (x z) (y x) (z y))
                 (:instance mwp-times-commutative
                            (x z) (y (mwp-plus x y)))
                 (:instance mwp-times-commutative (x z) (y x))
                 (:instance mwp-times-commutative (x z) (y y))))))

(defattach (adp-valuep mwp-valuep)
           (adp-zero mwp-zero)
           (adp-one mwp-one)
           (adp-plus mwp-plus)
           (adp-times mwp-times))

; Attachments make ADP-FAST-VALUE convenient at the ACL2 prompt, but ACL2
; deliberately ignores attachments while evaluating logical events such as
; DEFCONST and MAKE-EVENT.  The following specialization is therefore a
; concrete executable copy of the generic forward chart machine.  Its
; refinement theorem is transported from ADP-FAST-VALUE-CORRECT by functional
; instantiation.  Section 3 additionally checks the emitted path and potential
; and proves global optimality from that independently replayable certificate.

(defun mwp-fast-chart-ref (index chart)
  (let ((look (hons-get (nfix index) chart)))
    (if look (cdr look) (mwp-zero))))

(defun mwp-fast-eval-premises (premises chart)
  (if (endp premises)
      (mwp-one)
    (mwp-times (mwp-fast-chart-ref (car premises) chart)
               (mwp-fast-eval-premises (cdr premises) chart))))

(defun mwp-fast-eval-rule (rule chart)
  (mwp-times (car rule)
             (mwp-fast-eval-premises (cdr rule) chart)))

(defun mwp-fast-eval-rules (rules chart)
  (if (endp rules)
      (mwp-zero)
    (mwp-plus (mwp-fast-eval-rule (car rules) chart)
              (mwp-fast-eval-rules (cdr rules) chart))))

(defun mwp-fast-eval-item (item chart)
  (mwp-plus (car item)
            (mwp-fast-eval-rules (cdr item) chart)))

(defun mwp-fast-run-aux (items index chart)
  (if (endp items)
      chart
    (let ((value (mwp-fast-eval-item (car items) chart)))
      (mwp-fast-run-aux
       (cdr items)
       (1+ (nfix index))
       (hons-acons (nfix index) value chart)))))

(defun mwp-fast-run (program)
  (mwp-fast-run-aux program 0 nil))

(defun mwp-fast-value (index program)
  (let* ((chart (mwp-fast-run program))
         (value (mwp-fast-chart-ref index chart)))
    (prog2$ (fast-alist-free chart)
            value)))

; Concrete validity and derivation-tree semantics are deliberately isomorphic
; to the abstract ADP interface.  This lets ACL2 transport the already-proved
; fast-chart refinement theorem instead of rebuilding it for min-plus.

(defun mwp-rule-validp (rule bound)
  (and (consp rule)
       (mwp-valuep (car rule))
       (adp-premises-belowp (cdr rule) bound)))

(defun mwp-rules-validp (rules bound)
  (if (endp rules)
      t
    (and (mwp-rule-validp (car rules) bound)
         (mwp-rules-validp (cdr rules) bound))))

(defun mwp-item-validp (item bound)
  (and (consp item)
       (mwp-valuep (car item))
       (mwp-rules-validp (cdr item) bound)))

(defun mwp-prefix-validp (n program)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (and (mwp-prefix-validp (1- n) program)
         (mwp-item-validp (nth (1- n) program) (1- n)))))

(defun mwp-program-validp (program)
  (mwp-prefix-validp (len program) program))

(mutual-recursion
 (defun mwp-denote-item (index program)
   (declare
    (xargs
     :measure
     (two-nats-measure
      (nfix index)
      (+ 1 (acl2-count (nth (nfix index) program))))))
   (let ((item (nth (nfix index) program)))
     (if (consp item)
         (mwp-plus (car item)
                   (mwp-denote-rules (cdr item) (nfix index) program))
       (mwp-zero))))

 (defun mwp-denote-rules (rules bound program)
   (declare
    (xargs
     :measure
     (two-nats-measure (nfix bound) (+ 1 (acl2-count rules)))))
   (if (endp rules)
       (mwp-zero)
     (mwp-plus (mwp-denote-rule (car rules) bound program)
               (mwp-denote-rules (cdr rules) bound program))))

 (defun mwp-denote-rule (rule bound program)
   (declare
    (xargs
     :measure
     (two-nats-measure (nfix bound) (+ 1 (acl2-count rule)))))
   (if (consp rule)
       (mwp-times (car rule)
                  (mwp-denote-premises (cdr rule) bound program))
     (mwp-zero)))

 (defun mwp-denote-premises (premises bound program)
   (declare
    (xargs
     :measure
     (two-nats-measure (nfix bound) (+ 1 (acl2-count premises)))))
   (if (endp premises)
       (mwp-one)
     (if (and (natp (car premises))
              (< (car premises) (nfix bound)))
         (mwp-times
          (mwp-denote-item (car premises) program)
          (mwp-denote-premises (cdr premises) bound program))
       (mwp-zero)))))

(defthm mwp-denote-item-when-not-consp
  (implies (not (consp (nth index program)))
           (not (mwp-denote-item index program)))
  :hints (("Goal" :in-theory (enable mwp-denote-item mwp-zero))))

(defthm mwp-fast-value-correct
  (implies (and (mwp-program-validp program)
                (natp index)
                (< index (len program)))
           (equal (mwp-fast-value index program)
                  (mwp-denote-item index program)))
  :hints
  (("Goal"
    :in-theory nil
    :use
    ((:functional-instance
      adp-fast-value-correct
      (adp-valuep mwp-valuep)
      (adp-zero mwp-zero)
      (adp-one mwp-one)
      (adp-plus mwp-plus)
      (adp-times mwp-times)
      (adp-rule-validp mwp-rule-validp)
      (adp-rules-validp mwp-rules-validp)
      (adp-item-validp mwp-item-validp)
      (adp-prefix-validp mwp-prefix-validp)
      (adp-program-validp mwp-program-validp)
      (adp-fast-chart-ref mwp-fast-chart-ref)
      (adp-fast-eval-premises mwp-fast-eval-premises)
      (adp-fast-eval-rule mwp-fast-eval-rule)
      (adp-fast-eval-rules mwp-fast-eval-rules)
      (adp-fast-eval-item mwp-fast-eval-item)
      (adp-fast-run-aux mwp-fast-run-aux)
      (adp-fast-run mwp-fast-run)
      (adp-fast-value mwp-fast-value)
      (adp-denote-item mwp-denote-item)
      (adp-denote-rules mwp-denote-rules)
      (adp-denote-rule mwp-denote-rule)
      (adp-denote-premises mwp-denote-premises))))
   (and stable-under-simplificationp
        '(:in-theory
          (enable mwp-rule-validp
                  mwp-rules-validp
                  mwp-item-validp
                  mwp-prefix-validp
                  mwp-program-validp
                  mwp-fast-chart-ref
                  mwp-fast-eval-premises
                  mwp-fast-eval-rule
                  mwp-fast-eval-rules
                  mwp-fast-eval-item
                  mwp-fast-run-aux
                  mwp-fast-run
                  mwp-fast-value
                  mwp-denote-item
                  mwp-denote-rules
                  mwp-denote-rule
                  mwp-denote-premises
                  mwp-valuep
                  mwp-zero
                  mwp-one
                  mwp-plus
                  mwp-times)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Radix-packed path provenance
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mwp-pack (cost code base)
  (+ (* (nfix cost) (nfix base))
     (nfix code)))

(defthm mwp-pack-add
  (equal (+ (mwp-pack cost1 code1 base)
            (mwp-pack cost2 code2 base))
         (mwp-pack (+ (nfix cost1) (nfix cost2))
                   (+ (nfix code1) (nfix code2))
                   base))
  :hints (("Goal" :in-theory (enable mwp-pack))))

(defun mwp-base-fix (base)
  (if (posp base) base 1))

(defun mwp-unpack-cost (packed base)
  (floor (nfix packed) (mwp-base-fix base)))

(defun mwp-unpack-code (packed base)
  (mod (nfix packed) (mwp-base-fix base)))

(defthm mwp-unpack-cost-of-pack
  (implies (and (natp cost)
                (natp code)
                (posp base)
                (< code base))
           (equal (mwp-unpack-cost (mwp-pack cost code base) base)
                  cost))
  :hints (("Goal"
           :in-theory (enable mwp-unpack-cost mwp-pack mwp-base-fix))))

(defthm mwp-unpack-code-of-pack
  (implies (and (natp cost)
                (natp code)
                (posp base)
                (< code base))
           (equal (mwp-unpack-code (mwp-pack cost code base) base)
                  code))
  :hints (("Goal"
           :in-theory (enable mwp-unpack-code mwp-pack mwp-base-fix))))

(defun mwp-edge-selectedp (id code)
  (logbitp (nfix id) (nfix code)))

(defun mwp-decode-path (code edge-table)
  (if (endp edge-table)
      nil
    (if (mwp-edge-selectedp (caar edge-table) code)
        (cons (cdar edge-table)
              (mwp-decode-path code (cdr edge-table)))
      (mwp-decode-path code (cdr edge-table)))))

(defun mwp-table-graph (edge-table)
  (if (endp edge-table)
      nil
    (cons (cdar edge-table)
          (mwp-table-graph (cdr edge-table)))))

(defun mwp-node-index (node nodes)
  (if (endp nodes)
      0
    (if (equal (symbol-fix node) (symbol-fix (car nodes)))
        0
      (1+ (mwp-node-index node (cdr nodes))))))

(defun mwp-rules-for-node (node edge-table nodes base)
  (if (endp edge-table)
      nil
    (let* ((entry (car edge-table))
           (id (car entry))
           (edge (cdr entry))
           (rest (mwp-rules-for-node
                  node (cdr edge-table) nodes base)))
      (if (equal (vwc-edge->to edge) (symbol-fix node))
          (cons (list (mwp-pack (vwc-edge->weight edge)
                                (expt 2 (nfix id))
                                base)
                      (mwp-node-index (vwc-edge->from edge) nodes))
                rest)
        rest))))

(defun mwp-compile-program-aux
  (remaining-nodes all-nodes source edge-table base)
  (if (endp remaining-nodes)
      nil
    (let ((node (car remaining-nodes)))
      (cons
       (cons (if (equal (symbol-fix node) (symbol-fix source)) 0 nil)
             (mwp-rules-for-node node edge-table all-nodes base))
       (mwp-compile-program-aux
        (cdr remaining-nodes) all-nodes source edge-table base)))))

(defun mwp-base-for-table (edge-table)
  (expt 2 (len edge-table)))

(defun mwp-compile-program (nodes source edge-table)
  (mwp-compile-program-aux
   nodes nodes source edge-table (mwp-base-for-table edge-table)))

(defun mwp-chart-potentials (nodes index chart base)
  (if (endp nodes)
      nil
    (omap::update
     (symbol-fix (car nodes))
     (mwp-unpack-cost (mwp-fast-chart-ref index chart) base)
     (mwp-chart-potentials
      (cdr nodes) (1+ (nfix index)) chart base))))

(defun mwp-solve (target program base edge-table nodes)
  (let* ((chart (mwp-fast-run program))
         (packed (mwp-fast-chart-ref target chart))
         (cost (mwp-unpack-cost packed base))
         (code (mwp-unpack-code packed base))
         (path (mwp-decode-path code edge-table))
         (potentials (mwp-chart-potentials nodes 0 chart base)))
    (prog2$ (fast-alist-free chart)
            (list cost path potentials packed code))))

(defun mwp-solution-cost (solution) (nfix (car solution)))
(defun mwp-solution-path (solution) (cadr solution))
(defun mwp-solution-potentials (solution) (caddr solution))
(defun mwp-solution-packed (solution) (cadddr solution))
(defun mwp-solution-code (solution) (car (cddddr solution)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Potential certificates prove global optimality
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mwp-optimal-certificate-p
  (path graph source target potentials)
  (and (vwc-certificate-p path graph source target)
       (vwc-graph-model-p graph potentials)
       (equal (vwc-potential source potentials) 0)
       (equal (vwc-potential target potentials)
              (vwc-path-cost path))))

(defthm mwp-optimal-certificate-lower-bound
  (implies
   (and (mwp-optimal-certificate-p
         witness graph source target potentials)
        (vwc-certificate-p competitor graph source target))
   (<= (vwc-path-cost witness)
       (vwc-path-cost competitor)))
  :hints (("Goal"
           :use ((:instance vwc-certificate-sound
                            (path competitor)
                            (start source)
                            (finish target)))
           :in-theory (enable mwp-optimal-certificate-p))))

(defthm mwp-checked-solution-is-globally-optimal
  (implies
   (and (mwp-optimal-certificate-p
         (mwp-solution-path solution)
         graph source target potentials)
        (equal (mwp-solution-cost solution)
               (vwc-path-cost (mwp-solution-path solution)))
        (vwc-certificate-p competitor graph source target))
   (<= (mwp-solution-cost solution)
       (vwc-path-cost competitor)))
  :hints (("Goal"
           :use ((:instance mwp-optimal-certificate-lower-bound
                            (witness (mwp-solution-path solution)))))))

(defxdoc mwp-client-interface
  :parents (zac-adp-min-plus-provenance)
  :short "A small shortest-path program that emits its own witness."
  :long
  "<p><tt>MWP-SOLVE</tt> runs the generic ADP engine once.  The high radix
  digit is the optimum cost and the low bits decode to the selected path.
  <tt>MWP-OPTIMAL-CERTIFICATE-P</tt> checks that path and a feasible potential;
  <tt>MWP-CHECKED-SOLUTION-IS-GLOBALLY-OPTIMAL</tt> then compares the emitted
  answer with every other accepted path certificate.</p>")
