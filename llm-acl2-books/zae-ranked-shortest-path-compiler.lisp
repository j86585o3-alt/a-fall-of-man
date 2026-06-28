; zae-ranked-shortest-path-compiler.lisp
;
; A certificate-producing compiler for topologically ranked weighted graphs.
; The client supplies only nodes and incoming arcs.  The compiler constructs
; shortest paths, exact costs, a feasible potential, and a min-plus ADP program.

(in-package "ACL2")

(include-book "zac-adp-min-plus-provenance")
(include-book "std/lists/top" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc zae-ranked-shortest-path-compiler
  :parents (zac-adp-min-plus-provenance)
  :short "Ranked graphs compile to self-certifying shortest-path algorithms."
  :long
  "<p>A ranked graph is a list of items.  Item zero is the source and has no
  incoming arcs.  Every later item has at least one incoming arc from a smaller
  index.  An arc is <tt>(predecessor-index weight)</tt>.  This tiny description
  is compiled into a one-pass shortest-path algorithm, witness paths, and a
  feasible potential.  The principal theorem establishes that the generated
  solution is accepted by the independent weighted-path checker.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Ranked graph syntax
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rsp-nodes (spec)
  (if (endp spec)
      nil
    (cons (caar spec)
          (rsp-nodes (cdr spec)))))

(defun rsp-node-at (index spec)
  (symbol-fix (car (nth (nfix index) spec))))

(defun rsp-arcs-at (index spec)
  (cdr (nth (nfix index) spec)))

(defun rsp-arc-pred (arc)
  (nfix (car arc)))

(defun rsp-arc-weight (arc)
  (nfix (cadr arc)))

(defun rsp-arc-validp (arc bound)
  (and (true-listp arc)
       (equal (len arc) 2)
       (natp (car arc))
       (< (car arc) (nfix bound))
       (natp (cadr arc))))

(defun rsp-arcs-validp (arcs bound)
  (if (endp arcs)
      t
    (and (rsp-arc-validp (car arcs) bound)
         (rsp-arcs-validp (cdr arcs) bound))))

(defun rsp-item-validp (item bound)
  (and (consp item)
       (symbolp (car item))
       (rsp-arcs-validp (cdr item) bound)
       (if (zp bound)
           (endp (cdr item))
         (consp (cdr item)))))

(defun rsp-prefix-validp (n spec)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (and (rsp-prefix-validp (1- n) spec)
         (rsp-item-validp (nth (1- n) spec) (1- n)))))

(defun rsp-spec-validp (spec)
  (and (consp spec)
       (rsp-prefix-validp (len spec) spec)
       (no-duplicatesp-equal (rsp-nodes spec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Graph and ADP compilation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rsp-edge-for-arc (arc destination spec)
  (vwc-edge (rsp-node-at (rsp-arc-pred arc) spec)
            (symbol-fix destination)
            (rsp-arc-weight arc)))

(defun rsp-edges-for-arcs (arcs destination spec)
  (if (endp arcs)
      nil
    (cons (rsp-edge-for-arc (car arcs) destination spec)
          (rsp-edges-for-arcs (cdr arcs) destination spec))))

(defun rsp-graph-aux (items spec)
  (if (endp items)
      nil
    (append (rsp-edges-for-arcs (cdar items) (caar items) spec)
            (rsp-graph-aux (cdr items) spec))))

(defun rsp-graph (spec)
  (rsp-graph-aux spec spec))

(defun rsp-adp-rules (arcs)
  (if (endp arcs)
      nil
    (cons (list (rsp-arc-weight (car arcs))
                (rsp-arc-pred (car arcs)))
          (rsp-adp-rules (cdr arcs)))))

(defun rsp-adp-program-aux (items index)
  (if (endp items)
      nil
    (cons (cons (if (zp index) 0 nil)
                (rsp-adp-rules (cdar items)))
          (rsp-adp-program-aux (cdr items) (1+ (nfix index))))))

(defun rsp-adp-program (spec)
  (rsp-adp-program-aux spec 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Certificate-producing dynamic program
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rsp-entry-cost (entry)
  (nfix (car entry)))

(defun rsp-entry-path (entry)
  (cdr entry))

(defun rsp-chart-ref (index chart)
  (let ((look (assoc-equal (nfix index) chart)))
    (if look
        (cdr look)
      (cons 0 nil))))

(defun rsp-candidate (arc destination spec chart)
  (let* ((pred (rsp-arc-pred arc))
         (old (rsp-chart-ref pred chart))
         (edge (rsp-edge-for-arc arc destination spec)))
    (cons (+ (rsp-entry-cost old)
             (rsp-arc-weight arc))
          (append (rsp-entry-path old)
                  (list edge)))))

(defun rsp-better-entry (left right)
  (if (<= (rsp-entry-cost left)
          (rsp-entry-cost right))
      left
    right))

(defun rsp-best-candidate (arcs destination spec chart)
  (if (endp (cdr arcs))
      (rsp-candidate (car arcs) destination spec chart)
    (rsp-better-entry
     (rsp-candidate (car arcs) destination spec chart)
     (rsp-best-candidate (cdr arcs) destination spec chart))))

(defun rsp-run-aux (items spec index chart)
  (if (endp items)
      chart
    (let* ((item (car items))
           (entry (if (zp index)
                      (cons 0 nil)
                    (rsp-best-candidate (cdr item)
                                        (car item)
                                        spec chart))))
      (rsp-run-aux (cdr items)
                   spec
                   (1+ (nfix index))
                   (acons (nfix index) entry chart)))))

(defun rsp-run (spec)
  (rsp-run-aux spec spec 0 nil))

(defun rsp-potentials-aux (items index chart)
  (if (endp items)
      nil
    (omap::update
     (symbol-fix (caar items))
     (rsp-entry-cost (rsp-chart-ref index chart))
     (rsp-potentials-aux (cdr items) (1+ (nfix index)) chart))))

(defun rsp-potentials (spec chart)
  (rsp-potentials-aux spec 0 chart))

(defun rsp-solve (target spec)
  (let* ((chart (rsp-run spec))
         (entry (rsp-chart-ref target chart)))
    (list (rsp-entry-cost entry)
          (rsp-entry-path entry)
          (rsp-potentials spec chart))))

(defun rsp-solution-cost (solution)
  (nfix (car solution)))

(defun rsp-solution-path (solution)
  (cadr solution))

(defun rsp-solution-potentials (solution)
  (caddr solution))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Executable pressure test
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *rsp-example*
  '((a)
    (c (0 1))
    (b (0 3) (1 1))
    (d (2 2) (1 5))
    (e (3 1) (2 6))))

(defconst *rsp-example-solution*
  (rsp-solve 4 *rsp-example*))

(assert-event (rsp-spec-validp *rsp-example*))
(assert-event (equal (rsp-solution-cost *rsp-example-solution*) 5))
(assert-event
 (equal (rsp-solution-path *rsp-example-solution*)
        (list (vwc-edge 'a 'c 1)
              (vwc-edge 'c 'b 1)
              (vwc-edge 'b 'd 2)
              (vwc-edge 'd 'e 1))))
(assert-event
 (mwp-optimal-certificate-p
  (rsp-solution-path *rsp-example-solution*)
  (rsp-graph *rsp-example*)
  'a 'e
  (rsp-solution-potentials *rsp-example-solution*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Logical chart and path-certificate invariant
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rsp-entry-goodp (entry index spec)
  (and (vwc-certificate-p (rsp-entry-path entry)
                          (rsp-graph spec)
                          (rsp-node-at 0 spec)
                          (rsp-node-at index spec))
       (equal (rsp-entry-cost entry)
              (vwc-path-cost (rsp-entry-path entry)))))

(defun rsp-chart-goodp (n chart spec)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (and (rsp-chart-goodp (1- n) chart spec)
         (rsp-entry-goodp (rsp-chart-ref (1- n) chart)
                          (1- n)
                          spec))))

(defun rsp-build-chart (n spec)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (let* ((index (1- n))
           (chart (rsp-build-chart index spec))
           (item (nth index spec))
           (entry (if (zp index)
                      (cons 0 nil)
                    (rsp-best-candidate (cdr item)
                                        (car item)
                                        spec chart))))
      (acons index entry chart))))

(defthm rsp-chart-ref-of-acons-same
  (equal (rsp-chart-ref index (acons (nfix index) entry chart))
         entry)
  :hints (("Goal" :in-theory (enable rsp-chart-ref))))

(defthm rsp-chart-ref-of-acons-different
  (implies (not (equal (nfix i) (nfix j)))
           (equal (rsp-chart-ref i (acons (nfix j) entry chart))
                  (rsp-chart-ref i chart)))
  :hints (("Goal" :in-theory (enable rsp-chart-ref))))

(defthm rsp-chart-goodp-ref
  (implies (and (rsp-chart-goodp n chart spec)
                (natp index)
                (< index (nfix n)))
           (rsp-entry-goodp (rsp-chart-ref index chart) index spec))
  :hints (("Goal"
           :induct (rsp-chart-goodp n chart spec)
           :in-theory (enable rsp-chart-goodp))))

(defthm rsp-edge-for-arc-member-of-edges-for-arcs
  (implies (member-equal arc arcs)
           (member-equal (rsp-edge-for-arc arc destination spec)
                         (rsp-edges-for-arcs arcs destination spec)))
  :hints (("Goal"
           :induct (len arcs)
           :in-theory (e/d (rsp-edges-for-arcs member-equal)
                           (rsp-edge-for-arc)))))

(defthm rsp-edge-for-arc-member-of-graph-aux
  (implies (and (member-equal item items)
                (member-equal arc (cdr item)))
           (member-equal
            (rsp-edge-for-arc arc (car item) spec)
            (rsp-graph-aux items spec)))
  :hints (("Goal"
           :induct (rsp-graph-aux items spec)
           :in-theory (e/d (rsp-graph-aux member-equal)
                           (rsp-edge-for-arc)))))

(defthm rsp-edge-for-arc-member-of-graph
  (implies (and (natp index)
                (< index (len spec))
                (member-equal arc (rsp-arcs-at index spec)))
           (member-equal
            (rsp-edge-for-arc arc (rsp-node-at index spec) spec)
            (rsp-graph spec)))
  :hints (("Goal"
           :use ((:instance rsp-edge-for-arc-member-of-graph-aux
                            (item (nth index spec))
                            (items spec)))
           :in-theory (enable rsp-arcs-at rsp-node-at rsp-graph))))

(defthm rsp-singleton-arc-certificate
  (implies (and (natp index)
                (< index (len spec))
                (rsp-arc-validp arc index)
                (member-equal arc (rsp-arcs-at index spec)))
           (vwc-certificate-p
            (list (rsp-edge-for-arc arc (rsp-node-at index spec) spec))
            (rsp-graph spec)
            (rsp-node-at (rsp-arc-pred arc) spec)
            (rsp-node-at index spec)))
  :hints (("Goal"
           :use ((:instance rsp-edge-for-arc-member-of-graph))
           :in-theory (enable vwc-certificate-p
                              vwc-path-in-graph-p
                              vwc-path-chains-p
                              rsp-edge-for-arc
                              rsp-arc-validp
                              rsp-arc-pred))))

(defthm rsp-candidate-good
  (implies (and (natp index)
                (< index (len spec))
                (rsp-chart-goodp index chart spec)
                (rsp-arc-validp arc index)
                (member-equal arc (rsp-arcs-at index spec)))
           (rsp-entry-goodp
            (rsp-candidate arc (rsp-node-at index spec) spec chart)
            index spec))
  :hints (("Goal"
           :use ((:instance rsp-chart-goodp-ref
                            (n index)
                            (index (rsp-arc-pred arc)))
                 (:instance rsp-singleton-arc-certificate)
                 (:instance vwc-certificate-compose
                            (left (rsp-entry-path
                                   (rsp-chart-ref (rsp-arc-pred arc) chart)))
                            (right (list (rsp-edge-for-arc
                                          arc (rsp-node-at index spec) spec)))
                            (graph (rsp-graph spec))
                            (start (rsp-node-at 0 spec))
                            (middle (rsp-node-at (rsp-arc-pred arc) spec))
                            (finish (rsp-node-at index spec))))
           :in-theory (enable rsp-entry-goodp
                              rsp-candidate
                              rsp-arc-validp
                              rsp-arc-pred
                              rsp-arc-weight
                              rsp-entry-cost
                              rsp-entry-path
                              vwc-path-cost-of-append))))

(defthm rsp-entry-goodp-of-better
  (implies (and (rsp-entry-goodp left index spec)
                (rsp-entry-goodp right index spec))
           (rsp-entry-goodp (rsp-better-entry left right) index spec))
  :hints (("Goal" :in-theory (enable rsp-better-entry))))

(defthm rsp-best-candidate-good
  (implies (and (consp arcs)
                (natp index)
                (< index (len spec))
                (rsp-chart-goodp index chart spec)
                (rsp-arcs-validp arcs index)
                (subsetp-equal arcs (rsp-arcs-at index spec)))
           (rsp-entry-goodp
            (rsp-best-candidate arcs (rsp-node-at index spec) spec chart)
            index spec))
  :hints (("Goal"
           :induct (rsp-best-candidate arcs (rsp-node-at index spec) spec chart)
           :in-theory
           (e/d (rsp-best-candidate rsp-arcs-validp)
                (rsp-entry-goodp rsp-candidate rsp-better-entry
                 rsp-node-at rsp-arcs-at)))))

(defthm rsp-source-entry-good
  (implies (and (consp spec)
                (symbolp (caar spec)))
           (rsp-entry-goodp (cons 0 nil) 0 spec))
  :hints (("Goal"
           :in-theory (enable rsp-entry-goodp
                              rsp-entry-cost
                              rsp-entry-path
                              vwc-certificate-p
                              vwc-path-in-graph-p
                              vwc-path-chains-p
                              vwc-path-cost
                              rsp-node-at))))

(defthm rsp-item-validp-from-prefix
  (implies (and (rsp-prefix-validp n spec)
                (natp index)
                (< index (nfix n)))
           (rsp-item-validp (nth index spec) index))
  :hints (("Goal"
           :induct (rsp-prefix-validp n spec)
           :in-theory (enable rsp-prefix-validp))))

(defthm rsp-new-entry-good
  (implies
   (and (natp index)
        (< index (len spec))
        (rsp-prefix-validp (1+ index) spec)
        (rsp-chart-goodp index chart spec))
   (rsp-entry-goodp
    (if (zp index)
        (cons 0 nil)
      (rsp-best-candidate (cdr (nth index spec))
                          (car (nth index spec))
                          spec chart))
    index spec))
  :hints
  (("Goal"
    :use ((:instance rsp-item-validp-from-prefix
                     (n (1+ index)))
          (:instance rsp-best-candidate-good
                     (arcs (cdr (nth index spec))))
          (:instance rsp-source-entry-good))
    :in-theory
    (e/d (rsp-prefix-validp rsp-item-validp rsp-arcs-at rsp-node-at)
         (rsp-entry-goodp rsp-best-candidate
          rsp-best-candidate-good rsp-source-entry-good
          rsp-item-validp-from-prefix)))))

(defthm rsp-chart-goodp-of-acons-above
  (implies (and (rsp-chart-goodp n chart spec)
                (natp key)
                (<= (nfix n) key))
           (rsp-chart-goodp n (acons key entry chart) spec))
  :hints (("Goal"
           :induct (rsp-chart-goodp n chart spec)
           :in-theory (enable rsp-chart-goodp))))

(defthm rsp-chart-goodp-of-build-chart
  (implies (and (rsp-prefix-validp n spec)
                (<= (nfix n) (len spec)))
           (rsp-chart-goodp n (rsp-build-chart n spec) spec))
  :hints
  (("Goal"
    :induct (rsp-build-chart n spec)
    :in-theory
    (e/d (rsp-build-chart rsp-chart-goodp rsp-prefix-validp)
         (rsp-entry-goodp rsp-best-candidate)))
   (and stable-under-simplificationp
        '(:use ((:instance rsp-chart-goodp-of-acons-above
                           (n (1- n))
                           (chart (rsp-build-chart (1- n) spec))
                           (key (1- n))
                           (entry (if (zp (1- n))
                                      (cons 0 nil)
                                    (rsp-best-candidate
                                     (cdr (nth (1- n) spec))
                                     (car (nth (1- n) spec))
                                     spec
                                     (rsp-build-chart (1- n) spec)))))
                 (:instance rsp-new-entry-good
                            (index (1- n))
                            (chart (rsp-build-chart (1- n) spec))))
                :in-theory
                (disable rsp-chart-goodp-of-acons-above
                         rsp-new-entry-good)))))

