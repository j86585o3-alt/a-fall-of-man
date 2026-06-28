; zag-ranked-shortest-path-optimality.lisp
;
; Generic feasible-potential and global-optimality bridge for ranked graphs.

(in-package "ACL2")

(include-book "zaf-ranked-shortest-path-certificates")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 8. Every compiled edge satisfies its Bellman inequality
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm vwc-graph-model-p-of-append
  (equal (vwc-graph-model-p (append left right) potentials)
         (and (vwc-graph-model-p left potentials)
              (vwc-graph-model-p right potentials)))
  :hints (("Goal"
           :induct (len left)
           :in-theory (enable vwc-graph-model-p))))

(defthm vwc-graph-model-p-of-nil
  (vwc-graph-model-p nil potentials)
  :hints (("Goal" :in-theory (enable vwc-graph-model-p))))

(defthm rsp-chart-relaxedp-ref
  (implies (and (rsp-chart-relaxedp n chart spec)
                (natp index)
                (< index (nfix n)))
           (rsp-arcs-relaxedp (rsp-arcs-at index spec)
                              index chart))
  :hints (("Goal"
           :induct (rsp-chart-relaxedp n chart spec)
           :in-theory (enable rsp-chart-relaxedp))))

(defthm rsp-arc-pred-less-than-spec-length
  (implies (and (rsp-arc-validp arc index)
                (natp index)
                (< index (len spec)))
           (< (rsp-arc-pred arc) (len spec)))
  :hints (("Goal" :in-theory (enable rsp-arc-validp))))

(defthm rsp-edge-for-arc-model
  (implies
   (and (symbol-listp (rsp-nodes spec))
        (no-duplicatesp-equal (rsp-nodes spec))
        (natp index)
        (< index (len spec))
        (rsp-arc-validp arc index)
        (<= (rsp-entry-cost (rsp-chart-ref index chart))
            (+ (rsp-entry-cost
                (rsp-chart-ref (rsp-arc-pred arc) chart))
               (rsp-arc-weight arc))))
   (vwc-edge-model-p
    (rsp-edge-for-arc arc (rsp-node-at index spec) spec)
    (rsp-potentials spec chart)))
  :hints
  (("Goal"
    :use ((:instance rsp-potential-is-chart-cost
                     (index index))
          (:instance rsp-potential-is-chart-cost
                     (index (rsp-arc-pred arc)))
          (:instance rsp-arc-pred-less-than-spec-length))
    :in-theory
    (e/d (vwc-edge-model-p rsp-edge-for-arc rsp-arc-validp)
         (rsp-potential-is-chart-cost
          rsp-arc-pred-less-than-spec-length vwc-potential
          rsp-chart-ref rsp-entry-cost rsp-potentials
          rsp-node-at rsp-arc-pred rsp-arc-weight)))))

(defthm rsp-edges-for-arcs-model
  (implies
   (and (symbol-listp (rsp-nodes spec))
        (no-duplicatesp-equal (rsp-nodes spec))
        (natp index)
        (< index (len spec))
        (rsp-arcs-validp arcs index)
        (rsp-arcs-relaxedp arcs index chart))
   (vwc-graph-model-p
    (rsp-edges-for-arcs arcs (rsp-node-at index spec) spec)
    (rsp-potentials spec chart)))
  :hints
  (("Goal"
    :induct (rsp-arcs-validp arcs index)
    :in-theory
    (e/d (rsp-arcs-validp rsp-arcs-relaxedp
                          rsp-edges-for-arcs vwc-graph-model-p)
         (rsp-edge-for-arc rsp-arc-validp rsp-chart-ref
          rsp-entry-cost rsp-potentials)))
   (and stable-under-simplificationp
        '(:use ((:instance rsp-edge-for-arc-model
                           (arc (car arcs))))
                :in-theory
                (disable rsp-edge-for-arc-model
                         rsp-edge-for-arc rsp-arc-validp rsp-chart-ref
                         rsp-entry-cost rsp-potentials)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 9. Lift the local inequalities across the complete ranked graph
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rsp-node-at-of-nthcdr-head
  (implies (and (equal items (nthcdr index spec))
                (symbolp (caar items)))
           (equal (rsp-node-at index spec)
                  (caar items)))
  :hints (("Goal"
           :in-theory (enable rsp-node-at))))

(defthm rsp-arcs-at-of-nthcdr-head
  (implies (equal items (nthcdr index spec))
           (equal (rsp-arcs-at index spec)
                  (cdar items)))
  :hints (("Goal"
           :in-theory (enable rsp-arcs-at))))

(defthm rsp-cdr-of-nthcdr-tail
  (implies (and (equal items (nthcdr index spec))
                (natp index))
           (equal (cdr items)
                  (nthcdr (1+ index) spec)))
  :hints (("Goal"
           :in-theory (enable nthcdr))))

(defun rsp-tail-induct (items index)
  (declare (irrelevant index))
  (if (endp items)
      nil
    (rsp-tail-induct (cdr items) (1+ (nfix index)))))

(defun rsp-index-to-end-induct (index spec)
  (declare (xargs :measure (len (nthcdr index spec))))
  (if (endp (nthcdr index spec))
      nil
    (rsp-index-to-end-induct (1+ (nfix index)) spec)))

(defthm rsp-graph-aux-index-model
  (implies
   (and (natp index)
        (rsp-prefix-validp (len spec) spec)
        (rsp-chart-relaxedp (len spec) chart spec)
        (symbol-listp (rsp-nodes spec))
        (no-duplicatesp-equal (rsp-nodes spec)))
   (vwc-graph-model-p
    (rsp-graph-aux (nthcdr index spec) spec)
    (rsp-potentials spec chart)))
  :hints
  (("Goal"
    :induct (rsp-index-to-end-induct index spec)
    :in-theory
    (e/d (rsp-index-to-end-induct rsp-graph-aux rsp-item-validp)
         (rsp-edges-for-arcs rsp-edge-for-arc
          rsp-chart-ref rsp-entry-cost rsp-potentials
          rsp-arcs-relaxedp rsp-arcs-validp
          vwc-graph-model-p)))
   (and stable-under-simplificationp
        '(:use
          ((:instance rsp-item-validp-from-prefix
                      (n (len spec)))
           (:instance rsp-chart-relaxedp-ref
                      (n (len spec)))
           (:instance rsp-node-at-of-nthcdr-head
                      (items (nthcdr index spec)))
           (:instance rsp-arcs-at-of-nthcdr-head
                      (items (nthcdr index spec)))
           (:instance rsp-cdr-of-nthcdr-tail
                      (items (nthcdr index spec)))
           (:instance rsp-edges-for-arcs-model
                      (arcs (cdr (car (nthcdr index spec)))))
           (:instance vwc-graph-model-p-of-append
                      (left (rsp-edges-for-arcs
                             (cdr (car (nthcdr index spec)))
                             (car (car (nthcdr index spec))) spec))
                      (right (rsp-graph-aux
                              (cdr (nthcdr index spec)) spec))
                      (potentials (rsp-potentials spec chart))))
          :in-theory
          (disable rsp-item-validp-from-prefix
                   rsp-chart-relaxedp-ref
                   rsp-node-at-of-nthcdr-head
                   rsp-arcs-at-of-nthcdr-head
                   rsp-cdr-of-nthcdr-tail
                   rsp-edges-for-arcs-model
                   vwc-graph-model-p-of-append
                   rsp-edges-for-arcs rsp-edge-for-arc
                   rsp-chart-ref rsp-entry-cost rsp-potentials
                   rsp-arcs-relaxedp rsp-arcs-validp
                   vwc-graph-model-p)))))

(defthm rsp-generated-potential-models-graph
  (implies
   (and (rsp-spec-validp spec)
        (symbol-listp (rsp-nodes spec)))
   (vwc-graph-model-p
    (rsp-graph spec)
    (rsp-potentials spec
                    (rsp-build-chart (len spec) spec))))
  :hints
  (("Goal"
    :use
    ((:instance rsp-chart-relaxedp-of-build-chart
                (n (len spec)))
     (:instance rsp-graph-aux-index-model
                (index 0)
                (chart (rsp-build-chart (len spec) spec))))
    :in-theory
    (e/d (rsp-spec-validp rsp-graph)
         (rsp-chart-relaxedp-of-build-chart
          rsp-graph-aux-index-model)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 10. The generated witness and potential pass the independent checker
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rsp-chart-ref-zero-of-build-chart
  (implies (and (natp n)
                (< 0 n))
           (equal (rsp-chart-ref 0 (rsp-build-chart n spec))
                  (cons 0 nil)))
  :hints
  (("Goal"
    :induct (rsp-build-chart n spec)
    :in-theory
    (e/d (rsp-build-chart)
         (rsp-chart-ref rsp-best-candidate)))
   (and stable-under-simplificationp
        '(:use ((:instance rsp-chart-ref-of-acons-same
                           (index 0)
                           (entry (cons 0 nil))
                           (chart nil))
                 (:instance rsp-chart-ref-of-acons-different
                           (i 0)
                           (j (1- n))
                           (entry (if (zp (1- n))
                                      (cons 0 nil)
                                    (rsp-best-candidate
                                     (cdr (nth (1- n) spec))
                                     (car (nth (1- n) spec))
                                     spec
                                     (rsp-build-chart (1- n) spec))))
                           (chart (rsp-build-chart (1- n) spec))))
                :in-theory
                (disable rsp-chart-ref-of-acons-same
                         rsp-chart-ref-of-acons-different
                         rsp-chart-ref rsp-best-candidate)))))

(defthm rsp-generated-target-entry-good
  (implies
   (and (rsp-spec-validp spec)
        (natp target)
        (< target (len spec)))
   (rsp-entry-goodp
    (rsp-chart-ref target (rsp-build-chart (len spec) spec))
    target spec))
  :hints
  (("Goal"
    :use
    ((:instance rsp-chart-goodp-of-build-chart
                (n (len spec)))
     (:instance rsp-chart-goodp-ref
                (n (len spec))
                (index target)
                (chart (rsp-build-chart (len spec) spec))))
    :in-theory
    (e/d (rsp-spec-validp)
         (rsp-chart-goodp-of-build-chart
          rsp-chart-goodp-ref)))))

(defthm rsp-generated-source-potential-zero
  (implies
   (and (rsp-spec-validp spec)
        (symbol-listp (rsp-nodes spec)))
   (equal
    (vwc-potential
     (rsp-node-at 0 spec)
     (rsp-potentials spec
                     (rsp-build-chart (len spec) spec)))
    0))
  :hints
  (("Goal"
    :use
    ((:instance rsp-potential-is-chart-cost
                (index 0)
                (chart (rsp-build-chart (len spec) spec)))
     (:instance rsp-chart-ref-zero-of-build-chart
                (n (len spec))))
    :in-theory
    (e/d (rsp-spec-validp rsp-entry-cost)
         (rsp-potential-is-chart-cost
          rsp-chart-ref-zero-of-build-chart)))))

(defthm rsp-generated-optimal-certificate-p
  (implies
   (and (rsp-spec-validp spec)
        (symbol-listp (rsp-nodes spec))
        (natp target)
        (< target (len spec)))
   (mwp-optimal-certificate-p
    (rsp-entry-path
     (rsp-chart-ref target
                    (rsp-build-chart (len spec) spec)))
    (rsp-graph spec)
    (rsp-node-at 0 spec)
    (rsp-node-at target spec)
    (rsp-potentials spec
                    (rsp-build-chart (len spec) spec))))
  :hints
  (("Goal"
    :use
    ((:instance rsp-generated-target-entry-good)
     (:instance rsp-generated-potential-models-graph)
     (:instance rsp-generated-source-potential-zero)
     (:instance rsp-potential-is-chart-cost
                (index target)
                (chart (rsp-build-chart (len spec) spec))))
    :in-theory
    (e/d (mwp-optimal-certificate-p rsp-entry-goodp)
         (rsp-generated-target-entry-good
          rsp-generated-potential-models-graph
          rsp-generated-source-potential-zero
          rsp-potential-is-chart-cost
          rsp-chart-ref rsp-entry-cost rsp-entry-path
          rsp-potentials rsp-graph)))))

(defthm rsp-generated-answer-is-globally-optimal
  (implies
   (and (rsp-spec-validp spec)
        (symbol-listp (rsp-nodes spec))
        (natp target)
        (< target (len spec))
        (vwc-certificate-p competitor
                           (rsp-graph spec)
                           (rsp-node-at 0 spec)
                           (rsp-node-at target spec)))
   (<=
    (rsp-entry-cost
     (rsp-chart-ref target
                    (rsp-build-chart (len spec) spec)))
    (vwc-path-cost competitor)))
  :hints
  (("Goal"
    :use
    ((:instance rsp-generated-target-entry-good)
     (:instance rsp-generated-optimal-certificate-p)
     (:instance mwp-optimal-certificate-lower-bound
                (witness
                 (rsp-entry-path
                  (rsp-chart-ref target
                                 (rsp-build-chart (len spec) spec))))
                (graph (rsp-graph spec))
                (source (rsp-node-at 0 spec))
                (target (rsp-node-at target spec))
                (potentials
                 (rsp-potentials spec
                                 (rsp-build-chart (len spec) spec)))))
    :in-theory
    (e/d (rsp-entry-goodp)
         (rsp-generated-target-entry-good
          rsp-generated-optimal-certificate-p
          mwp-optimal-certificate-lower-bound
          rsp-chart-ref rsp-entry-cost rsp-entry-path
          rsp-potentials rsp-graph)))))
