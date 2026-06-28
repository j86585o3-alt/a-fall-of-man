; zah-ranked-shortest-path-executable.lisp
;
; Refinement from the forward ranked-graph executor to the logical chart,
; followed by executable optimality theorems.

(in-package "ACL2")

(include-book "zag-ranked-shortest-path-optimality")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 11. The forward executor is exactly the logical chart construction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rsp-build-chart-of-successor
  (implies (natp index)
           (equal
            (rsp-build-chart (1+ index) spec)
            (acons index
                   (if (zp index)
                       (cons 0 nil)
                     (rsp-best-candidate
                      (cdr (nth index spec))
                      (car (nth index spec))
                      spec
                      (rsp-build-chart index spec)))
                   (rsp-build-chart index spec))))
  :hints (("Goal"
           :in-theory (enable rsp-build-chart))))

(defthm rsp-build-chart-zero
  (equal (rsp-build-chart 0 spec) nil)
  :hints (("Goal" :in-theory (enable rsp-build-chart))))

(defthm rsp-run-aux-from-logical-prefix
  (implies
   (and (natp index)
        (<= index (len spec)))
   (equal
    (rsp-run-aux (nthcdr index spec)
                 spec index
                 (rsp-build-chart index spec))
    (rsp-build-chart (len spec) spec)))
  :hints
  (("Goal"
    :induct (rsp-index-to-end-induct index spec)
    :in-theory
    (e/d (rsp-index-to-end-induct rsp-run-aux)
         (rsp-build-chart rsp-best-candidate)))
   (and stable-under-simplificationp
        '(:use
          ((:instance rsp-build-chart-of-successor)
           (:instance rsp-cdr-of-nthcdr-tail
                      (items (nthcdr index spec))))
          :in-theory
          (disable rsp-build-chart-of-successor
                   rsp-cdr-of-nthcdr-tail
                   rsp-build-chart rsp-best-candidate)))))

(defthm rsp-run-equals-build-chart
  (equal (rsp-run spec)
         (rsp-build-chart (len spec) spec))
  :hints
  (("Goal"
    :use ((:instance rsp-run-aux-from-logical-prefix
                     (index 0)))
    :in-theory
    (e/d (rsp-run rsp-build-chart-zero)
         (rsp-run-aux-from-logical-prefix
          rsp-run-aux rsp-build-chart)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 12. Executable certificate and global-optimality interface
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rsp-run-emits-optimal-certificate
  (implies
   (and (rsp-spec-validp spec)
        (symbol-listp (rsp-nodes spec))
        (natp target)
        (< target (len spec)))
   (mwp-optimal-certificate-p
    (rsp-entry-path (rsp-chart-ref target (rsp-run spec)))
    (rsp-graph spec)
    (rsp-node-at 0 spec)
    (rsp-node-at target spec)
    (rsp-potentials spec (rsp-run spec))))
  :hints
  (("Goal"
    :use ((:instance rsp-generated-optimal-certificate-p))
    :in-theory
    (e/d (rsp-run-equals-build-chart)
         (rsp-generated-optimal-certificate-p
          rsp-run rsp-build-chart)))))

(defthm rsp-run-answer-is-globally-optimal
  (implies
   (and (rsp-spec-validp spec)
        (symbol-listp (rsp-nodes spec))
        (natp target)
        (< target (len spec))
        (vwc-certificate-p competitor
                           (rsp-graph spec)
                           (rsp-node-at 0 spec)
                           (rsp-node-at target spec)))
   (<= (rsp-entry-cost
        (rsp-chart-ref target (rsp-run spec)))
       (vwc-path-cost competitor)))
  :hints
  (("Goal"
    :use ((:instance rsp-generated-answer-is-globally-optimal))
    :in-theory
    (e/d (rsp-run-equals-build-chart)
         (rsp-generated-answer-is-globally-optimal
          rsp-run rsp-build-chart)))))

(defthm rsp-solve-emits-optimal-certificate
  (implies
   (and (rsp-spec-validp spec)
        (symbol-listp (rsp-nodes spec))
        (natp target)
        (< target (len spec)))
   (mwp-optimal-certificate-p
    (rsp-solution-path (rsp-solve target spec))
    (rsp-graph spec)
    (rsp-node-at 0 spec)
    (rsp-node-at target spec)
    (rsp-solution-potentials (rsp-solve target spec))))
  :hints
  (("Goal"
    :use ((:instance rsp-run-emits-optimal-certificate))
    :in-theory
    (e/d (rsp-solve rsp-solution-path rsp-solution-potentials)
         (rsp-run-emits-optimal-certificate)))))

(defthm rsp-solve-answer-is-globally-optimal
  (implies
   (and (rsp-spec-validp spec)
        (symbol-listp (rsp-nodes spec))
        (natp target)
        (< target (len spec))
        (vwc-certificate-p competitor
                           (rsp-graph spec)
                           (rsp-node-at 0 spec)
                           (rsp-node-at target spec)))
   (<= (rsp-solution-cost (rsp-solve target spec))
       (vwc-path-cost competitor)))
  :hints
  (("Goal"
    :use ((:instance rsp-run-answer-is-globally-optimal))
    :in-theory
    (e/d (rsp-solve rsp-solution-cost)
         (rsp-run-answer-is-globally-optimal)))))
