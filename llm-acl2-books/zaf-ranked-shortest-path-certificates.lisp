; zaf-ranked-shortest-path-certificates.lisp
;
; Bellman inequalities, feasible potentials, and the generic optimality bridge
; for the ranked shortest-path compiler.

(in-package "ACL2")

(include-book "zae-ranked-shortest-path-compiler")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 6. Bellman inequalities for every compiled edge
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rsp-arcs-relaxedp (arcs index chart)
  (if (endp arcs)
      t
    (and
     (<= (rsp-entry-cost (rsp-chart-ref index chart))
         (+ (rsp-entry-cost
             (rsp-chart-ref (rsp-arc-pred (car arcs)) chart))
            (rsp-arc-weight (car arcs))))
     (rsp-arcs-relaxedp (cdr arcs) index chart))))

(defun rsp-chart-relaxedp (n chart spec)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (and (rsp-chart-relaxedp (1- n) chart spec)
         (rsp-arcs-relaxedp (rsp-arcs-at (1- n) spec)
                            (1- n) chart))))

(defthm rsp-better-entry-cost-at-most-left
  (<= (rsp-entry-cost (rsp-better-entry left right))
      (rsp-entry-cost left))
  :hints (("Goal" :in-theory (enable rsp-better-entry))))

(defthm rsp-better-entry-cost-at-most-right
  (<= (rsp-entry-cost (rsp-better-entry left right))
      (rsp-entry-cost right))
  :hints (("Goal" :in-theory (enable rsp-better-entry))))

(defthm rsp-best-candidate-cost-upper-bound
  (implies (and (consp arcs)
                (member-equal arc arcs))
           (<= (rsp-entry-cost
                (rsp-best-candidate arcs destination spec chart))
               (rsp-entry-cost
                (rsp-candidate arc destination spec chart))))
  :hints
  (("Goal"
    :induct (rsp-best-candidate arcs destination spec chart)
    :in-theory
    (e/d (rsp-best-candidate member-equal)
         (rsp-entry-cost rsp-candidate rsp-better-entry)))
   (and stable-under-simplificationp
        '(:use ((:instance rsp-better-entry-cost-at-most-left
                           (left (rsp-candidate (car arcs)
                                                destination spec chart))
                           (right (rsp-best-candidate (cdr arcs)
                                                      destination spec chart)))
                 (:instance rsp-better-entry-cost-at-most-right
                           (left (rsp-candidate (car arcs)
                                                destination spec chart))
                           (right (rsp-best-candidate (cdr arcs)
                                                      destination spec chart))))
                :in-theory
                (disable rsp-better-entry-cost-at-most-left
                         rsp-better-entry-cost-at-most-right)))))

(defthm rsp-entry-cost-of-candidate
  (equal (rsp-entry-cost (rsp-candidate arc destination spec chart))
         (+ (rsp-entry-cost
             (rsp-chart-ref (rsp-arc-pred arc) chart))
            (rsp-arc-weight arc)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable rsp-candidate rsp-entry-cost))))

(defthm rsp-new-entry-relaxes-member
  (implies
   (and (natp index)
        (consp arcs)
        (member-equal arc arcs)
        (rsp-arc-validp arc index))
   (<= (rsp-entry-cost
        (rsp-chart-ref
         index
         (acons index
                (rsp-best-candidate arcs destination spec chart)
                chart)))
       (+ (rsp-entry-cost
           (rsp-chart-ref
            (rsp-arc-pred arc)
            (acons index
                   (rsp-best-candidate arcs destination spec chart)
                   chart)))
          (rsp-arc-weight arc))))
  :hints
  (("Goal"
    :use ((:instance rsp-best-candidate-cost-upper-bound)
          (:instance rsp-entry-cost-of-candidate))
    :in-theory
    (e/d (rsp-arc-validp)
         (rsp-best-candidate rsp-candidate rsp-entry-cost)))))

(defthm rsp-arcs-relaxedp-for-new-entry-aux
  (implies
   (and (consp full-arcs)
        (subsetp-equal arcs full-arcs)
        (rsp-arcs-validp arcs index)
        (natp index))
   (rsp-arcs-relaxedp
    arcs index
    (acons index
           (rsp-best-candidate full-arcs destination spec chart)
           chart)))
  :hints
  (("Goal"
    :induct (rsp-arcs-validp arcs index)
    :in-theory
    (e/d (rsp-arcs-relaxedp rsp-arcs-validp)
         (rsp-chart-ref rsp-entry-cost rsp-best-candidate
          rsp-candidate rsp-arc-pred rsp-arc-weight)))
   (and stable-under-simplificationp
        '(:use ((:instance rsp-new-entry-relaxes-member
                           (arcs full-arcs)
                           (arc (car arcs))))
                :in-theory
                (disable rsp-new-entry-relaxes-member
                         rsp-chart-ref rsp-entry-cost rsp-best-candidate
                         rsp-candidate rsp-arc-pred rsp-arc-weight)))))

(defthm rsp-arcs-relaxedp-for-new-entry
  (implies (and (consp arcs)
                (rsp-arcs-validp arcs index)
                (natp index))
           (rsp-arcs-relaxedp
            arcs index
            (acons index
                   (rsp-best-candidate arcs destination spec chart)
                   chart)))
  :hints (("Goal"
           :use ((:instance rsp-arcs-relaxedp-for-new-entry-aux
                            (full-arcs arcs)))
           :in-theory (disable rsp-arcs-relaxedp-for-new-entry-aux))))

(defthm rsp-chart-ref-of-acons-greater
  (implies (and (natp key)
                (< (nfix index) key))
           (equal (rsp-chart-ref index (acons key entry chart))
                  (rsp-chart-ref index chart)))
  :hints (("Goal"
           :use ((:instance rsp-chart-ref-of-acons-different
                            (i index) (j key)))
           :in-theory (disable rsp-chart-ref-of-acons-different))))

(defthm rsp-arcs-relaxedp-of-acons-above
  (implies (and (rsp-arcs-relaxedp arcs index chart)
                (natp key)
                (< (nfix index) key)
                (rsp-arcs-validp arcs index))
           (rsp-arcs-relaxedp arcs index
                              (acons key entry chart)))
  :hints
  (("Goal"
    :induct (rsp-arcs-validp arcs index)
    :in-theory
    (e/d (rsp-arcs-relaxedp rsp-arcs-validp rsp-arc-validp)
         (rsp-chart-ref rsp-entry-cost)))
   (and stable-under-simplificationp
        '(:use ((:instance rsp-chart-ref-of-acons-greater
                           (index index))
                 (:instance rsp-chart-ref-of-acons-greater
                           (index (rsp-arc-pred (car arcs)))))
                :in-theory
                (disable rsp-chart-ref-of-acons-greater
                         rsp-chart-ref rsp-entry-cost)))))

(defthm rsp-arcs-relaxedp-when-not-consp
  (implies (not (consp arcs))
           (rsp-arcs-relaxedp arcs index chart))
  :hints (("Goal" :in-theory (enable rsp-arcs-relaxedp))))

(defthm rsp-chart-relaxedp-of-acons-above
  (implies (and (natp n)
                (rsp-chart-relaxedp n chart spec)
                (rsp-prefix-validp n spec)
                (natp key)
                (<= (nfix n) key))
           (rsp-chart-relaxedp n (acons key entry chart) spec))
  :hints
  (("Goal"
    :induct (rsp-prefix-validp n spec)
    :in-theory
    (e/d (rsp-chart-relaxedp rsp-prefix-validp rsp-item-validp
                             rsp-arcs-at)
         (rsp-arcs-relaxedp)))
   (and stable-under-simplificationp
        '(:use ((:instance rsp-arcs-relaxedp-of-acons-above
                           (arcs (rsp-arcs-at (1- n) spec))
                           (index (1- n))))
                :in-theory
                (disable rsp-arcs-relaxedp-of-acons-above
                         rsp-arcs-relaxedp)))))

(defthm rsp-chart-relaxedp-of-build-chart
  (implies (and (rsp-prefix-validp n spec)
                (<= (nfix n) (len spec)))
           (rsp-chart-relaxedp n (rsp-build-chart n spec) spec))
  :hints
  (("Goal"
    :induct (rsp-build-chart n spec)
    :in-theory
    (e/d (rsp-build-chart rsp-chart-relaxedp rsp-prefix-validp
                          rsp-item-validp rsp-arcs-at)
         (rsp-best-candidate rsp-arcs-relaxedp)))
   (and stable-under-simplificationp
        '(:use ((:instance rsp-chart-relaxedp-of-acons-above
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
                 (:instance rsp-arcs-relaxedp-for-new-entry
                            (arcs (cdr (nth (1- n) spec)))
                            (index (1- n))
                            (destination (car (nth (1- n) spec)))
                            (chart (rsp-build-chart (1- n) spec))))
                :in-theory
                (disable rsp-chart-relaxedp-of-acons-above
                         rsp-arcs-relaxedp-for-new-entry)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 7. Potentials expose chart costs at every ranked node
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rsp-index-induct (index items)
  (if (or (zp index) (endp items))
      nil
    (rsp-index-induct (1- index) (cdr items))))

(defun rsp-potential-induct (index items base)
  (declare (irrelevant base))
  (if (or (zp index) (endp items))
      nil
    (rsp-potential-induct (1- index)
                          (cdr items)
                          (1+ (nfix base)))))

(defthm rsp-nodes-of-cdr
  (equal (rsp-nodes (cdr items))
         (cdr (rsp-nodes items)))
  :hints (("Goal" :in-theory (enable rsp-nodes))))

(defthm rsp-node-at-zero
  (equal (rsp-node-at 0 items)
         (symbol-fix (caar items)))
  :hints (("Goal" :in-theory (enable rsp-node-at))))

(defthm rsp-node-at-successor
  (equal (rsp-node-at (1+ (nfix index)) items)
         (rsp-node-at index (cdr items)))
  :hints (("Goal" :in-theory (enable rsp-node-at))))

(defthm rsp-node-at-member-of-nodes
  (implies (and (symbol-listp (rsp-nodes items))
                (natp index)
                (< index (len items)))
           (member-equal (rsp-node-at index items)
                         (rsp-nodes items)))
  :hints (("Goal"
           :induct (rsp-index-induct index items)
           :in-theory (enable rsp-index-induct rsp-node-at rsp-nodes))))

(defthm rsp-first-node-differs-from-later-node
  (implies (and (symbol-listp (rsp-nodes items))
                (no-duplicatesp-equal (rsp-nodes items))
                (natp index)
                (< 0 index)
                (< index (len items)))
           (not (equal (symbol-fix (caar items))
                       (rsp-node-at index items))))
  :hints (("Goal"
           :use ((:instance rsp-node-at-member-of-nodes
                            (items (cdr items))
                            (index (1- index))))
           :in-theory (enable rsp-nodes rsp-node-at))))

(defthm rsp-assoc-of-potentials-aux
  (implies
   (and (symbol-listp (rsp-nodes items))
        (no-duplicatesp-equal (rsp-nodes items))
        (natp base)
        (natp index)
        (< index (len items)))
   (equal
    (omap::assoc (rsp-node-at index items)
                 (rsp-potentials-aux items base chart))
    (cons (rsp-node-at index items)
          (rsp-entry-cost
           (rsp-chart-ref (+ base index) chart)))))
  :hints
  (("Goal"
    :induct (rsp-potential-induct index items base)
    :in-theory
    (e/d (rsp-potential-induct rsp-potentials-aux rsp-nodes
                           rsp-node-at-successor)
         (rsp-chart-ref rsp-entry-cost)))
   (and stable-under-simplificationp
        '(:use ((:instance rsp-first-node-differs-from-later-node))
                :in-theory
                (disable rsp-first-node-differs-from-later-node
                         rsp-chart-ref rsp-entry-cost)))))

(defthm rsp-potential-is-chart-cost
  (implies
   (and (symbol-listp (rsp-nodes spec))
        (no-duplicatesp-equal (rsp-nodes spec))
        (natp index)
        (< index (len spec)))
   (equal
    (vwc-potential (rsp-node-at index spec)
                   (rsp-potentials spec chart))
    (rsp-entry-cost (rsp-chart-ref index chart))))
  :hints (("Goal"
           :use ((:instance rsp-assoc-of-potentials-aux
                            (items spec)
                            (base 0)))
           :in-theory (enable rsp-potentials vwc-potential))))
