; zai-ranked-shortest-path-interface.lisp
;
; Minimal client interface for the certified ranked shortest-path compiler.

(in-package "ACL2")

(include-book "zah-ranked-shortest-path-executable")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 13. Valid specifications already contain a proper symbol node list
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rsp-symbol-listp-of-nodes-tail
  (implies
   (and (natp index)
        (rsp-prefix-validp (len spec) spec))
   (symbol-listp (rsp-nodes (nthcdr index spec))))
  :hints
  (("Goal"
    :induct (rsp-index-to-end-induct index spec)
    :in-theory
    (e/d (rsp-index-to-end-induct rsp-nodes rsp-item-validp)
         (rsp-prefix-validp)))
   (and stable-under-simplificationp
        '(:use
          ((:instance rsp-item-validp-from-prefix
                      (n (len spec)))
           (:instance rsp-cdr-of-nthcdr-tail
                      (items (nthcdr index spec))))
          :in-theory
          (disable rsp-item-validp-from-prefix
                   rsp-cdr-of-nthcdr-tail
                   rsp-prefix-validp)))))

(defthm rsp-spec-validp-implies-symbol-listp-nodes
  (implies (rsp-spec-validp spec)
           (symbol-listp (rsp-nodes spec)))
  :hints
  (("Goal"
    :use ((:instance rsp-symbol-listp-of-nodes-tail
                     (index 0)))
    :in-theory
    (e/d (rsp-spec-validp)
         (rsp-symbol-listp-of-nodes-tail)))))

(defthm rsp-spec-validp-implies-consp
  (implies (rsp-spec-validp spec)
           (consp spec))
  :hints (("Goal" :in-theory (enable rsp-spec-validp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 14. Final-target solver: graph declaration in, certified optimum out
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rsp-final-index (spec)
  (if (consp spec)
      (1- (len spec))
    0))

(defun rsp-solve-final (spec)
  (rsp-solve (rsp-final-index spec) spec))

(defthm rsp-final-index-in-range
  (implies (consp spec)
           (and (natp (rsp-final-index spec))
                (< (rsp-final-index spec) (len spec))))
  :hints (("Goal" :in-theory (enable rsp-final-index))))

(defthm rsp-solve-final-emits-optimal-certificate
  (implies
   (rsp-spec-validp spec)
   (mwp-optimal-certificate-p
    (rsp-solution-path (rsp-solve-final spec))
    (rsp-graph spec)
    (rsp-node-at 0 spec)
    (rsp-node-at (rsp-final-index spec) spec)
    (rsp-solution-potentials (rsp-solve-final spec))))
  :hints
  (("Goal"
    :expand ((rsp-solve-final spec))
    :use
    ((:instance rsp-spec-validp-implies-consp)
     (:instance rsp-spec-validp-implies-symbol-listp-nodes)
     (:instance rsp-final-index-in-range)
     (:instance rsp-solve-emits-optimal-certificate
                (target (rsp-final-index spec))))
    :in-theory nil)))

(defthm rsp-solve-final-answer-is-globally-optimal
  (implies
   (and
    (rsp-spec-validp spec)
    (vwc-certificate-p
     competitor
     (rsp-graph spec)
     (rsp-node-at 0 spec)
     (rsp-node-at (rsp-final-index spec) spec)))
   (<= (rsp-solution-cost (rsp-solve-final spec))
       (vwc-path-cost competitor)))
  :hints
  (("Goal"
    :expand ((rsp-solve-final spec))
    :use
    ((:instance rsp-spec-validp-implies-consp)
     (:instance rsp-spec-validp-implies-symbol-listp-nodes)
     (:instance rsp-final-index-in-range)
     (:instance rsp-solve-answer-is-globally-optimal
                (target (rsp-final-index spec))))
    :in-theory nil)))
