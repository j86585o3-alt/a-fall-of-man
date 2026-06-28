; zad-adp-shortest-path.lisp
;
; A compact shortest-path client of the min-plus provenance compiler.

(in-package "ACL2")

(include-book "zac-adp-min-plus-provenance")

; Nodes and edges are the entire algorithm description.  The compiler derives
; the radix, packed rule weights, predecessor indices, dynamic program,
; witness path, and distance potential.
(defconst *mwp-nodes* '(a c b d e))

(defconst *mwp-edge-table*
  (list
   (cons 0 (vwc-edge 'a 'c 1))
   (cons 1 (vwc-edge 'a 'b 3))
   (cons 2 (vwc-edge 'c 'b 1))
   (cons 3 (vwc-edge 'b 'd 2))
   (cons 4 (vwc-edge 'c 'd 5))
   (cons 5 (vwc-edge 'd 'e 1))
   (cons 6 (vwc-edge 'b 'e 6))))

(defconst *mwp-base*
  (mwp-base-for-table *mwp-edge-table*))

(defconst *mwp-program*
  (mwp-compile-program *mwp-nodes* 'a *mwp-edge-table*))

(defconst *mwp-graph*
  (mwp-table-graph *mwp-edge-table*))

(defconst *mwp-answer*
  (mwp-solve 4 *mwp-program* *mwp-base*
             *mwp-edge-table* *mwp-nodes*))

(defconst *mwp-potentials*
  (mwp-solution-potentials *mwp-answer*))

(defthm mwp-example-program-valid
  (mwp-program-validp *mwp-program*))

(defthm mwp-example-packed-answer
  (equal (mwp-fast-value 4 *mwp-program*) 685))

(defthm mwp-example-fast-value-is-denotation
  (equal (mwp-fast-value 4 *mwp-program*)
         (mwp-denote-item 4 *mwp-program*))
  :hints (("Goal"
           :use ((:instance mwp-fast-value-correct
                            (program *mwp-program*)
                            (index 4))))))

(defthm mwp-example-answer-cost
  (equal (mwp-solution-cost *mwp-answer*) 5))

(defthm mwp-example-answer-code
  (equal (mwp-solution-code *mwp-answer*) 45))

(defthm mwp-example-answer-path
  (equal (mwp-solution-path *mwp-answer*)
         (list (vwc-edge 'a 'c 1)
               (vwc-edge 'c 'b 1)
               (vwc-edge 'b 'd 2)
               (vwc-edge 'd 'e 1))))

(defthm mwp-example-answer-certificate
  (mwp-optimal-certificate-p
   (mwp-solution-path *mwp-answer*)
   *mwp-graph* 'a 'e *mwp-potentials*))

(defthm mwp-example-answer-cost-matches-path
  (equal (mwp-solution-cost *mwp-answer*)
         (vwc-path-cost (mwp-solution-path *mwp-answer*))))

(defthm mwp-example-answer-is-globally-optimal
  (implies (vwc-certificate-p competitor *mwp-graph* 'a 'e)
           (<= (mwp-solution-cost *mwp-answer*)
               (vwc-path-cost competitor)))
  :hints (("Goal"
           :use ((:instance mwp-checked-solution-is-globally-optimal
                            (solution *mwp-answer*)
                            (graph *mwp-graph*)
                            (source 'a)
                            (target 'e)
                            (potentials *mwp-potentials*))))))
