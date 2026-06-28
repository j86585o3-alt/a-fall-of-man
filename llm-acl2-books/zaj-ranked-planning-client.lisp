; zaj-ranked-planning-client.lisp
;
; A compact client: minimum-cost staged planning from a ranked declaration.

(in-package "ACL2")

(include-book "zai-ranked-shortest-path-interface")

(defconst *deployment-plan*
  '((idea)
    (prototype       (0 5))
    (formal-model    (0 2))
    (verified-core   (2 4) (1 3))
    (optimized-core  (3 2) (2 8))
    (release         (4 1) (3 5))))

(defconst *deployment-answer*
  (rsp-solve-final *deployment-plan*))

(defthm deployment-plan-valid
  (rsp-spec-validp *deployment-plan*)
  :hints (("Goal"
           :in-theory
           (enable rsp-spec-validp rsp-prefix-validp rsp-item-validp
                   rsp-arcs-validp rsp-arc-validp rsp-nodes
                   rsp-arc-pred rsp-arc-weight))))

(assert-event
 (equal (rsp-solution-cost *deployment-answer*) 9))

(assert-event
 (equal
  (rsp-solution-path *deployment-answer*)
  (list (vwc-edge 'idea 'formal-model 2)
        (vwc-edge 'formal-model 'verified-core 4)
        (vwc-edge 'verified-core 'optimized-core 2)
        (vwc-edge 'optimized-core 'release 1))))

(defthm deployment-answer-is-globally-optimal
  (implies
   (vwc-certificate-p
    competitor
    (rsp-graph *deployment-plan*)
    'idea 'release)
   (<= (rsp-solution-cost *deployment-answer*)
       (vwc-path-cost competitor)))
  :hints
  (("Goal"
    :use
    ((:instance rsp-solve-final-answer-is-globally-optimal
                (spec *deployment-plan*)))
    :in-theory
    (e/d (rsp-final-index rsp-node-at)
         (rsp-solve-final-answer-is-globally-optimal)))))
