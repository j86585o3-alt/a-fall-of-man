; zkx-weighted-path-certificates.lisp
; Composable weighted path certificates and model-theoretic bound soundness.

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/omaps/update" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc zkx-weighted-path-certificates
  :parents (acl2::top)
  :short "Composable weighted paths whose bounds hold in every feasible potential."
  :long "<p>An edge carries symbolic endpoints and a natural weight.  A path
  certificate is checked for graph membership and endpoint continuity.  Any
  ordered-map potential satisfying every graph edge inequality must satisfy
  the accumulated inequality induced by every accepted path certificate.
  Certificates compose by append, with exact endpoint and cost laws.</p>")

(fty::defprod vwc-edge
  ((from symbol)
   (to symbol)
   (weight nat))
  :tag :vwc-edge
  :layout :tree)

(fty::deflist vwc-path
  :elt-type vwc-edge
  :true-listp t)

(defun vwc-potential (node potentials)
  (let ((look (omap::assoc (symbol-fix node) potentials)))
    (if look (ifix (cdr look)) 0)))

(defun vwc-path-cost (path)
  (if (endp path) 0
    (+ (vwc-edge->weight (car path))
       (vwc-path-cost (cdr path)))))

(defun vwc-path-chains-p (path start finish)
  (if (endp path)
      (equal (symbol-fix start) (symbol-fix finish))
    (and (equal (vwc-edge->from (car path)) (symbol-fix start))
         (vwc-path-chains-p (cdr path)
                            (vwc-edge->to (car path))
                            finish))))

(defun vwc-path-in-graph-p (path graph)
  (if (endp path) t
    (and (member-equal (vwc-edge-fix (car path)) graph)
         (vwc-path-in-graph-p (cdr path) graph))))

(defun vwc-certificate-p (path graph start finish)
  (and (vwc-path-p path)
       (vwc-path-in-graph-p path graph)
       (vwc-path-chains-p path start finish)))

(defun vwc-edge-model-p (edge potentials)
  (<= (vwc-potential (vwc-edge->to edge) potentials)
      (+ (vwc-potential (vwc-edge->from edge) potentials)
         (vwc-edge->weight edge))))

(defun vwc-graph-model-p (graph potentials)
  (if (endp graph) t
    (and (vwc-edge-model-p (car graph) potentials)
         (vwc-graph-model-p (cdr graph) potentials))))

(defun vwc-path-model-p (path potentials)
  (if (endp path) t
    (and (vwc-edge-model-p (vwc-edge-fix (car path)) potentials)
         (vwc-path-model-p (cdr path) potentials))))

(defthm vwc-path-cost-of-append
  (equal (vwc-path-cost (append left right))
         (+ (vwc-path-cost left) (vwc-path-cost right)))
  :hints (("Goal" :induct (vwc-path-cost left) :in-theory (enable vwc-path-cost))))

(defthm vwc-path-in-graph-p-of-append
  (equal (vwc-path-in-graph-p (append left right) graph)
         (and (vwc-path-in-graph-p left graph)
              (vwc-path-in-graph-p right graph)))
  :hints (("Goal" :induct (vwc-path-in-graph-p left graph) :in-theory (enable vwc-path-in-graph-p))))

(defthm vwc-path-chains-p-of-append
  (implies (vwc-path-chains-p left start middle)
           (equal (vwc-path-chains-p (append left right) start finish)
                  (vwc-path-chains-p right middle finish)))
  :hints (("Goal" :induct (vwc-path-chains-p left start middle) :in-theory (enable vwc-path-chains-p))))

(defthm vwc-certificate-compose
  (implies (and (vwc-certificate-p left graph start middle)
                (vwc-certificate-p right graph middle finish))
           (vwc-certificate-p (append left right) graph start finish))
  :hints (("Goal" :in-theory (enable vwc-certificate-p))))

(defthm vwc-member-edge-in-graph-model
  (implies (and (vwc-graph-model-p graph potentials)
                (member-equal edge graph))
           (vwc-edge-model-p edge potentials))
  :hints (("Goal" :induct (vwc-graph-model-p graph potentials) :in-theory (enable vwc-graph-model-p))))

(defthm vwc-certificate-implies-path-model
  (implies (and (vwc-path-in-graph-p path graph)
                (vwc-graph-model-p graph potentials))
           (vwc-path-model-p path potentials))
  :hints (("Goal"
           :induct (vwc-path-in-graph-p path graph)
           :in-theory (enable vwc-path-in-graph-p vwc-path-model-p))
          ("Subgoal *1/2"
           :use ((:instance vwc-member-edge-in-graph-model
                            (edge (vwc-edge-fix (car path)))))
           :in-theory (disable vwc-member-edge-in-graph-model))))

(defthm vwc-path-model-bound
  (implies (and (vwc-path-p path)
                (vwc-path-chains-p path start finish)
                (vwc-path-model-p path potentials))
           (<= (vwc-potential finish potentials)
               (+ (vwc-potential start potentials)
                  (vwc-path-cost path))))
  :hints (("Goal" :induct (vwc-path-chains-p path start finish)
           :in-theory (enable vwc-path-chains-p vwc-path-model-p
                              vwc-path-cost))))

(defthm vwc-certificate-sound
  (implies (and (vwc-certificate-p path graph start finish)
                (vwc-graph-model-p graph potentials))
           (<= (vwc-potential finish potentials)
               (+ (vwc-potential start potentials)
                  (vwc-path-cost path))))
  :hints (("Goal"
           :use ((:instance vwc-certificate-implies-path-model)
                 (:instance vwc-path-model-bound))
           :in-theory (enable vwc-certificate-p))))

(defconst *vwc-graph*
  (list (vwc-edge 'a 'b 3)
        (vwc-edge 'b 'c 4)
        (vwc-edge 'a 'c 10)))
(defconst *vwc-path*
  (list (vwc-edge 'a 'b 3)
        (vwc-edge 'b 'c 4)))

(assert-event
 (and (vwc-certificate-p *vwc-path* *vwc-graph* 'a 'c)
      (equal (vwc-path-cost *vwc-path*) 7)))

(defxdoc vwc-user-interface
  :parents (zkx-weighted-path-certificates)
  :short "Public interface for weighted path proof objects."
  :long "<p>Use <tt>VWC-CERTIFICATE-P</tt> to check paths,
  <tt>VWC-CERTIFICATE-COMPOSE</tt> to concatenate them, and
  <tt>VWC-CERTIFICATE-SOUND</tt> to transport graph edge inequalities across
  an accepted path.</p>")
