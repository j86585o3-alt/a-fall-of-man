; zml-tame-pipeline-fusion.lisp
;
; A single-pass executor for finite pipelines of APPLY$ map and filter stages,
; proved equivalent to the obvious staged semantics.

(in-package "ACL2")

(include-book "tools/def-functional-instance" :dir :system)
(include-book "xdoc/top" :dir :system)


(defxdoc zml-tame-pipeline-fusion
  :parents (acl2::top)
  :short "Verified single-pass fusion for tame APPLY$ map/filter pipelines."
  :long
  "<p>A pipeline is a finite list of <tt>(:MAP fn)</tt> and
  <tt>(:FILTER fn)</tt> stages.  Its direct semantics allocates one complete
  intermediate list per stage using local reference functions <tt>VPF-COLLECT</tt> and
  <tt>VPF-FILTER</tt>.  The fused executor instead threads each input element
  through every stage and emits at most one output, traversing the input once
  and constructing no intermediate lists.</p>

  <p>The principal theorem equates these two executable semantics for arbitrary
  pipeline data, including malformed stages and improper input tails.  A
  generic flat-map algebra is transported to the fused executor with
  @(see acl2::def-functional-instance), yielding append compositionality without
  reproving the list recursion.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Pipeline syntax
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun vpf-map-stage (fn)
  (list :map fn))

(defun vpf-filter-stage (fn)
  (list :filter fn))

(defun vpf-map-stage-p (stage)
  (and (consp stage)
       (equal (car stage) :map)
       (consp (cdr stage))
       (equal (cddr stage) nil)))

(defun vpf-filter-stage-p (stage)
  (and (consp stage)
       (equal (car stage) :filter)
       (consp (cdr stage))
       (equal (cddr stage) nil)))

(defun vpf-stage-function (stage)
  (cadr stage))

(defthm vpf-map-stage-reconstruction
  (implies (vpf-map-stage-p stage)
           (equal (vpf-map-stage (vpf-stage-function stage))
                  stage))
  :hints (("Goal" :in-theory (enable vpf-map-stage
                                      vpf-map-stage-p
                                      vpf-stage-function))))

(defthm vpf-filter-stage-reconstruction
  (implies (vpf-filter-stage-p stage)
           (equal (vpf-filter-stage (vpf-stage-function stage))
                  stage))
  :hints (("Goal" :in-theory (enable vpf-filter-stage
                                      vpf-filter-stage-p
                                      vpf-stage-function))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Single-element and fused semantics
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun vpf-run-one (stages value)
  (if (endp stages)
      (mv t value)
    (let ((stage (car stages)))
      (cond ((vpf-map-stage-p stage)
             (vpf-run-one
              (cdr stages)
              (apply$ (vpf-stage-function stage) (list value))))
            ((vpf-filter-stage-p stage)
             (if (apply$ (vpf-stage-function stage) (list value))
                 (vpf-run-one (cdr stages) value)
               (mv nil value)))
            (t
             (vpf-run-one (cdr stages) value))))))

(defun vpf-one-output (stages value)
  (mv-let (keep new-value)
    (vpf-run-one stages value)
    (if keep (list new-value) nil)))

(defun vpf-run-fused (stages input)
  (if (endp input)
      nil
    (append (vpf-one-output stages (car input))
            (vpf-run-fused stages (cdr input)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun vpf-collect (input fn)
  (if (endp input)
      nil
    (cons (apply$ fn (list (car input)))
          (vpf-collect (cdr input) fn))))

(defun vpf-filter (input fn)
  (if (endp input)
      nil
    (if (apply$ fn (list (car input)))
        (cons (car input)
              (vpf-filter (cdr input) fn))
      (vpf-filter (cdr input) fn))))

;; 3. Staged reference semantics
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun vpf-run-stage-list (stage input)
  (cond ((vpf-map-stage-p stage)
         (vpf-collect input (vpf-stage-function stage)))
        ((vpf-filter-stage-p stage)
         (vpf-filter input (vpf-stage-function stage)))
        (t
         (true-list-fix input))))

(defun vpf-run-staged (stages input)
  (if (endp stages)
      (true-list-fix input)
    (vpf-run-staged
     (cdr stages)
     (vpf-run-stage-list (car stages) input))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. One-stage fusion algebra
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm vpf-one-output-of-map-stage
  (equal (vpf-one-output
          (cons (vpf-map-stage fn) rest)
          value)
         (vpf-one-output
          rest
          (apply$ fn (list value))))
  :hints (("Goal"
           :in-theory (enable vpf-one-output
                              vpf-run-one
                              vpf-map-stage
                              vpf-map-stage-p
                              vpf-filter-stage-p
                              vpf-stage-function))))

(defthm vpf-one-output-of-filter-stage
  (equal (vpf-one-output
          (cons (vpf-filter-stage fn) rest)
          value)
         (if (apply$ fn (list value))
             (vpf-one-output rest value)
           nil))
  :hints (("Goal"
           :in-theory (enable vpf-one-output
                              vpf-run-one
                              vpf-filter-stage
                              vpf-map-stage-p
                              vpf-filter-stage-p
                              vpf-stage-function))))

(defthm vpf-run-fused-after-collect
  (equal (vpf-run-fused rest (vpf-collect input fn))
         (vpf-run-fused (cons (vpf-map-stage fn) rest) input))
  :hints (("Goal"
           :induct (vpf-collect input fn)
           :in-theory (enable vpf-collect
                              vpf-run-fused))))

(defthm vpf-run-fused-after-filter
  (equal (vpf-run-fused rest (vpf-filter input fn))
         (vpf-run-fused (cons (vpf-filter-stage fn) rest) input))
  :hints (("Goal"
           :induct (vpf-filter input fn)
           :in-theory (enable vpf-filter
                              vpf-run-fused))))

(defthm vpf-run-fused-of-true-list-fix
  (equal (vpf-run-fused stages (true-list-fix input))
         (vpf-run-fused stages input))
  :hints (("Goal"
           :induct (true-list-fix input)
           :in-theory (enable vpf-run-fused true-list-fix))))

(defthm vpf-one-output-of-malformed-stage
  (implies (and (not (vpf-map-stage-p stage))
                (not (vpf-filter-stage-p stage)))
           (equal (vpf-one-output (cons stage rest) value)
                  (vpf-one-output rest value)))
  :hints (("Goal"
           :in-theory (enable vpf-one-output vpf-run-one))))

(defthm vpf-run-fused-of-malformed-stage
  (implies (and (not (vpf-map-stage-p stage))
                (not (vpf-filter-stage-p stage)))
           (equal (vpf-run-fused (cons stage rest) input)
                  (vpf-run-fused rest input)))
  :hints (("Goal"
           :induct (vpf-run-fused rest input)
           :in-theory (enable vpf-run-fused))))

(defthm vpf-run-fused-when-endp-stages
  (implies (endp stages)
           (equal (vpf-run-fused stages input)
                  (true-list-fix input)))
  :hints (("Goal"
           :induct (vpf-run-fused stages input)
           :in-theory (enable vpf-run-fused
                              vpf-one-output
                              vpf-run-one
                              true-list-fix))))

(defthm vpf-prepend-stage-fusion
  (equal (vpf-run-fused
          rest
          (vpf-run-stage-list stage input))
         (vpf-run-fused (cons stage rest) input))
  :hints
  (("Goal"
    :cases ((vpf-map-stage-p stage)
            (vpf-filter-stage-p stage))
    :use ((:instance vpf-map-stage-reconstruction)
          (:instance vpf-filter-stage-reconstruction)
          (:instance vpf-run-fused-after-collect
                     (fn (vpf-stage-function stage)))
          (:instance vpf-run-fused-after-filter
                     (fn (vpf-stage-function stage)))
          (:instance vpf-run-fused-of-true-list-fix
                     (stages rest))
          (:instance vpf-run-fused-of-malformed-stage
                     (stage stage)
                     (rest rest)
                     (input input)))
    :in-theory
    (e/d (vpf-run-stage-list
          vpf-map-stage
          vpf-filter-stage
          vpf-map-stage-p
          vpf-filter-stage-p)
         (vpf-run-fused
          vpf-run-fused-after-collect
          vpf-run-fused-after-filter
          vpf-run-fused-of-true-list-fix
          vpf-run-fused-of-malformed-stage
          vpf-map-stage-reconstruction
          vpf-filter-stage-reconstruction)))))

(defthm vpf-fusion-correct
  (equal (vpf-run-fused stages input)
         (vpf-run-staged stages input))
  :hints
  (("Goal"
    :induct (vpf-run-staged stages input)
    :in-theory
    (e/d (vpf-run-staged)
         (vpf-run-fused
          vpf-run-stage-list
          vpf-prepend-stage-fusion)))
   ("Subgoal *1/2"
    :use ((:instance vpf-prepend-stage-fusion
                     (stage (car stages))
                     (rest (cdr stages)))
          (:instance vpf-run-fused-when-endp-stages)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Generic flat-map transport by functional instantiation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  (((vpf-emit * *) => *))
  (local (defun vpf-emit (configuration value)
           (declare (ignore configuration value))
           nil)))

(defun vpf-generic-flatmap (configuration input)
  (if (endp input)
      nil
    (append (vpf-emit configuration (car input))
            (vpf-generic-flatmap configuration (cdr input)))))

(defthm vpf-generic-flatmap-of-append
  (equal (vpf-generic-flatmap configuration (append left right))
         (append (vpf-generic-flatmap configuration left)
                 (vpf-generic-flatmap configuration right)))
  :hints (("Goal"
           :induct (append left right)
           :in-theory (enable vpf-generic-flatmap))))

(in-theory (disable vpf-fusion-correct))

(acl2::def-functional-instance
  vpf-run-fused-of-append
  vpf-generic-flatmap-of-append
  ((vpf-emit vpf-one-output)
   (vpf-generic-flatmap vpf-run-fused))
  :hints (("Subgoal 1"
           :in-theory (enable vpf-run-fused))))

(in-theory (enable vpf-fusion-correct))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 6. Ground witness
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (and (equal (vpf-run-fused nil '(a b c)) '(a b c))
      (equal (vpf-run-staged nil '(a b c)) '(a b c))
      (equal (vpf-run-fused '(malformed-stage) '(a b c))
             '(a b c))))

(defxdoc vpf-user-interface
  :parents (zml-tame-pipeline-fusion)
  :short "Public interface for single-pass tame pipelines."
  :long
  "<p>Construct stages with <tt>VPF-MAP-STAGE</tt> and
  <tt>VPF-FILTER-STAGE</tt>.  <tt>VPF-RUN-STAGED</tt> is the allocating
  reference semantics; <tt>VPF-RUN-FUSED</tt> is the single-pass executor.
  Their equality is <tt>VPF-FUSION-CORRECT</tt>.  The functionally transported
  theorem <tt>VPF-RUN-FUSED-OF-APPEND</tt> gives input chunk compositionality.</p>")
