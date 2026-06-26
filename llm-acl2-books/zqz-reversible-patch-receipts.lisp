; zqz-reversible-patch-receipts.lisp
;
; Source-indexed inverse patches and total transactional receipts.

(in-package "ACL2")

(include-book "zsh-verified-patch-composition")

(defxdoc zqz-reversible-patch-receipts
  :parents (zpc-user-interface)
  :short "Certified source-indexed rollback patches and transactional receipts."
  :long
  "<p>A patch need not be injective: DROP destroys source symbols.  This book
  restores reversibility by compiling, from a patch and its concrete source,
  an ordinary canonical patch that undoes the successful edit.  KEEP remains
  KEEP, DROP becomes an RLE-compressed INSERT carrying the removed prefix, and
  INSERT becomes DROP of the decoded insertion length.</p>

  <p>A receipt packages the committed word and inverse patch.  Rejected edits
  carry the original word and an empty inverse, so rollback is a total
  operation.  The principal theorems prove success of the generated inverse,
  exact restoration, and unconditional receipt rollback.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Inverse compiler
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zrr-inverse-raw (patch source)
  (if (endp patch)
      nil
    (let ((instruction (car patch)))
      (cond
       ((zyp-keep-p instruction)
        (cons (zyp-keep (zyp-count instruction))
              (zrr-inverse-raw
               (cdr patch)
               (zyp-drop-prefix (zyp-count instruction) source))))
       ((zyp-drop-p instruction)
        (cons (zyp-insert
               (xef-rle-encode
                (zyp-take (zyp-count instruction) source)))
              (zrr-inverse-raw
               (cdr patch)
               (zyp-drop-prefix (zyp-count instruction) source))))
       ((zyp-insert-p instruction)
        (cons (zyp-drop
               (xef-rle-symbol-count
                (zyp-insert-runs instruction)))
              (zrr-inverse-raw (cdr patch) source)))
       (t
        (zrr-inverse-raw (cdr patch) source))))))

(defun zrr-inverse (patch source)
  (zyp-normalize (zrr-inverse-raw patch source)))

(defthm zrr-inverse-is-canonical
  (zyp-canonical-p (zrr-inverse patch source))
  :hints
  (("Goal"
    :in-theory (enable zrr-inverse))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Total-list and one-step algebra
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm zrr-patch-transform-open
  (implies (consp patch)
           (equal (zpc-patch-transform patch source)
                  (append
                   (zyp-step-output (car patch) source)
                   (zpc-patch-transform
                    (cdr patch)
                    (zyp-step-rest (car patch) source)))))
  :hints
  (("Goal"
    :in-theory
    (enable zpc-patch-transform
            zyp-patch-output
            zyp-patch-rest))))

(defthm zrr-drop-prefix-length-of-append
  (equal (zyp-drop-prefix (len prefix)
                          (append prefix suffix))
         suffix)
  :hints
  (("Goal"
    :use ((:instance zrs-drop-prefix-of-append
                     (n (len prefix))
                     (xs prefix)
                     (ys suffix)))
    :in-theory (disable zrs-drop-prefix-of-append))))

(defthm zrr-take-length-of-append
  (equal (zyp-take (len prefix)
                   (append prefix suffix))
         (true-list-fix prefix))
  :hints
  (("Goal"
    :use ((:instance zrs-take-of-append
                     (n (len prefix))
                     (xs prefix)
                     (ys suffix)))
    :in-theory (disable zrs-take-of-append))))

(defthm zrr-enoughp-length-of-append
  (zyp-enoughp (len prefix) (append prefix suffix))
  :hints
  (("Goal"
    :in-theory (enable zrs-enoughp-iff-count-at-most-len))))

(defthm zrr-decode-encode-take
  (equal (xef-rle-decode
          (xef-rle-encode (zyp-take n source)))
         (zyp-take n source))
  :hints
  (("Goal"
    :use ((:instance xef-rle-decode-of-encode
                     (word (zyp-take n source)))))))

(defthm zrr-patch-transform-of-nil
  (equal (zpc-patch-transform nil source)
         (true-list-fix source))
  :hints
  (("Goal"
    :in-theory
    (enable zpc-patch-transform
            zyp-patch-output
            zyp-patch-rest))))

(defthm zrr-transform-of-keep-prefix
  (equal
   (zpc-patch-transform
    (cons (zyp-keep (len prefix)) inverse)
    (append prefix tail))
   (append (true-list-fix prefix)
           (zpc-patch-transform inverse tail)))
  :hints
  (("Goal"
    :use ((:instance zrr-take-length-of-append)
          (:instance zrr-drop-prefix-length-of-append))
    :in-theory
    (e/d (zrr-patch-transform-open
          zyp-step-output
          zyp-step-rest)
         (zrr-take-length-of-append
          zrr-drop-prefix-length-of-append)))))

(defthm zrr-transform-of-insert-prefix
  (equal
   (zpc-patch-transform
    (cons (zyp-insert (xef-rle-encode prefix)) inverse)
    tail)
   (append (true-list-fix prefix)
           (zpc-patch-transform inverse tail)))
  :hints
  (("Goal"
    :use ((:instance xef-rle-decode-of-encode
                     (word prefix)))
    :in-theory
    (e/d (zrr-patch-transform-open
          zyp-step-output
          zyp-step-rest)
         ()))))

(defthm zrr-transform-of-drop-prefix
  (equal
   (zpc-patch-transform
    (cons (zyp-drop (len prefix)) inverse)
    (append prefix tail))
   (zpc-patch-transform inverse tail))
  :hints
  (("Goal"
    :use ((:instance zrr-drop-prefix-length-of-append))
    :in-theory
    (e/d (zrr-patch-transform-open
          zyp-step-output
          zyp-step-rest)
         (zrr-drop-prefix-length-of-append)))))

(defthm zrr-take-consumption-prefix
  (equal (append (zyp-take n source)
                 (zyp-take m (zyp-drop-prefix n source)))
         (zyp-take (+ (nfix m) (nfix n)) source))
  :hints
  (("Goal"
    :use ((:instance zyp-take-of-sum
                     (m n)
                     (n m)
                     (xs source)))
    :in-theory (disable zyp-take-of-sum))))

(defthm zrr-take-consumption-prefix-with-tail
  (equal (append (zyp-take n source)
                 (zyp-take m (zyp-drop-prefix n source))
                 (true-list-fix tail))
         (append (zyp-take (+ (nfix m) (nfix n)) source)
                 (true-list-fix tail)))
  :hints
  (("Goal"
    :use ((:instance zrr-take-consumption-prefix))
    :in-theory (disable zrr-take-consumption-prefix))))

(defthm zrr-patch-rest-is-drop-source-demand
  (equal (zyp-patch-rest patch source)
         (true-list-fix
          (zyp-drop-prefix (zyp-source-demand patch) source)))
  :hints
  (("Goal"
    :induct (zyp-patch-rest patch source)
    :in-theory
    (enable zyp-patch-rest
            zyp-source-demand
            zyp-step-rest))))

(defthm zrr-patch-output-when-static-length-zero
  (implies (and (equal (zyp-kept-length patch) 0)
                (equal (zyp-inserted-length patch) 0))
           (equal (zyp-patch-output patch source) nil))
  :hints
  (("Goal"
    :induct (zyp-patch-output patch source)
    :in-theory
    (enable zyp-patch-output
            zyp-kept-length
            zyp-inserted-length
            zyp-step-output
            zyp-step-rest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Rollback correctness
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zrr-inverse-induction (patch source tail)
  (if (endp patch)
      (list source tail)
    (let ((instruction (car patch)))
      (cond
       ((or (zyp-keep-p instruction)
            (zyp-drop-p instruction))
        (zrr-inverse-induction
         (cdr patch)
         (zyp-drop-prefix (zyp-count instruction) source)
         tail))
       (t
        (zrr-inverse-induction (cdr patch) source tail))))))

(defthm zrr-source-demand-of-inverse-raw
  (equal (zyp-source-demand (zrr-inverse-raw patch source))
         (zyp-output-length patch))
  :hints
  (("Goal"
    :induct (zrr-inverse-raw patch source)
    :in-theory
    (enable zrr-inverse-raw
            zyp-source-demand
            zyp-output-length
            zyp-kept-length
            zyp-inserted-length))))

(defthm zrr-output-length-at-most-transform-length
  (implies (zyp-patch-okp patch source)
           (<= (zyp-output-length patch)
               (len (zpc-patch-transform patch source))))
  :hints
  (("Goal"
    :use ((:instance zyp-len-of-patch-output-when-okp))
    :in-theory
    (enable zpc-patch-transform))))

(defthm zrr-raw-inverse-succeeds
  (implies (zyp-patch-okp patch source)
           (zyp-patch-okp
            (zrr-inverse-raw patch source)
            (zpc-patch-transform patch source)))
  :hints
  (("Goal"
    :use ((:instance zrr-output-length-at-most-transform-length))
    :in-theory
    (e/d (zsp-patch-okp-is-source-demand
          zrs-enoughp-iff-count-at-most-len)
         (zrr-output-length-at-most-transform-length)))))

(defun zrr-consumed-prefix (patch source)
  (if (endp patch)
      nil
    (let ((instruction (car patch)))
      (cond
       ((or (zyp-keep-p instruction)
            (zyp-drop-p instruction))
        (append
         (zyp-take (zyp-count instruction) source)
         (zrr-consumed-prefix
          (cdr patch)
          (zyp-drop-prefix (zyp-count instruction) source))))
       (t
        (zrr-consumed-prefix (cdr patch) source))))))

(defthm zrr-consumed-prefix-is-take-demand
  (implies (zyp-patch-okp patch source)
           (equal (zrr-consumed-prefix patch source)
                  (zyp-take (zyp-source-demand patch) source)))
  :hints
  (("Goal"
    :induct (zrr-inverse-induction patch source nil)
    :in-theory
    (enable zrr-inverse-induction
            zrr-consumed-prefix
            zyp-patch-okp
            zyp-source-demand
            zyp-step-okp
            zyp-step-rest
            zrr-take-consumption-prefix))))

(defun zrr-inverse-transform-property (patch source tail)
  (equal
   (zpc-patch-transform
    (zrr-inverse-raw patch source)
    (append (zyp-patch-output patch source) tail))
   (append (zrr-consumed-prefix patch source)
           (true-list-fix tail))))

(defthm zrr-inverse-transform-property-when-endp
  (implies (endp patch)
           (zrr-inverse-transform-property patch source tail))
  :hints
  (("Goal"
    :in-theory
    (enable zrr-inverse-transform-property
            zrr-inverse-raw
            zrr-consumed-prefix
            zyp-patch-output
            zpc-patch-transform
            zyp-patch-rest))))

(defthm zrr-inverse-transform-property-step-keep
  (implies
   (and (zyp-keep-p instruction)
        (zyp-step-okp instruction source)
        (zrr-inverse-transform-property
         rest (zyp-step-rest instruction source) tail))
   (zrr-inverse-transform-property
    (cons instruction rest) source tail))
  :hints
  (("Goal"
    :use
    ((:instance zrr-transform-of-keep-prefix
                (prefix (zyp-take (zyp-count instruction) source))
                (inverse
                 (zrr-inverse-raw
                  rest (zyp-step-rest instruction source)))
                (tail
                 (append
                  (zyp-patch-output
                   rest (zyp-step-rest instruction source))
                  tail))))
    :in-theory
    (e/d (zrr-inverse-transform-property
          zrr-inverse-raw
          zrr-consumed-prefix
          zyp-patch-output
          zyp-step-output
          zyp-step-rest
          zyp-step-okp)
         (zpc-patch-transform
          zrr-transform-of-keep-prefix)))))

(defthm zrr-inverse-transform-property-step-drop
  (implies
   (and (zyp-drop-p instruction)
        (zyp-step-okp instruction source)
        (zrr-inverse-transform-property
         rest (zyp-step-rest instruction source) tail))
   (zrr-inverse-transform-property
    (cons instruction rest) source tail))
  :hints
  (("Goal"
    :use
    ((:instance zrr-transform-of-insert-prefix
                (prefix (zyp-take (zyp-count instruction) source))
                (inverse
                 (zrr-inverse-raw
                  rest (zyp-step-rest instruction source)))
                (tail
                 (append
                  (zyp-patch-output
                   rest (zyp-step-rest instruction source))
                  tail))))
    :in-theory
    (e/d (zrr-inverse-transform-property
          zrr-inverse-raw
          zrr-consumed-prefix
          zyp-patch-output
          zyp-step-output
          zyp-step-rest
          zyp-step-okp)
         (zpc-patch-transform
          zrr-transform-of-insert-prefix)))))

(defthm zrr-inverse-transform-property-step-insert
  (implies
   (and (zyp-insert-p instruction)
        (zrr-inverse-transform-property rest source tail))
   (zrr-inverse-transform-property
    (cons instruction rest) source tail))
  :hints
  (("Goal"
    :use
    ((:instance zrr-transform-of-drop-prefix
                (prefix
                 (xef-rle-decode (zyp-insert-runs instruction)))
                (inverse (zrr-inverse-raw rest source))
                (tail (append (zyp-patch-output rest source) tail))))
    :in-theory
    (e/d (zrr-inverse-transform-property
          zrr-inverse-raw
          zrr-consumed-prefix
          zyp-patch-output
          zyp-step-output
          zyp-step-rest)
         (zpc-patch-transform
          zrr-transform-of-drop-prefix)))))

(defthm zrr-inverse-transform-property-step-malformed
  (implies
   (and (not (zyp-keep-p instruction))
        (not (zyp-drop-p instruction))
        (not (zyp-insert-p instruction))
        (zrr-inverse-transform-property rest source tail))
   (zrr-inverse-transform-property
    (cons instruction rest) source tail))
  :hints
  (("Goal"
    :in-theory
    (enable zrr-inverse-transform-property
            zrr-inverse-raw
            zrr-consumed-prefix
            zyp-patch-output
            zyp-step-output
            zyp-step-rest))))

(defthm zrr-inverse-transform-property-when-okp
  (implies (zyp-patch-okp patch source)
           (zrr-inverse-transform-property patch source tail))
  :hints
  (("Goal"
    :induct (zrr-inverse-induction patch source tail)
    :in-theory
    (e/d (zrr-inverse-induction
          zyp-patch-okp)
         (zrr-inverse-transform-property)))
   ("Subgoal *1/3.4"
    :cases ((zyp-insert-p (car patch)))
    :use ((:instance zrr-inverse-transform-property-step-insert
                     (instruction (car patch))
                     (rest (cdr patch)))
          (:instance zrr-inverse-transform-property-step-malformed
                     (instruction (car patch))
                     (rest (cdr patch)))))
   ("Subgoal *1/1''"
    :use ((:instance zrr-inverse-transform-property-when-endp)))))

(defthm zrr-raw-inverse-transform-consumed-prefix
  (implies (zyp-patch-okp patch source)
           (equal
            (zpc-patch-transform
             (zrr-inverse-raw patch source)
             (append (zyp-patch-output patch source) tail))
            (append (zrr-consumed-prefix patch source)
                    (true-list-fix tail))))
  :hints
  (("Goal"
    :use ((:instance zrr-inverse-transform-property-when-okp))
    :in-theory
    (e/d (zrr-inverse-transform-property)
         (zrr-inverse-transform-property-when-okp)))))

(defthm zrr-raw-inverse-transform-with-tail
  (implies (zyp-patch-okp patch source)
           (equal
            (zpc-patch-transform
             (zrr-inverse-raw patch source)
             (append (zyp-patch-output patch source) tail))
            (append
             (zyp-take (zyp-source-demand patch) source)
             (true-list-fix tail))))
  :hints
  (("Goal"
    :use ((:instance zrr-raw-inverse-transform-consumed-prefix)
          (:instance zrr-consumed-prefix-is-take-demand))
    :in-theory
    (disable zrr-raw-inverse-transform-consumed-prefix
             zrr-consumed-prefix-is-take-demand))))

(defthm zrr-raw-inverse-restores
  (implies (zyp-patch-okp patch source)
           (equal
            (zpc-patch-transform
             (zrr-inverse-raw patch source)
             (zpc-patch-transform patch source))
            (true-list-fix source)))
  :hints
  (("Goal"
    :use ((:instance zrr-raw-inverse-transform-with-tail
                     (tail (zyp-patch-rest patch source)))
          (:instance zyp-append-take-and-drop
                     (n (zyp-source-demand patch))
                     (xs source)))
    :in-theory
    (e/d (zpc-patch-transform)
         (zrr-raw-inverse-transform-with-tail
          zyp-append-take-and-drop)))))

(defthm zrr-patch-transform-of-normalize
  (equal (zpc-patch-transform (zyp-normalize patch) source)
         (zpc-patch-transform patch source))
  :hints
  (("Goal"
    :use ((:instance zyp-patch-output-of-normalize)
          (:instance zyp-patch-rest-of-normalize))
    :in-theory
    (e/d (zpc-patch-transform)
         (zrr-patch-rest-is-drop-source-demand
          zyp-patch-output-of-normalize
          zyp-patch-rest-of-normalize)))))

(defthm zrr-inverse-succeeds
  (implies (zyp-patch-okp patch source)
           (zyp-patch-okp
            (zrr-inverse patch source)
            (zpc-patch-transform patch source)))
  :hints
  (("Goal"
    :use ((:instance zrr-raw-inverse-succeeds)
          (:instance zyp-patch-okp-of-normalize
                     (patch (zrr-inverse-raw patch source))
                     (source (zpc-patch-transform patch source))))
    :in-theory
    (e/d (zrr-inverse)
         (zrr-raw-inverse-succeeds
          zyp-patch-okp-of-normalize)))))

(defthm zrr-inverse-restores
  (implies (zyp-patch-okp patch source)
           (equal
            (zpc-patch-transform
             (zrr-inverse patch source)
             (zpc-patch-transform patch source))
            (true-list-fix source)))
  :hints
  (("Goal"
    :use ((:instance zrr-raw-inverse-restores))
    :in-theory
    (e/d (zrr-inverse)
         (zrr-raw-inverse-restores
          zpc-patch-transform)))))

(defthm zrr-patch-word-when-okp
  (implies (zyp-patch-okp patch source)
           (equal (zvr-patch-word patch source)
                  (zpc-patch-transform patch source)))
  :hints
  (("Goal"
    :expand ((zvr-patch-word patch source)
             (zpc-patch-transform patch source))
    :in-theory
    (disable zsp-patch-okp-is-source-demand))))

(defthm zrr-transactional-rollback
  (implies (zyp-patch-okp patch source)
           (equal
            (zvr-patch-word
             (zrr-inverse patch source)
             (zvr-patch-word patch source))
            (true-list-fix source)))
  :hints
  (("Goal"
    :use ((:instance zrr-inverse-succeeds)
          (:instance zrr-inverse-restores))
    :in-theory
    (e/d (zrr-patch-word-when-okp)
         (zvr-patch-word
          zpc-patch-transform
          zrr-inverse-succeeds
          zrr-inverse-restores)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Receipts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zrr-receipt (patch source)
  (if (zyp-patch-okp patch source)
      (list :committed
            (zpc-patch-transform patch source)
            (zrr-inverse patch source))
    (list :rejected
          (true-list-fix source)
          nil)))

(defun zrr-receipt-committed-p (receipt)
  (equal (car receipt) :committed))

(defun zrr-receipt-word (receipt)
  (true-list-fix (cadr receipt)))

(defun zrr-receipt-inverse (receipt)
  (caddr receipt))

(defun zrr-rollback-receipt (receipt)
  (zvr-patch-word
   (zrr-receipt-inverse receipt)
   (zrr-receipt-word receipt)))

(defthm zrr-receipt-committed-p-correct
  (equal (zrr-receipt-committed-p (zrr-receipt patch source))
         (if (zyp-patch-okp patch source) t nil))
  :hints
  (("Goal"
    :in-theory
    (enable zrr-receipt
            zrr-receipt-committed-p))))

(defthm zrr-receipt-word-is-transactional-result
  (equal (zrr-receipt-word (zrr-receipt patch source))
         (zvr-patch-word patch source))
  :hints
  (("Goal"
    :in-theory
    (enable zrr-receipt
            zrr-receipt-word
            zvr-patch-word))))

(defthm zrr-patch-word-of-nil
  (equal (zvr-patch-word nil source)
         (true-list-fix source))
  :hints
  (("Goal"
    :in-theory
    (enable zvr-patch-word
            zyp-patch-okp
            zyp-patch-output
            zyp-patch-rest))))

(defthm zrr-receipt-rollback-when-committed
  (implies (zyp-patch-okp patch source)
           (equal (zrr-rollback-receipt
                   (zrr-receipt patch source))
                  (true-list-fix source)))
  :hints
  (("Goal"
    :use ((:instance zrr-transactional-rollback)
          (:instance zrr-receipt-word-is-transactional-result))
    :in-theory
    (e/d (zrr-receipt
          zrr-receipt-inverse
          zrr-rollback-receipt)
         (zvr-patch-word
          zpc-patch-transform
          zrr-transactional-rollback
          zrr-receipt-word-is-transactional-result)))))

(defthm zrr-receipt-rollback-when-rejected
  (implies (not (zyp-patch-okp patch source))
           (equal (zrr-rollback-receipt
                   (zrr-receipt patch source))
                  (true-list-fix source)))
  :hints
  (("Goal"
    :use ((:instance zrr-patch-word-of-nil
                     (source (true-list-fix source))))
    :in-theory
    (e/d (zrr-receipt
          zrr-receipt-word
          zrr-receipt-inverse
          zrr-rollback-receipt)
         (zvr-patch-word
          zrr-patch-word-of-nil)))))

(defthm zrr-receipt-rollback-correct
  (equal (zrr-rollback-receipt (zrr-receipt patch source))
         (true-list-fix source))
  :hints
  (("Goal"
    :use ((:instance zrr-receipt-rollback-when-committed)
          (:instance zrr-receipt-rollback-when-rejected))
    :in-theory
    (disable zrr-receipt-rollback-when-committed
             zrr-receipt-rollback-when-rejected))))

(defthm zrr-receipt-rollback-summary
  (equal
   (xef-word-bi-summary
    (zrr-rollback-receipt (zrr-receipt patch source))
    table)
   (xef-word-bi-summary source table))
  :hints
  (("Goal"
    :use ((:instance zrr-receipt-rollback-correct)
          (:instance zvr-word-bi-summary-of-true-list-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Ground witness
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *zrr-patch*
  (list (zyp-keep 2)
        (zyp-drop 2)
        (zyp-insert (xef-rle-encode '(x x y)))
        (zyp-keep 1)))

(assert-event
 (let* ((source '(a b c d e f))
        (receipt (zrr-receipt *zrr-patch* source)))
   (and (zrr-receipt-committed-p receipt)
        (equal (zrr-receipt-word receipt)
               '(a b x x y e f))
        (equal (zrr-rollback-receipt receipt)
               source))))

(defxdoc zrr-user-interface
  :parents (zqz-reversible-patch-receipts)
  :short "Public interface for reversible patch receipts."
  :long
  "<p><tt>ZRR-INVERSE</tt> compiles a canonical source-indexed inverse patch.
  <tt>ZRR-RECEIPT</tt> records the committed word and inverse, while
  <tt>ZRR-ROLLBACK-RECEIPT</tt> performs total rollback.  The certified laws
  are <tt>ZRR-INVERSE-SUCCEEDS</tt>, <tt>ZRR-INVERSE-RESTORES</tt>,
  <tt>ZRR-TRANSACTIONAL-ROLLBACK</tt>, and
  <tt>ZRR-RECEIPT-ROLLBACK-CORRECT</tt>.</p>")
