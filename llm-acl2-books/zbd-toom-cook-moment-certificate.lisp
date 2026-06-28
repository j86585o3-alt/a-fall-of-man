; Compact moment certificates for generated rational Toom-Cook plans.
(in-package "ACL2")
(include-book "zbc-toom-cook-cyclic-generator")
(include-book "std/lists/nth" :dir :system)

(defun tc-point-matrix-aux (rows row-power cols col-power point coefficient)
  (declare (xargs :measure (nfix rows)))
  (if (zp rows)
      nil
    (cons (tc-powers-aux cols point
                         (* coefficient row-power col-power))
          (tc-point-matrix-aux (1- rows) (* point row-power)
                               cols col-power point coefficient))))

(defthm tc-powers-aux-times-power
  (equal (wbc-row-scale coefficient
                        (tc-powers-aux count point power))
         (tc-powers-aux count point (* coefficient power)))
  :hints (("Goal" :induct (tc-powers-aux count point power)
           :in-theory (enable tc-powers-aux wbc-row-scale))))

(defthm tc-scaled-outer-is-point-matrix
  (equal (wbc-matrix-scale
          coefficient
          (wbc-outer (tc-powers-aux rows point row-power)
                     (tc-powers-aux cols point col-power)))
         (tc-point-matrix-aux rows row-power cols col-power
                              point coefficient))
  :hints (("Goal"
           :induct (tc-powers-aux rows point row-power)
           :in-theory (enable wbc-matrix-scale wbc-outer
                              tc-point-matrix-aux))))

(defthm tc-term-matrix-is-point-matrix
  (equal (wbc-term-matrix
          (cons (tc-evaluation-row n point)
                (tc-evaluation-row n point))
          coefficient)
         (tc-point-matrix-aux n 1 n 1 point coefficient))
  :hints (("Goal"
           :in-theory (enable wbc-term-matrix tc-evaluation-row))))

(defun tc-powers-nth-induct (count point power k)
  (if (or (zp count) (zp k))
      (list point power)
    (tc-powers-nth-induct (1- count) point (* point power) (1- k))))

(defthm consp-of-tc-powers-aux
  (equal (consp (tc-powers-aux count point power))
         (not (zp count)))
  :hints (("Goal" :in-theory (enable tc-powers-aux))))

(defthm car-of-tc-powers-aux
  (implies (not (zp count))
           (equal (car (tc-powers-aux count point power)) power))
  :hints (("Goal" :in-theory (enable tc-powers-aux))))

(defthm tc-nth0-of-tc-powers-aux
  (implies (and (natp k) (< k (nfix count))
                (rationalp point) (rationalp power))
           (equal (tc-nth0 k (tc-powers-aux count point power))
                  (* power (expt point k))))
  :hints (("Goal"
           :induct (tc-powers-nth-induct count point power k)
           :in-theory (enable tc-powers-nth-induct tc-nth0 tc-powers-aux))))

(defthm consp-of-tc-point-matrix-aux
  (equal (consp (tc-point-matrix-aux rows row-power cols col-power point coefficient))
         (not (zp rows)))
  :hints (("Goal" :in-theory (enable tc-point-matrix-aux))))

(defthm car-of-tc-point-matrix-aux
  (implies (not (zp rows))
           (equal (car (tc-point-matrix-aux
                        rows row-power cols col-power point coefficient))
                  (tc-powers-aux cols point
                                 (* coefficient row-power col-power))))
  :hints (("Goal" :in-theory (enable tc-point-matrix-aux))))

(defun tc-point-matrix-nth-induct
  (rows row-power cols col-power point coefficient row)
  (if (or (zp rows) (zp row))
      (list row-power cols col-power point coefficient)
    (tc-point-matrix-nth-induct
     (1- rows) (* point row-power) cols col-power point coefficient (1- row))))

(defthm tc-nth0-row-of-point-matrix
  (implies (and (natp row) (< row (nfix rows))
                (rationalp row-power) (rationalp col-power)
                (rationalp point) (rationalp coefficient))
           (equal (tc-nth0 row
                           (tc-point-matrix-aux
                            rows row-power cols col-power point coefficient))
                  (tc-powers-aux
                   cols point
                   (* coefficient row-power col-power
                      (expt point row)))))
  :hints (("Goal"
           :induct (tc-point-matrix-nth-induct
                    rows row-power cols col-power point coefficient row)
           :in-theory (enable tc-point-matrix-nth-induct
                              tc-nth0 tc-point-matrix-aux))))

(defun tc-matrix-entry (row column matrix)
  (tc-nth0 column (tc-nth0 row matrix)))

(defthm tc-entry-of-point-matrix
  (implies (and (natp row) (< row (nfix rows))
                (natp column) (< column (nfix cols))
                (rationalp row-power) (rationalp col-power)
                (rationalp point) (rationalp coefficient))
           (equal (tc-matrix-entry
                   row column
                   (tc-point-matrix-aux
                    rows row-power cols col-power point coefficient))
                  (* coefficient row-power col-power
                     (expt point (+ row column)))))
  :hints (("Goal"
           :use ((:instance tc-nth0-row-of-point-matrix)
                 (:instance tc-nth0-of-tc-powers-aux
                            (k column) (count cols)
                            (power (* coefficient row-power col-power
                                      (expt point row)))))
           :in-theory (enable tc-matrix-entry))))

(defthm tc-entry-of-generated-term-matrix
  (implies (and (natp row) (< row (nfix n))
                (natp column) (< column (nfix n))
                (rationalp point) (rationalp coefficient))
           (equal (tc-matrix-entry
                   row column
                   (wbc-term-matrix
                    (cons (tc-evaluation-row n point)
                          (tc-evaluation-row n point))
                    coefficient))
                  (* coefficient (expt point (+ row column)))))
  :hints (("Goal"
           :use ((:instance tc-entry-of-point-matrix
                            (rows n) (row-power 1)
                            (cols n) (col-power 1)))
           :in-theory (disable tc-term-matrix-is-point-matrix))))

(defun tc-two-list-nth-induct (a b k)
  (if (or (endp a) (endp b) (zp k))
      (list a b)
    (tc-two-list-nth-induct (cdr a) (cdr b) (1- k))))

(defthm tc-nth0-of-wbc-row-add
  (implies (and (natp k) (< k (len a))
                (equal (len a) (len b)))
           (equal (tc-nth0 k (wbc-row-add a b))
                  (+ (tc-nth0 k a) (tc-nth0 k b))))
  :hints (("Goal" :induct (tc-two-list-nth-induct a b k)
           :in-theory (enable tc-two-list-nth-induct tc-nth0 wbc-row-add))))

(defthm tc-nth0-row-of-wbc-matrix-add
  (implies (and (natp row) (< row (len a))
                (equal (len a) (len b)))
           (equal (tc-nth0 row (wbc-matrix-add a b))
                  (wbc-row-add (tc-nth0 row a)
                               (tc-nth0 row b))))
  :hints (("Goal" :induct (tc-two-list-nth-induct a b row)
           :in-theory (enable tc-two-list-nth-induct tc-nth0 wbc-matrix-add))))

(defthm tc-entry-of-wbc-matrix-add
  (implies (and (natp row) (< row (len a))
                (natp column) (< column (len (tc-nth0 row a)))
                (equal (len a) (len b))
                (equal (len (tc-nth0 row a))
                       (len (tc-nth0 row b))))
           (equal (tc-matrix-entry row column (wbc-matrix-add a b))
                  (+ (tc-matrix-entry row column a)
                     (tc-matrix-entry row column b))))
  :hints (("Goal"
           :use ((:instance tc-nth0-row-of-wbc-matrix-add)
                 (:instance tc-nth0-of-wbc-row-add
                            (k column)
                            (a (tc-nth0 row a))
                            (b (tc-nth0 row b))))
           :in-theory (enable tc-matrix-entry))))

(defun tc-matrix-nth-induct (rows matrix row)
  (if (or (zp rows) (zp row) (endp matrix))
      matrix
    (tc-matrix-nth-induct (1- rows) (cdr matrix) (1- row))))

(defthm rational-rowp-of-tc-nth0-of-rational-matrixp
  (implies (and (rational-matrixp rows cols matrix)
                (natp row) (< row (nfix rows)))
           (rational-rowp cols (tc-nth0 row matrix)))
  :hints (("Goal"
           :induct (tc-matrix-nth-induct rows matrix row)
           :in-theory (enable tc-matrix-nth-induct
                              rational-matrixp tc-nth0))))

(defthm len-of-tc-nth0-of-rational-matrixp
  (implies (and (rational-matrixp rows cols matrix)
                (natp row) (< row (nfix rows)))
           (equal (len (tc-nth0 row matrix)) (nfix cols)))
  :hints (("Goal"
           :use ((:instance rational-rowp-of-tc-nth0-of-rational-matrixp))
           :in-theory (enable rational-rowp))))

(defthm consp-of-tc-plan-terms-aux
  (equal (consp (tc-plan-terms-aux count point n))
         (not (zp count)))
  :hints (("Goal" :in-theory (enable tc-plan-terms-aux))))

(defthm tc-generated-output-plan-validp
  (implies (and (posp n) (posp count)
                (natp point)
                (rational-listp post)
                (equal (len post) (nfix count)))
           (wbc-plan-validp
            n (tc-plan-terms-aux count point n) post))
  :hints (("Goal" :in-theory (enable wbc-plan-validp))))

(defun tc-nth-rational-induct (k xs)
  (if (or (zp k) (endp xs))
      xs
    (tc-nth-rational-induct (1- k) (cdr xs))))

(defthm rationalp-of-tc-nth0-of-rational-listp
  (implies (and (rational-listp xs)
                (natp k)
                (< k (len xs)))
           (rationalp (tc-nth0 k xs)))
  :hints (("Goal"
           :induct (tc-nth-rational-induct k xs)
           :in-theory (enable tc-nth-rational-induct tc-nth0))))

(defthm rationalp-of-tc-matrix-entry
  (implies (and (rational-matrixp rows cols matrix)
                (natp row) (< row (nfix rows))
                (natp column) (< column (nfix cols)))
           (rationalp (tc-matrix-entry row column matrix)))
  :hints (("Goal"
           :induct (tc-matrix-nth-induct rows matrix row)
           :in-theory (enable tc-matrix-nth-induct rational-matrixp
                              rational-rowp tc-matrix-entry tc-nth0))))

(defthm tc-nth0-of-nil
  (implies (natp k)
           (equal (tc-nth0 k nil) 0))
  :hints (("Goal" :induct (tc-nth-rational-induct k nil)
           :in-theory (enable tc-nth-rational-induct tc-nth0))))

(defthm rational-matrixp-of-generated-plan-matrix
  (implies (and (posp n)
                (posp count)
                (natp point)
                (rational-listp post)
                (equal (len post) (nfix count)))
           (rational-matrixp
            n n
            (wbc-plan-matrix
             (tc-plan-terms-aux count point n) post)))
  :hints (("Goal"
           :use ((:instance tc-generated-output-plan-validp)
                 (:instance rational-matrixp-of-plan-matrix
                            (terms (tc-plan-terms-aux count point n))))
           :in-theory (disable tc-generated-output-plan-validp
                               rational-matrixp-of-plan-matrix))))

(defthm rationalp-of-generated-plan-entry-positive
  (implies (and (posp n)
                (posp count)
                (natp point)
                (rational-listp post)
                (equal (len post) (nfix count))
                (natp row) (< row n)
                (natp column) (< column n))
           (rationalp
            (tc-matrix-entry
             row column
             (wbc-plan-matrix
              (tc-plan-terms-aux count point n) post))))
  :hints (("Goal"
           :use ((:instance rational-matrixp-of-generated-plan-matrix)
                 (:instance rationalp-of-tc-matrix-entry
                            (rows n) (cols n)
                            (matrix
                             (wbc-plan-matrix
                              (tc-plan-terms-aux count point n) post))))
           :in-theory (disable rational-matrixp-of-generated-plan-matrix
                               rationalp-of-tc-matrix-entry))))

(defthm rationalp-of-generated-plan-entry
  (implies (and (posp n)
                (natp count)
                (natp point)
                (rational-listp post)
                (equal (len post) count)
                (natp row) (< row n)
                (natp column) (< column n))
           (rationalp
            (tc-matrix-entry
             row column
             (wbc-plan-matrix
              (tc-plan-terms-aux count point n) post))))
  :hints (("Goal" :cases ((zp count)))
          ("Subgoal 2"
           :use ((:instance rationalp-of-generated-plan-entry-positive))
           :in-theory (disable rationalp-of-generated-plan-entry-positive))
          ("Subgoal 1"
           :in-theory (enable tc-plan-terms-aux wbc-plan-matrix
                              tc-matrix-entry))))

(defthm rational-matrixp-of-generated-term-matrix
  (implies (and (posp n)
                (natp point)
                (rationalp coefficient))
           (rational-matrixp
            n n
            (wbc-term-matrix
             (cons (tc-evaluation-row n point)
                   (tc-evaluation-row n point))
             coefficient)))
  :hints (("Goal"
           :use ((:instance rational-matrixp-of-wbc-term-matrix
                            (term
                             (cons (tc-evaluation-row n point)
                                   (tc-evaluation-row n point)))))
           :in-theory (enable rational-rowp-of-tc-evaluation-row))))

(defthm tc-entry-of-wbc-matrix-add-rational
  (implies (and (posp n)
                (rational-matrixp n n a)
                (rational-matrixp n n b)
                (natp row) (< row n)
                (natp column) (< column n))
           (equal (tc-matrix-entry row column (wbc-matrix-add a b))
                  (+ (tc-matrix-entry row column a)
                     (tc-matrix-entry row column b))))
  :hints (("Goal"
           :use ((:instance rational-matrixp-implies-length
                            (matrix a) (m n))
                 (:instance rational-matrixp-implies-length
                            (matrix b) (m n))
                 (:instance len-of-tc-nth0-of-rational-matrixp
                            (rows n) (cols n) (matrix a))
                 (:instance len-of-tc-nth0-of-rational-matrixp
                            (rows n) (cols n) (matrix b))
                 (:instance tc-entry-of-wbc-matrix-add))
           :in-theory (disable rational-matrixp-implies-length
                               len-of-tc-nth0-of-rational-matrixp
                               tc-entry-of-wbc-matrix-add))))

(defthm rational-matrixp-of-generated-point-matrix
  (implies (and (posp n)
                (natp point)
                (rationalp coefficient))
           (rational-matrixp
            n n
            (tc-point-matrix-aux n 1 n 1 point coefficient)))
  :hints (("Goal"
           :use ((:instance rational-matrixp-of-generated-term-matrix))
           :in-theory (disable rational-matrixp-of-generated-term-matrix))))

(defthm tc-generated-plan-entry-step
  (implies (and (posp n)
                (natp point)
                (rational-listp post)
                (consp post)
                (natp row) (< row n)
                (natp column) (< column n))
           (equal
            (tc-matrix-entry
             row column
             (wbc-plan-matrix
              (tc-plan-terms-aux (len post) point n) post))
            (+ (* (car post) (expt point (+ row column)))
               (tc-matrix-entry
                row column
                (wbc-plan-matrix
                 (tc-plan-terms-aux (len (cdr post)) (1+ point) n)
                 (cdr post))))))
  :hints (("Goal" :cases ((endp (cdr post))))
          ("Subgoal 2"
           :do-not-induct t
           :expand ((tc-plan-terms-aux (len post) point n)
                    (wbc-plan-matrix
                     (cons (cons (tc-evaluation-row n point)
                                 (tc-evaluation-row n point))
                           (tc-plan-terms-aux (len (cdr post))
                                              (1+ point) n))
                     post)
                    (wbc-plan-matrix
                     (cons (cons (tc-evaluation-row n point)
                                 (tc-evaluation-row n point))
                           (tc-plan-terms-aux (+ -1 (len post))
                                              (1+ point) n))
                     post))
           :use ((:instance rational-matrixp-of-generated-point-matrix
                            (coefficient (car post)))
                 (:instance rational-matrixp-of-generated-plan-matrix
                            (count (len (cdr post)))
                            (point (1+ point))
                            (post (cdr post)))
                 (:instance rational-matrixp-implies-length
                            (matrix
                             (wbc-plan-matrix
                              (tc-plan-terms-aux (len (cdr post))
                                                 (1+ point) n)
                              (cdr post)))
                            (m n))
                 (:instance tc-entry-of-wbc-matrix-add-rational
                            (a (tc-point-matrix-aux
                                n 1 n 1 point (car post)))
                            (b (wbc-plan-matrix
                                (tc-plan-terms-aux (len (cdr post))
                                                   (1+ point) n)
                                (cdr post))))
                 (:instance tc-entry-of-generated-term-matrix
                            (coefficient (car post))))
           :in-theory
           (disable tc-plan-terms-aux wbc-plan-matrix tc-evaluation-row
                    rational-matrixp-of-generated-point-matrix
                    rational-matrixp-of-generated-plan-matrix
                    rational-matrixp-implies-length
                    tc-entry-of-wbc-matrix-add-rational
                    tc-entry-of-generated-term-matrix))
          ("Subgoal 1"
           :do-not-induct t
           :expand ((tc-plan-terms-aux (len post) point n)
                    (tc-plan-terms-aux (+ -1 (len post))
                                       (1+ point) n)
                    (tc-plan-terms-aux 0 (1+ point) n)
                    (wbc-plan-matrix
                     (cons (cons (tc-evaluation-row n point)
                                 (tc-evaluation-row n point))
                           (tc-plan-terms-aux (+ -1 (len post))
                                              (1+ point) n))
                     post)
                    (wbc-plan-matrix
                     (cons (cons (tc-evaluation-row n point)
                                 (tc-evaluation-row n point)) nil)
                     post)
                    (wbc-plan-matrix nil (cdr post)))
           :use ((:instance tc-entry-of-generated-term-matrix
                            (coefficient (car post))))
           :in-theory
           (disable tc-plan-terms-aux wbc-plan-matrix tc-evaluation-row
                    tc-entry-of-generated-term-matrix))))

(defun tc-plan-entry-acc-induct (count point post row column acc)
  (if (or (zp count) (endp post))
      (list point row column acc)
    (let ((term (* (car post)
                   (expt (nfix point) (+ (nfix row) (nfix column))))))
      (tc-plan-entry-acc-induct
       (1- count) (1+ (nfix point)) (cdr post) row column
       (+ acc term)))))

(defthm tc-entry-of-generated-plan-matrix-with-acc
  (implies (and (posp n)
                (natp count)
                (natp point)
                (rational-listp post)
                (equal (len post) count)
                (natp row) (< row n)
                (natp column) (< column n)
                (acl2-numberp acc))
           (equal
            (+ acc
               (tc-matrix-entry
                row column
                (wbc-plan-matrix
                 (tc-plan-terms-aux count point n) post)))
            (tc-row-moment-aux post point (+ row column) acc)))
  :hints (("Goal"
           :induct (tc-plan-entry-acc-induct
                    count point post row column acc)
           :in-theory
           (e/d (tc-plan-entry-acc-induct tc-row-moment-aux)
                (tc-generated-plan-entry-step
                 tc-plan-terms-aux wbc-plan-matrix)))
          ("Subgoal *1/2"
           :use ((:instance tc-generated-plan-entry-step)
                 (:instance rationalp-of-generated-plan-entry
                            (count (len (cdr post)))
                            (point (1+ point))
                            (post (cdr post)))
                 (:instance rationalp-of-generated-plan-entry
                            (count (len post))))
           :in-theory
           (disable tc-generated-plan-entry-step
                    rationalp-of-generated-plan-entry
                    tc-plan-terms-aux wbc-plan-matrix))
          ("Subgoal *1/1"
           :in-theory
           (enable tc-plan-terms-aux wbc-plan-matrix
                   tc-matrix-entry tc-row-moment-aux tc-nth0))))

(defthm tc-entry-of-generated-plan-matrix
  (implies (and (posp n) (posp count)
                (natp point)
                (rational-listp post)
                (equal (len post) (nfix count))
                (natp row) (< row n)
                (natp column) (< column n))
           (equal
            (tc-matrix-entry
             row column
             (wbc-plan-matrix
              (tc-plan-terms-aux count point n) post))
            (tc-row-moment-aux post point (+ row column) 0)))
  :hints (("Goal"
           :use ((:instance tc-entry-of-generated-plan-matrix-with-acc
                            (acc 0))
                 (:instance rationalp-of-generated-plan-entry))
           :in-theory
           (disable tc-entry-of-generated-plan-matrix-with-acc
                    rationalp-of-generated-plan-entry))))

(defun tc-compact-post-certifiesp (n out post)
  (let ((m (if (posp n) (1- (* 2 n)) 0)))
    (and (posp n)
         (rational-listp post)
         (equal (len post) m)
         (tc-post-moments-okp n out post))))

(defun tc-compact-bank-certifies-aux (count out n posts)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (endp posts)
    (and (consp posts)
         (tc-compact-post-certifiesp n (nfix out) (car posts))
         (tc-compact-bank-certifies-aux
          (1- count) (1+ (nfix out)) n (cdr posts)))))

(defun tc-generated-compact-certifiesp (n)
  (tc-compact-bank-certifies-aux n 0 n (tc-plan-posts n)))

(defun tc-moment-index-induct (count degree k)
  (if (or (zp count) (zp k))
      (list count degree k)
    (tc-moment-index-induct (1- count) (1+ (nfix degree)) (1- k))))

(defthm tc-post-moments-okp-aux-entry
  (implies (and (tc-post-moments-okp-aux count degree n out post)
                (natp k) (< k (nfix count)))
           (equal (tc-row-moment post (+ (nfix degree) k))
                  (if (equal (mod (+ (nfix degree) k) (nfix n))
                             (nfix out))
                      1 0)))
  :hints (("Goal"
           :induct (tc-moment-index-induct count degree k)
           :in-theory (enable tc-moment-index-induct
                              tc-post-moments-okp-aux
                              tc-row-moment))))

(defthm tc-post-moments-okp-entry
  (implies (and (tc-post-moments-okp n out post)
                (natp degree)
                (< degree (1- (* 2 n))))
           (equal (tc-row-moment post degree)
                  (if (equal (mod degree n) (nfix out)) 1 0)))
  :hints (("Goal"
           :use ((:instance tc-post-moments-okp-aux-entry
                            (count (1- (* 2 n)))
                            (degree 0)
                            (k degree)))
           :in-theory (enable tc-post-moments-okp))))

(defthm wbc-delta-row-aux-open
  (implies (not (zp count))
           (equal (wbc-delta-row-aux count j i out n)
                  (cons (if (equal (mod (+ (nfix i) (nfix j)) (nfix n))
                                           (nfix out)) 1 0)
                        (wbc-delta-row-aux (1- count) (1+ (nfix j))
                                           i out n))))
  :hints (("Goal" :expand ((wbc-delta-row-aux count j i out n)))))
(defthm wbc-delta-matrix-aux-open
  (implies (not (zp count))
           (equal (wbc-delta-matrix-aux count i out n)
                  (cons (wbc-delta-row-aux n 0 i out n)
                        (wbc-delta-matrix-aux (1- count)
                                              (1+ (nfix i)) out n))))
  :hints (("Goal" :expand ((wbc-delta-matrix-aux count i out n)))))
(defun tc-delta-row-nth-induct (count j i out n column)
  (if (or (zp count) (zp column))
      (list j i out n)
    (tc-delta-row-nth-induct (1- count) (1+ j) i out n (1- column))))
(defthm tc-nth0-of-delta-row-aux
  (implies (and (natp count) (natp j) (natp i) (natp out) (posp n)
                (natp column) (< column count))
           (equal (tc-nth0 column (wbc-delta-row-aux count j i out n))
                  (if (equal (mod (+ i j column) n) out) 1 0)))
  :hints (("Goal" :induct (tc-delta-row-nth-induct count j i out n column)
           :in-theory (e/d (tc-delta-row-nth-induct tc-nth0)
                           (wbc-delta-row-aux)))))
(defun tc-delta-matrix-nth-induct (count i out n row)
  (if (or (zp count) (zp row))
      (list i out n)
    (tc-delta-matrix-nth-induct (1- count) (1+ i) out n (1- row))))
(defthm tc-nth0-row-of-delta-matrix-aux
  (implies (and (natp count) (natp i)
                (natp row) (< row count))
           (equal (tc-nth0 row (wbc-delta-matrix-aux count i out n))
                  (wbc-delta-row-aux n 0 (+ i row) out n)))
  :hints (("Goal" :induct (tc-delta-matrix-nth-induct count i out n row)
           :in-theory (e/d (tc-delta-matrix-nth-induct tc-nth0)
                           (wbc-delta-matrix-aux)))))
(defthm tc-entry-of-cyclic-matrix
  (implies (and (posp n) (natp out)
                (natp row) (< row n) (natp column) (< column n))
           (equal (tc-matrix-entry row column (wbc-cyclic-matrix n out))
                  (if (equal (mod (+ row column) n) out) 1 0)))
  :hints (("Goal"
           :use ((:instance tc-nth0-row-of-delta-matrix-aux
                            (count n) (i 0))
                 (:instance tc-nth0-of-delta-row-aux
                            (count n) (j 0) (i row)))
           :in-theory
           (e/d (tc-matrix-entry wbc-cyclic-matrix)
                (wbc-delta-matrix-aux wbc-delta-row-aux
                 wbc-delta-matrix-aux-open wbc-delta-row-aux-open
                 tc-nth0-row-of-delta-matrix-aux
                 tc-nth0-of-delta-row-aux)))))
(defthm tc-entry-of-compact-certified-plan
  (implies (and (tc-compact-post-certifiesp n out post)
                (natp out)
                (natp row) (< row n)
                (natp column) (< column n))
           (equal
            (tc-matrix-entry row column
             (wbc-plan-matrix (tc-plan-terms n) post))
            (if (equal (mod (+ row column) n) out) 1 0)))
  :hints (("Goal"
           :use ((:instance tc-entry-of-generated-plan-matrix
                            (count (1- (* 2 n)))
                            (point 0))
                 (:instance tc-post-moments-okp-entry
                            (degree (+ row column))))
           :in-theory
           (e/d (tc-compact-post-certifiesp tc-plan-terms
                 tc-row-moment)
                (tc-entry-of-generated-plan-matrix
                 tc-post-moments-okp-entry
                 tc-post-moments-okp-aux-entry)))))

(defthm tc-nth0-is-nth-when-in-bounds
  (implies (and (natp k) (< k (len xs)))
           (equal (tc-nth0 k xs) (nth k xs)))
  :hints (("Goal" :induct (tc-nth0 k xs)
           :in-theory (enable tc-nth0 nth))))

(defthm tc-true-listp-when-rational-listp
  (implies (rational-listp xs) (true-listp xs))
  :hints (("Goal" :induct (rational-listp xs)
           :in-theory (enable rational-listp))))

(defthm tc-compact-post-plan-validp
  (implies (tc-compact-post-certifiesp n out post)
           (wbc-plan-validp n (tc-plan-terms n) post))
  :hints (("Goal"
           :use ((:instance tc-generated-output-plan-validp
                            (count (1- (* 2 n))) (point 0)))
           :in-theory (e/d (tc-compact-post-certifiesp tc-plan-terms)
                           (tc-generated-output-plan-validp)))))

(defthm tc-rational-matrixp-of-compact-plan
  (implies (tc-compact-post-certifiesp n out post)
           (rational-matrixp n n
             (wbc-plan-matrix (tc-plan-terms n) post)))
  :hints (("Goal"
           :use ((:instance tc-compact-post-plan-validp)
                 (:instance rational-matrixp-of-plan-matrix
                            (terms (tc-plan-terms n))))
           :in-theory nil)))

(defthm tc-compact-plan-row-rationalp
  (implies (and (tc-compact-post-certifiesp n out post)
                (natp row) (< row n))
           (rational-rowp n
             (tc-nth0 row
               (wbc-plan-matrix (tc-plan-terms n) post))))
  :hints (("Goal"
           :use ((:instance tc-rational-matrixp-of-compact-plan
                            (n n) (out out) (post post))
                 (:instance rational-rowp-of-tc-nth0-of-rational-matrixp
                            (rows n) (cols n) (row row)
                            (matrix (wbc-plan-matrix
                                     (tc-plan-terms n) post))))
           :in-theory (enable tc-compact-post-certifiesp))))

(defthm tc-cyclic-row-rationalp
  (implies (and (posp n) (natp row) (< row n))
           (rational-rowp n
             (tc-nth0 row (wbc-cyclic-matrix n out))))
  :hints (("Goal"
           :use ((:instance rational-matrixp-of-cyclic-matrix
                            (n n) (out out))
                 (:instance rational-rowp-of-tc-nth0-of-rational-matrixp
                            (rows n) (cols n) (row row)
                            (matrix (wbc-cyclic-matrix n out))))
           :in-theory
           (e/d (nfix posp)
                (wbc-cyclic-matrix wbc-delta-matrix-aux
                 wbc-delta-row-aux wbc-delta-matrix-aux-open
                 wbc-delta-row-aux-open
                 rational-matrixp-of-cyclic-matrix
                 rational-rowp-of-tc-nth0-of-rational-matrixp
                 tc-nth0-row-of-delta-matrix-aux
                 tc-nth0-of-delta-row-aux)))))

(defthm tc-true-listp-of-compact-plan-row
  (implies (and (tc-compact-post-certifiesp n out post)
                (natp row) (< row n))
           (true-listp
             (tc-nth0 row
               (wbc-plan-matrix (tc-plan-terms n) post))))
  :hints (("Goal"
           :use ((:instance tc-compact-plan-row-rationalp)
                 (:instance tc-true-listp-when-rational-listp
                            (xs (tc-nth0 row
                                  (wbc-plan-matrix
                                   (tc-plan-terms n) post)))))
           :in-theory (enable rational-rowp))))

(defthm tc-true-listp-of-cyclic-row
  (implies (and (posp n) (natp row) (< row n))
           (true-listp (tc-nth0 row (wbc-cyclic-matrix n out))))
  :hints (("Goal"
           :use ((:instance tc-cyclic-row-rationalp)
                 (:instance tc-true-listp-when-rational-listp
                            (xs (tc-nth0 row
                                  (wbc-cyclic-matrix n out)))))
           :in-theory
           (e/d (rational-rowp)
                (wbc-cyclic-matrix wbc-delta-matrix-aux
                 wbc-delta-row-aux wbc-delta-matrix-aux-open
                 wbc-delta-row-aux-open tc-cyclic-row-rationalp
                 tc-true-listp-when-rational-listp
                 tc-nth0-row-of-delta-matrix-aux
                 tc-nth0-of-delta-row-aux)))))

(defthm tc-len-of-compact-plan-row
  (implies (and (tc-compact-post-certifiesp n out post)
                (natp row) (< row n))
           (equal (len (tc-nth0 row
                         (wbc-plan-matrix (tc-plan-terms n) post)))
                  n))
  :hints (("Goal" :use ((:instance tc-compact-plan-row-rationalp))
           :in-theory (enable rational-rowp tc-compact-post-certifiesp))))

(defthm tc-len-of-cyclic-row
  (implies (and (posp n) (natp row) (< row n))
           (equal (len (tc-nth0 row (wbc-cyclic-matrix n out))) n))
  :hints (("Goal"
           :use ((:instance tc-cyclic-row-rationalp))
           :in-theory
           (e/d (rational-rowp nfix posp)
                (wbc-cyclic-matrix wbc-delta-matrix-aux
                 wbc-delta-row-aux wbc-delta-matrix-aux-open
                 wbc-delta-row-aux-open tc-cyclic-row-rationalp
                 tc-nth0-row-of-delta-matrix-aux
                 tc-nth0-of-delta-row-aux)))))

(defthm tc-nth0-is-nth-of-compact-plan-row
  (implies (and (tc-compact-post-certifiesp n out post)
                (natp row) (< row n)
                (natp column) (< column n))
           (equal
            (tc-nth0 column
             (tc-nth0 row (wbc-plan-matrix (tc-plan-terms n) post)))
            (nth column
             (tc-nth0 row (wbc-plan-matrix (tc-plan-terms n) post)))))
  :hints (("Goal"
           :use ((:instance tc-len-of-compact-plan-row)
                 (:instance tc-nth0-is-nth-when-in-bounds
                            (k column)
                            (xs (tc-nth0 row
                                  (wbc-plan-matrix
                                   (tc-plan-terms n) post)))))
           :in-theory nil)))

(defthm tc-nth0-is-nth-of-cyclic-row
  (implies (and (posp n) (natp row) (< row n)
                (natp column) (< column n))
           (equal
            (tc-nth0 column (tc-nth0 row (wbc-cyclic-matrix n out)))
            (nth column (tc-nth0 row (wbc-cyclic-matrix n out)))))
  :hints (("Goal"
           :use ((:instance tc-len-of-cyclic-row)
                 (:instance tc-nth0-is-nth-when-in-bounds
                            (k column)
                            (xs (tc-nth0 row
                                  (wbc-cyclic-matrix n out)))))
           :in-theory nil)))

(defthm tc-compact-post-certifiesp-implies-posp
  (implies (tc-compact-post-certifiesp n out post) (posp n))
  :hints (("Goal" :in-theory (enable tc-compact-post-certifiesp))))

(defthm tc-equality-chain-5
  (implies (and (equal a b) (equal b c)
                (equal d c) (equal d e))
           (equal a e))
  :rule-classes nil)


(defthm tc-nth0-entry-of-compact-certified-plan
  (implies (and (tc-compact-post-certifiesp n out post)
                (natp out) (natp row) (< row n)
                (natp column) (< column n))
           (equal
            (tc-nth0 column
             (tc-nth0 row (wbc-plan-matrix (tc-plan-terms n) post)))
            (if (equal (mod (+ row column) n) out) 1 0)))
  :hints (("Goal"
           :use ((:instance tc-entry-of-compact-certified-plan
                            (n n) (out out) (post post)
                            (row row) (column column)))
           :in-theory '((:definition tc-matrix-entry)))))

(defthm tc-nth0-entry-of-cyclic-matrix
  (implies (and (posp n) (natp out)
                (natp row) (< row n)
                (natp column) (< column n))
           (equal
            (tc-nth0 column
             (tc-nth0 row (wbc-cyclic-matrix n out)))
            (if (equal (mod (+ row column) n) out) 1 0)))
  :hints (("Goal"
           :use ((:instance tc-entry-of-cyclic-matrix
                            (n n) (out out)
                            (row row) (column column)))
           :in-theory '((:definition tc-matrix-entry)))))

(defthm tc-nth-of-compact-plan-row-equals-cyclic
  (implies (and (tc-compact-post-certifiesp n out post)
                (natp out) (natp row) (< row n)
                (natp column) (< column n))
           (equal
            (nth column
             (tc-nth0 row (wbc-plan-matrix (tc-plan-terms n) post)))
            (nth column
             (tc-nth0 row (wbc-cyclic-matrix n out)))))
  :hints (("Goal"
           :use ((:instance tc-equality-chain-5
                    (a (nth column
                         (tc-nth0 row
                          (wbc-plan-matrix (tc-plan-terms n) post))))
                    (b (tc-nth0 column
                         (tc-nth0 row
                          (wbc-plan-matrix (tc-plan-terms n) post))))
                    (c (if (equal (mod (+ row column) n) out) 1 0))
                    (d (tc-nth0 column
                         (tc-nth0 row (wbc-cyclic-matrix n out))))
                    (e (nth column
                         (tc-nth0 row (wbc-cyclic-matrix n out)))))
                 (:instance tc-nth0-is-nth-of-compact-plan-row
                            (n n) (out out) (post post)
                            (row row) (column column))
                 (:instance tc-nth0-entry-of-compact-certified-plan
                            (n n) (out out) (post post)
                            (row row) (column column))
                 (:instance tc-nth0-entry-of-cyclic-matrix
                            (n n) (out out)
                            (row row) (column column))
                 (:instance tc-nth0-is-nth-of-cyclic-row
                            (n n) (out out)
                            (row row) (column column))
                 (:instance tc-compact-post-certifiesp-implies-posp
                            (n n) (out out) (post post)))
           :in-theory nil)))

(defthm tc-row-of-compact-plan-equals-cyclic-row
  (implies (and (tc-compact-post-certifiesp n out post)
                (natp out) (natp row) (< row n))
           (equal
            (tc-nth0 row (wbc-plan-matrix (tc-plan-terms n) post))
            (tc-nth0 row (wbc-cyclic-matrix n out))))
  :hints
  (("Goal"
    :use ((:functional-instance
           equal-by-nths
           (equal-by-nths-lhs
            (lambda ()
              (tc-nth0 row
               (wbc-plan-matrix (tc-plan-terms n) post))))
           (equal-by-nths-rhs
            (lambda ()
              (tc-nth0 row (wbc-cyclic-matrix n out))))
           (equal-by-nths-hyp
            (lambda ()
              (and (tc-compact-post-certifiesp n out post)
                   (natp out) (natp row) (< row n))))))
    :in-theory
    '((:rewrite tc-true-listp-of-compact-plan-row)
      (:rewrite tc-true-listp-of-cyclic-row)
      (:rewrite tc-len-of-compact-plan-row)
      (:rewrite tc-len-of-cyclic-row)
      (:rewrite tc-nth-of-compact-plan-row-equals-cyclic)
      (:rewrite tc-compact-post-certifiesp-implies-posp)))))

(defthm tc-true-listp-of-wbc-plan-matrix
  (true-listp (wbc-plan-matrix terms post))
  :hints (("Goal" :induct (wbc-plan-matrix terms post)
           :in-theory (enable wbc-plan-matrix wbc-term-matrix
                              wbc-matrix-scale wbc-outer wbc-matrix-add))))

(defthm tc-true-listp-of-wbc-cyclic-matrix
  (true-listp (wbc-cyclic-matrix n out))
  :hints (("Goal" :in-theory (enable wbc-cyclic-matrix
                                      wbc-delta-matrix-aux))))

(defthm tc-len-of-rational-matrixp
  (implies (rational-matrixp rows cols matrix)
           (equal (len matrix) (nfix rows)))
  :hints (("Goal" :induct (rational-matrixp rows cols matrix)
           :in-theory (enable rational-matrixp))))

(defthm tc-len-of-compact-plan-matrix
  (implies (tc-compact-post-certifiesp n out post)
           (equal (len (wbc-plan-matrix (tc-plan-terms n) post)) n))
  :hints (("Goal"
           :use ((:instance tc-rational-matrixp-of-compact-plan)
                 (:instance tc-len-of-rational-matrixp
                            (rows n) (cols n)
                            (matrix (wbc-plan-matrix
                                     (tc-plan-terms n) post))))
           :in-theory (enable tc-compact-post-certifiesp nfix posp))))

(defthm tc-len-of-cyclic-matrix
  (implies (posp n)
           (equal (len (wbc-cyclic-matrix n out)) n))
  :hints (("Goal"
           :use ((:instance rational-matrixp-of-cyclic-matrix)
                 (:instance tc-len-of-rational-matrixp
                            (rows n) (cols n)
                            (matrix (wbc-cyclic-matrix n out))))
           :in-theory
           (e/d (nfix posp)
                (wbc-cyclic-matrix wbc-delta-matrix-aux
                 wbc-delta-row-aux wbc-delta-matrix-aux-open
                 wbc-delta-row-aux-open
                 rational-matrixp-of-cyclic-matrix
                 tc-len-of-rational-matrixp)))))

(defthm tc-nth0-is-nth-of-compact-plan-matrix
  (implies (and (tc-compact-post-certifiesp n out post)
                (natp row) (< row n))
           (equal
            (tc-nth0 row (wbc-plan-matrix (tc-plan-terms n) post))
            (nth row (wbc-plan-matrix (tc-plan-terms n) post))))
  :hints (("Goal"
           :use ((:instance tc-len-of-compact-plan-matrix)
                 (:instance tc-nth0-is-nth-when-in-bounds
                            (k row)
                            (xs (wbc-plan-matrix
                                 (tc-plan-terms n) post))))
           :in-theory nil)))

(defthm tc-nth0-is-nth-of-cyclic-matrix
  (implies (and (posp n) (natp row) (< row n))
           (equal
            (tc-nth0 row (wbc-cyclic-matrix n out))
            (nth row (wbc-cyclic-matrix n out))))
  :hints (("Goal"
           :use ((:instance tc-len-of-cyclic-matrix)
                 (:instance tc-nth0-is-nth-when-in-bounds
                            (k row)
                            (xs (wbc-cyclic-matrix n out))))
           :in-theory nil)))

(defthm tc-equality-chain-3
  (implies (and (equal a b) (equal b c) (equal c d))
           (equal a d))
  :rule-classes nil)

(defthm tc-nth-of-compact-plan-matrix-equals-cyclic
  (implies (and (tc-compact-post-certifiesp n out post)
                (natp out) (natp row) (< row n))
           (equal
            (nth row (wbc-plan-matrix (tc-plan-terms n) post))
            (nth row (wbc-cyclic-matrix n out))))
  :hints (("Goal"
           :use ((:instance tc-equality-chain-3
                    (a (nth row
                         (wbc-plan-matrix (tc-plan-terms n) post)))
                    (b (tc-nth0 row
                         (wbc-plan-matrix (tc-plan-terms n) post)))
                    (c (tc-nth0 row (wbc-cyclic-matrix n out)))
                    (d (nth row (wbc-cyclic-matrix n out))))
                 (:instance tc-nth0-is-nth-of-compact-plan-matrix
                            (n n) (out out) (post post) (row row))
                 (:instance tc-row-of-compact-plan-equals-cyclic-row
                            (n n) (out out) (post post) (row row))
                 (:instance tc-nth0-is-nth-of-cyclic-matrix
                            (n n) (out out) (row row))
                 (:instance tc-compact-post-certifiesp-implies-posp
                            (n n) (out out) (post post)))
           :in-theory nil)))

(defthm tc-compact-post-certificate-implies-matrix-certificate
  (implies (and (tc-compact-post-certifiesp n out post)
                (natp out))
           (equal (wbc-plan-matrix (tc-plan-terms n) post)
                  (wbc-cyclic-matrix n out)))
  :hints
  (("Goal"
    :use ((:functional-instance
           equal-by-nths
           (equal-by-nths-lhs
            (lambda ()
              (wbc-plan-matrix (tc-plan-terms n) post)))
           (equal-by-nths-rhs
            (lambda () (wbc-cyclic-matrix n out)))
           (equal-by-nths-hyp
            (lambda ()
              (and (tc-compact-post-certifiesp n out post)
                   (natp out))))))
    :in-theory
    '((:rewrite tc-true-listp-of-wbc-plan-matrix)
      (:rewrite tc-true-listp-of-wbc-cyclic-matrix)
      (:rewrite tc-len-of-compact-plan-matrix)
      (:rewrite tc-len-of-cyclic-matrix)
      (:rewrite tc-nth-of-compact-plan-matrix-equals-cyclic)
      (:rewrite tc-compact-post-certifiesp-implies-posp)))))

(defthm tc-compact-post-implies-plan-certificate
  (implies (and (tc-compact-post-certifiesp n out post)
                (natp out))
           (wbc-plan-certifies-outputp
            n out (tc-plan-terms n) post))
  :hints (("Goal"
           :use ((:instance tc-compact-post-plan-validp)
                 (:instance tc-compact-post-certificate-implies-matrix-certificate))
           :in-theory (enable wbc-plan-certifies-outputp))))

(defthm tc-compact-bank-certificate-implies-wbc-bank-certificate
  (implies (tc-compact-bank-certifies-aux count out n posts)
           (wbc-bank-certifies-aux
            count (nfix out) n (tc-plan-terms n) posts))
  :hints (("Goal"
           :induct (tc-compact-bank-certifies-aux count out n posts)
           :in-theory
           (e/d (tc-compact-bank-certifies-aux
                 wbc-bank-certifies-aux)
                (tc-compact-post-certifiesp
                 wbc-plan-certifies-outputp
                 tc-plan-terms)))))

(defthm tc-generated-compact-certificate-implies-plan-certificate
  (implies (tc-generated-compact-certifiesp n)
           (tc-generated-plan-certifiesp n))
  :hints (("Goal"
           :use ((:instance
                  tc-compact-bank-certificate-implies-wbc-bank-certificate
                  (count n) (out 0) (posts (tc-plan-posts n))))
           :in-theory (enable tc-generated-compact-certifiesp
                              tc-generated-plan-certifiesp))))

(defthm tc-compactly-certified-generated-plan-correct
  (implies (and (tc-generated-compact-certifiesp n)
                (qcx-vectorp n xs)
                (qcx-vectorp n ys))
           (equal (tc-run n xs ys)
                  (wbc-cyclic-convolution n xs ys)))
  :hints (("Goal"
           :use ((:instance
                  tc-generated-compact-certificate-implies-plan-certificate)
                 (:instance tc-generated-plan-correct))
           :in-theory nil)))
