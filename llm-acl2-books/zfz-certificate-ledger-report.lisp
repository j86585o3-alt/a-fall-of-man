; zfz-certificate-ledger-report.lisp
; Parallelizable certificate-ledger summaries and an ACL2 FMT1 file report.

(in-package "ACL2")

(defun vlr-recordp (x)
  (and (true-listp x)
       (equal (len x) 3)
       (symbolp (car x))
       (or (equal (cadr x) :pass)
           (equal (cadr x) :fail))
       (natp (caddr x))))

(defun vlr-ledgerp (xs)
  (if (endp xs) t
    (and (vlr-recordp (car xs))
         (vlr-ledgerp (cdr xs)))))

; Summary = (total passes failures total-steps).
(defun vlr-zero-summary () '(0 0 0 0))
(defun vlr-combine (a b)
  (list (+ (nth 0 a) (nth 0 b))
        (+ (nth 1 a) (nth 1 b))
        (+ (nth 2 a) (nth 2 b))
        (+ (nth 3 a) (nth 3 b))))

(defun vlr-record-summary (record)
  (let ((passp (equal (cadr record) :pass))
        (steps (nfix (caddr record))))
    (list 1 (if passp 1 0) (if passp 0 1) steps)))

(defun vlr-summary (ledger)
  (if (endp ledger)
      (vlr-zero-summary)
    (vlr-combine (vlr-record-summary (car ledger))
                 (vlr-summary (cdr ledger)))))

(defthm vlr-combine-associative
  (equal (vlr-combine (vlr-combine a b) c)
         (vlr-combine a (vlr-combine b c)))
  :hints (("Goal" :in-theory (enable vlr-combine associativity-of-+))))

(defthm vlr-summary-shape
  (equal (list (nth 0 (vlr-summary ledger))
               (nth 1 (vlr-summary ledger))
               (nth 2 (vlr-summary ledger))
               (nth 3 (vlr-summary ledger)))
         (vlr-summary ledger))
  :hints (("Goal" :induct (vlr-summary ledger)
           :in-theory (enable vlr-summary vlr-combine vlr-zero-summary))))

(defthm vlr-combine-zero-summary-left
  (equal (vlr-combine (vlr-zero-summary) (vlr-summary ledger))
         (vlr-summary ledger))
  :hints (("Goal"
           :use ((:instance vlr-summary-shape))
           :in-theory (enable vlr-combine vlr-zero-summary))))

(defthm vlr-summary-of-append
  (equal (vlr-summary (append left right))
         (vlr-combine (vlr-summary left)
                      (vlr-summary right)))
  :hints (("Goal" :induct (len left)
           :in-theory (e/d (vlr-summary) (vlr-combine)))
          ("Subgoal *1/2"
           :use ((:instance vlr-combine-zero-summary-left
                            (ledger right)))
           :in-theory (disable vlr-combine
                               vlr-combine-zero-summary-left))))

(defthm vlr-total-is-pass-plus-fail
  (implies (vlr-ledgerp ledger)
           (equal (nth 0 (vlr-summary ledger))
                  (+ (nth 1 (vlr-summary ledger))
                     (nth 2 (vlr-summary ledger)))))
  :hints (("Goal" :induct (vlr-summary ledger)
           :in-theory (enable vlr-summary vlr-ledgerp
                              vlr-record-summary vlr-combine))))

(defthm vlr-summary-counts-records
  (implies (vlr-ledgerp ledger)
           (equal (nth 0 (vlr-summary ledger))
                  (len ledger)))
  :hints (("Goal" :induct (vlr-summary ledger)
           :in-theory (e/d (vlr-summary vlr-ledgerp
                                      vlr-record-summary vlr-combine)
                                     (vlr-total-is-pass-plus-fail)))))

(defun vlr-write-rows (ledger col channel state)
  (declare (xargs :stobjs state :verify-guards nil))
  (if (endp ledger)
      (mv col state)
    (mv-let (col state)
      (fmt1 "~S0~t1~S2~t3~c4~%"
            (list (cons #\0 (car (car ledger)))
                  (cons #\1 28)
                  (cons #\2 (cadr (car ledger)))
                  (cons #\3 40)
                  (cons #\4 (cons (caddr (car ledger)) 12)))
            col channel state nil)
      (vlr-write-rows (cdr ledger) col channel state))))

(defun vlr-write-report (filename ledger state)
  (declare (xargs :stobjs state :verify-guards nil))
  (mv-let (channel state)
    (open-output-channel filename :character state)
    (if (not channel)
        (mv :open-failed state)
      (mv-let (col state)
        (fmt1 "ACL2 certificate ledger~%~%Book~t0Status~t1Steps~%"
              (list (cons #\0 28) (cons #\1 40))
              0 channel state nil)
        (mv-let (col state)
          (vlr-write-rows ledger col channel state)
          (declare (ignore col))
          (let ((summary (vlr-summary ledger)))
            (mv-let (col state)
              (fmt1 "~%Total ~x0; passed ~x1; failed ~x2; steps ~x3.~%"
                    (list (cons #\0 (nth 0 summary))
                          (cons #\1 (nth 1 summary))
                          (cons #\2 (nth 2 summary))
                          (cons #\3 (nth 3 summary)))
                    0 channel state nil)
              (declare (ignore col))
              (let ((state (close-output-channel channel state)))
                (mv nil state)))))))))

(defconst *vlr-demo*
  '((alpha :pass 120)
    (beta :fail 75)
    (gamma :pass 305)))

(assert-event
 (equal (vlr-summary *vlr-demo*)
        '(3 2 1 500)))
