; zby-text-file-census.lisp
; Compositional word scanning and READ-FILE-INTO-STRING census reports.

(in-package "ACL2")

(defun vfc-separatorp (ch)
  (or (equal ch #\Space)
      (equal ch #\Newline)
      (equal ch #\Tab)
      (equal ch #\Return)))

(defun vfc-word-char-p (ch)
  (and (characterp ch)
       (not (vfc-separatorp ch))))

(defun vfc-word-count-from (chars in-word-p)
  (if (endp chars)
      0
    (let ((wordp (vfc-word-char-p (car chars))))
      (+ (if (and wordp (not in-word-p)) 1 0)
         (vfc-word-count-from (cdr chars) wordp)))))

(defun vfc-final-in-word (chars in-word-p)
  (if (endp chars)
      (if in-word-p t nil)
    (vfc-final-in-word (cdr chars)
                       (vfc-word-char-p (car chars)))))

; Result = (new-word-count final-in-word-p).
(defun vfc-word-scan (chars in-word-p)
  (list (vfc-word-count-from chars in-word-p)
        (vfc-final-in-word chars in-word-p)))

(defun vfc-line-count (chars)
  (if (endp chars)
      0
    (+ (if (equal (car chars) #\Newline) 1 0)
       (vfc-line-count (cdr chars)))))

(defun vfc-census (chars)
  (let ((scan (vfc-word-scan chars nil)))
    (list (len chars)
          (vfc-line-count chars)
          (nfix (car scan))
          (cadr scan))))

(defthm vfc-final-in-word-of-append
  (equal (vfc-final-in-word (append left right) in-word-p)
         (vfc-final-in-word
          right
          (vfc-final-in-word left in-word-p)))
  :hints (("Goal" :induct (vfc-final-in-word left in-word-p)
           :in-theory (enable vfc-final-in-word))))

(defthm vfc-word-count-from-of-append
  (equal
   (vfc-word-count-from (append left right) in-word-p)
   (+ (vfc-word-count-from left in-word-p)
      (vfc-word-count-from
       right
       (vfc-final-in-word left in-word-p))))
  :hints (("Goal" :induct (vfc-word-count-from left in-word-p)
           :in-theory (enable vfc-word-count-from
                              vfc-final-in-word))))

(defthm vfc-word-scan-of-append
  (equal
   (vfc-word-scan (append left right) in-word-p)
   (let* ((left-scan (vfc-word-scan left in-word-p))
          (right-scan (vfc-word-scan right (cadr left-scan))))
     (list (+ (car left-scan) (car right-scan))
           (cadr right-scan))))
  :hints (("Goal"
           :use ((:instance vfc-final-in-word-of-append)
                 (:instance vfc-word-count-from-of-append))
           :in-theory (enable vfc-word-scan))))

(defthm vfc-line-count-of-append
  (equal (vfc-line-count (append left right))
         (+ (vfc-line-count left)
            (vfc-line-count right)))
  :hints (("Goal" :induct (len left)
           :in-theory (enable vfc-line-count))))

(defthm vfc-census-character-count
  (equal (nth 0 (vfc-census chars))
         (len chars))
  :hints (("Goal" :in-theory (enable vfc-census))))

(defthm vfc-census-line-count
  (equal (nth 1 (vfc-census chars))
         (vfc-line-count chars))
  :hints (("Goal" :in-theory (enable vfc-census))))

(defun vfc-write-report (filename source-name chars state)
  (declare (xargs :stobjs state :verify-guards nil))
  (mv-let (channel state)
    (open-output-channel filename :character state)
    (if (not channel)
        (mv :open-failed state)
      (let ((census (vfc-census chars)))
        (mv-let (col state)
          (fmt1 "Text census for ~x0~%~%Characters: ~x1~%Newlines:   ~x2~%Words:      ~x3~%Ends in word: ~x4~%"
                (list (cons #\0 source-name)
                      (cons #\1 (nth 0 census))
                      (cons #\2 (nth 1 census))
                      (cons #\3 (nth 2 census))
                      (cons #\4 (nth 3 census)))
                0 channel state nil)
          (declare (ignore col))
          (let ((state (close-output-channel channel state)))
            (mv nil state)))))))

(defun vfc-audit-file (input-filename report-filename state)
  (declare (xargs :stobjs state :mode :program))
  (let ((text (read-file-into-string input-filename :close t)))
    (if (not (stringp text))
        (mv :read-failed state)
      (vfc-write-report report-filename
                        input-filename
                        (coerce text 'list)
                        state))))

(defconst *vfc-demo*
  (list #\a #\b #\Space #\c #\Newline #\d #\e #\f))

(assert-event
 (and (equal (vfc-word-scan *vfc-demo* nil) '(3 t))
      (equal (vfc-line-count *vfc-demo*) 1)
      (equal (vfc-census *vfc-demo*) '(8 1 3 t))))
