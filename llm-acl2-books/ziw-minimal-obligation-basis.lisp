; ziw-minimal-obligation-basis.lisp
; Exact reduction of finite subset-ordered obligations to a minimal basis.

(in-package "ACL2")


(defun vob-weakerp (left right)
  (if (endp left)
      t
    (and (member-equal (car left) right)
         (vob-weakerp (cdr left) right))))

(defun vob-satisfiedp (query basis)
  (if (endp basis) nil
    (or (vob-weakerp (car basis) query)
        (vob-satisfiedp query (cdr basis)))))

(defun vob-trim (new basis)
  (if (endp basis) nil
    (if (vob-weakerp new (car basis))
        (vob-trim new (cdr basis))
      (cons (car basis) (vob-trim new (cdr basis))))))

(defun vob-add (new basis)
  (if (vob-satisfiedp new basis) basis
    (cons new (vob-trim new basis))))

(defun vob-basis (obligations)
  (if (endp obligations) nil
    (vob-add (car obligations) (vob-basis (cdr obligations)))))

(defun vob-naive-satisfiedp (query obligations)
  (if (endp obligations) nil
    (or (vob-weakerp (car obligations) query)
        (vob-naive-satisfiedp query (cdr obligations)))))

(defthm vob-weakerp-of-cons-right
  (implies (vob-weakerp x y)
           (vob-weakerp x (cons a y)))
  :hints (("Goal" :induct (len x)
           :in-theory (enable vob-weakerp))))

(defthm vob-weakerp-reflexive
  (vob-weakerp x x)
  :hints (("Goal" :induct (len x)
           :in-theory (enable vob-weakerp))))

(defthm vob-member-when-weaker
  (implies (and (vob-weakerp x y)
                (member-equal a x))
           (member-equal a y))
  :hints (("Goal" :induct (len x)
           :in-theory (enable vob-weakerp))))

(defthm vob-weakerp-transitive
  (implies (and (vob-weakerp x y) (vob-weakerp y z))
           (vob-weakerp x z))
  :hints (("Goal" :induct (len x)
           :in-theory (enable vob-weakerp))))

(defthm vob-satisfiedp-by-member
  (implies (member-equal x basis) (vob-satisfiedp x basis))
  :hints (("Goal" :induct (vob-satisfiedp x basis)
           :in-theory (enable vob-satisfiedp))))

(defthm vob-satisfiedp-monotone-query
  (implies (and (vob-satisfiedp small basis)
                (vob-weakerp small large))
           (vob-satisfiedp large basis))
  :hints (("Goal" :induct (vob-satisfiedp small basis)
           :in-theory (enable vob-satisfiedp))))

(defthm vob-satisfiedp-of-trim-implies-old
  (implies (vob-satisfiedp query (vob-trim new basis))
           (vob-satisfiedp query basis))
  :hints (("Goal" :induct (vob-trim new basis)
           :in-theory (enable vob-trim vob-satisfiedp))))

(defthm vob-old-satisfaction-survives-trim-or-new
  (implies (vob-satisfiedp query basis)
           (or (vob-satisfiedp query (vob-trim new basis))
               (vob-weakerp new query)))
  :hints (("Goal" :induct (vob-trim new basis)
           :in-theory (enable vob-trim vob-satisfiedp))))

(defthm vob-satisfiedp-of-add
  (equal (vob-satisfiedp query (vob-add new basis))
         (or (vob-weakerp new query) (vob-satisfiedp query basis)))
  :hints (("Goal"
           :cases ((vob-satisfiedp new basis))
           :use ((:instance vob-satisfiedp-monotone-query
                            (small new) (large query))
                 (:instance vob-satisfiedp-of-trim-implies-old)
                 (:instance vob-old-satisfaction-survives-trim-or-new))
           :in-theory (enable vob-add vob-satisfiedp))))

(defthm vob-basis-preserves-all-queries
  (equal (vob-satisfiedp query (vob-basis obligations))
         (vob-naive-satisfiedp query obligations))
  :hints (("Goal" :induct (vob-basis obligations)
           :in-theory (enable vob-basis vob-naive-satisfiedp))))

(defun vob-reducedp (basis)
  (if (endp basis) t
    (and (not (vob-satisfiedp (car basis) (cdr basis)))
         (vob-reducedp (cdr basis)))))

(defthm vob-trim-leaves-new-unsatisfied
  (implies (not (vob-satisfiedp new basis))
           (not (vob-satisfiedp new (vob-trim new basis))))
  :hints (("Goal" :induct (vob-trim new basis)
           :in-theory (enable vob-trim vob-satisfiedp))))

(defthm vob-reducedp-of-trim
  (implies (vob-reducedp basis)
           (vob-reducedp (vob-trim new basis)))
  :hints (("Goal" :induct (vob-trim new basis)
           :in-theory (enable vob-trim vob-reducedp))))

(defthm vob-basis-is-reduced
  (vob-reducedp (vob-basis obligations))
  :hints (("Goal" :induct (vob-basis obligations)
           :in-theory (enable vob-basis vob-add vob-reducedp))))

(defconst *vob-demo* '((a b c) (a) (a b) (d e) (d e f)))

(assert-event
 (and (vob-satisfiedp '(a z) (vob-basis *vob-demo*))
      (vob-satisfiedp '(d e q) (vob-basis *vob-demo*))
      (vob-reducedp (vob-basis *vob-demo*))))

