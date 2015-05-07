(defun rev2 (x)
  (if (endp x)
      nil
      (append (rev2 (cdr x)) (list (car x)))))

(defun dupsp (x)  ; does x contain duplicate elements?
  (if (endp x)
      nil
      (if (member (car x) (cdr x))
          t
          (dupsp (cdr x)))))

(defthm member-rev
  (iff (member x (rev2 y))
       (member x y)))

(defthm dupsp-append
  (iff (dupsp (append y (list x)))
       (if (member x y)
           (dupsp (cons x y))
           (dupsp y))))

(defthm dupsp-rev
  (equal (dupsp (rev2 x)) (dupsp x)))

(defun collect-once (x)
  (if (endp x)
      nil
      (let ((rest (collect-once (cdr x))))
        (if (member (car x) rest)
            rest
            (cons (car x) rest)))))

(defthm collect-once-member
  (iff (member x (collect-once y))
       (member x y)))

(defthm main-theorem-1-about-collect-once
  (subsetp (collect-once x) x))

(defthm main-theorem-2-about-collect-once
  (not (dupsp (collect-once x))))

(defun while-loop-version (x acc)
  (if (endp x)
      acc
      (while-loop-version
        (cdr x)
        (if (member (car x) acc)
            acc
            (cons (car x) acc)))))

(defun remove-elem (x xs)
  (if (endp xs)
      nil
      (if (equal x (car xs))
          (cdr xs)
          (cons (car xs) (remove-elem x (cdr xs))))))

(defun list-minus (x y)
  (if (endp x)
      nil
      (if (member (car x) y)
          (list-minus (cdr x) y)
          (cons (car x) (list-minus (cdr x) y)))))

(defthm list-minus-append
  (equal (list-minus (append x y) z)
         (append (list-minus x z) 
                 (list-minus y z))))

;; Having this rewrite rule makes the goal impossible
; (defthm list-minus-rev
;   (equal (list-minus (rev2 x) y) 
;          (rev2 (list-minus x y))))

(defthm collect-once-append
  (equal (collect-once (append x y))
         (append (list-minus (collect-once x) y)
                 (collect-once y))))

(defthm list-minus-member
  (iff (member x (list-minus y z))
       (and (member x y)
            (not (member x z)))))

(defthm list-minus-collect-once
  (equal (list-minus (collect-once x) y)
         (collect-once (list-minus x y))))

(defthm lift-minus-twice
  (equal (list-minus (list-minus x y) z)
         (list-minus x (append y z))))

(defthm while-loop-collect-once
  (equal (while-loop-version x a)
         (append (collect-once (list-minus (rev2 x) a)) a)))
