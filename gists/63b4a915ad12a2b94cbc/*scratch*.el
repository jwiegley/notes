(defun shuffle (xs)
  (if xs
      (if (zerop (random 2))
          (nconc (shuffle (cdr xs)) (list (car xs)))
        (cons (car xs) (shuffle (cdr xs))))))
