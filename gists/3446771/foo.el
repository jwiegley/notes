(defun fix (f)
  `(lambda (&rest args)
     (apply ,f (fix ,f) args)))

(funcall (fix (lambda (f x) (funcall f x))) 10)
