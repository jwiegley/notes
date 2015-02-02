(defun fix (f)
  (apply-partially f f))

(funcall (fix (lambda (f x) (funcall (fix f) x))) 10)