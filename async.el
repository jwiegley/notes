(defun async--fold-left (f z xs)
  (let ((res z))
    (dolist (x xs)
      (setq res (funcall f res x)))
    res))

(defmacro async-let (bindings forms)
  (async--fold-left
   (lambda (acc binding)
     `(async-start ,(cadr binding)
                   (lambda (,(car binding))
                     ,acc)))
   forms (reverse bindings)))

(async-let ((x (foo))
            (y (bar)))
   (message "%s %s" x y))

;; ==>

;; (async-start (foo)
;;  (lambda (x)
;;    (async-start (bar)
;;     (lambda (y)
;;       (message "%s %s" x y)))))
