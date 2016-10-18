(defun sort-on (seq predicate accessor)
  "Sort SEQ use PREDICATE applied to values returned by ACCESSOR.
This implements the so-called Schwartzian transform, which has
the performance advantage of applying ACCESSOR at most once per
element in the list, as opposed to using `sort' with a PREDICATE
that applies the ACCESSOR."
  (mapcar #'cdr
          (sort (mapcar #'(lambda (x) (cons (funcall accessor x) x)) seq)
                #'(lambda (x y)
                    (funcall predicate (car x) (car y))))))
