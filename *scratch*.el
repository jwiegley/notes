  (defun smart-hypen (next)
    (interactive (list (progn
                         (insert ?-)
                         (read-char))))
    (if (eq ?w (char-syntax next))
        (progn
          (delete-char -1)
          (insert (upcase next)))
      (insert next)))