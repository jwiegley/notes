(defun smart-hyphen (n)
    "Capitalize the next word, or behave as the usual '-'."
    (interactive "p")
    (if (memq (get-text-property (point) 'face)
              '(font-lock-doc-face
                font-lock-comment-face
                font-lock-string-face))
        (self-insert-command n)
      (insert ?-)
      (insert (let ((next (read-char)))
                (if (eq ?w (char-syntax next))
                    (progn
                      (delete-char -1)
                      (upcase next))
                  next)))))