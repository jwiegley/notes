  (defun smart-hyphen ()
    "Capitalize the next word, or behave as the usual '-'."
    (interactive)
    (if (memq (get-text-property (point) 'face)
              '(font-lock-doc-face
                font-lock-comment-face
                font-lock-string-face))
        (call-interactively 'self-insert-command)
      (insert ?- (let ((next (read-char)))
                   (if (eq ?w (char-syntax next))
                       (progn
                         (delete-char -1)
                         (upcase next))
                     next)))))