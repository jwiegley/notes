(defun smart-hyphen (arg)
    "Insert a hyphen or capitalize the next word."
    (interactive "p")
    (if (memq (get-text-property (point) 'face)
              '(font-lock-doc-face
                font-lock-comment-face
                font-lock-string-face))
        (call-interactively 'self-insert-command)
      (let ((next (progn
                    (insert ?-)
                    (read-char))))
        (if (eq ?w (char-syntax next))
            (progn
              (delete-char -1)
              (insert (upcase next)))
          (insert next)))))