(defun smart-hyphen (n)
    "Insert a hyphen or capitalize the next word."
    (interactive "p")
    (if (memq (get-text-property (point) 'face)
              '(font-lock-doc-face
                font-lock-comment-face
                font-lock-string-face))
        (self-insert-command n)
      (let ((next (progn
                    (insert ?-)
                    (read-char))))
        (if (eq ?w (char-syntax next))
            (progn
              (delete-char -1)
              (insert (upcase next)))
          (insert next)))))