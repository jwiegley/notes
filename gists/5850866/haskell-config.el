(defun my-inferior-haskell-break (&optional arg)
  (interactive "P")
  (let ((line (line-number-at-pos))
        (col (if arg
                 ""
               (format " %d" (current-column))))
        (proc (inferior-haskell-process)))
    (inferior-haskell-send-command
     proc (format ":break %d%s" line col))
    (message "Breakpoint set at %s:%d%s"
             (file-name-nondirectory (buffer-file-name)) line col)))