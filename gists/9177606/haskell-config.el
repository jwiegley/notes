(defun debug-string (put-prefix)
  (format "liftIO $ putStrLn $ \"%s %s:%d..\""
          put-prefix
          (file-name-nondirectory (buffer-file-name))
          (1+ (line-number-at-pos))))

(defun adjust-counting-putStrLn (&rest ignore)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "liftIO \\$ putStrLn \\$ \"\\([^ ]+\\) .+?:[0-9]+\\.\\.\"" nil t)
      (let ((fun (match-string 1)))
        (replace-match (debug-string fun))))))

(defun insert-counting-putStrLn (arg)
  (interactive "P")
  (if arg
      (setq put-index 0
            put-prefix (read-string "Prefix: ")))
  (insert (debug-string put-prefix) ?\n)
  (forward-line -1)
  (goto-char (line-beginning-position))
  (if (save-excursion (re-search-backward "^\\( +\\)liftIO \\$ putStrLn" nil t))
      (let ((leader (match-string 1)))
        (insert leader))
    (indent-according-to-mode))
  (forward-line))
