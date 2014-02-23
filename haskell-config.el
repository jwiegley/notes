(defun insert-counting-putStrLn (arg)
  (interactive "P")
  (if arg
      (setq put-index 0
            put-prefix (read-string "Prefix: ")))
  ;; (insert (format "trace (\"%s %d..\") $ return ()\n"
  ;;                 put-prefix
  ;;                 (setq put-index (1+ put-index))))
  ;; (insert (format "liftIO $ putStrLn $ \"%s %d..\"\n"
  ;;                 put-prefix
  ;;                 (setq put-index (1+ put-index))))
  (insert (format "liftIO $ putStrLn $ \"%s %s:%d..\"\n"
                  put-prefix
                  (file-name-nondirectory (buffer-file-name))
                  (1+ (count-lines (point-min) (point)))))
  (forward-line -1)
  (goto-char (line-beginning-position))
  (if (save-excursion (re-search-backward "^\\( +\\)liftIO \\$ putStrLn" nil t))
      (let ((leader (match-string 1)))
        (insert leader))
    (indent-according-to-mode))
  (forward-line))