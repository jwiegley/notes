(defun batch-untabify ()
  ;; command-line-args-left is what is left of the command line (from startup.el)
  (defvar command-line-args-left)	;Avoid 'free variable' warning
  (if (not noninteractive)
      (error "`batch-untabify' is to be used only with -batch"))
  (while command-line-args-left
    (if (file-directory-p (expand-file-name (car command-line-args-left)))
        ;; Directory as argument.
        (let ((untabify-files (directory-files (car command-line-args-left)))
              untabify-source untabify-dest)
          (dolist (untabify-file untabify-files)
            (if (and (not (auto-save-file-name-p untabify-file))
                     (setq untabify-source
                           (expand-file-name untabify-file
                                             (car command-line-args-left))))
                (with-current-buffer (find-file untabify-source)
                  (untabify (point-min) (point-max))
                  (save-buffer)))))
      ;; Specific file argument
      (let ((untabify-source (car command-line-args-left)))
        (with-current-buffer (find-file untabify-source)
          (untabify (point-min) (point-max))
          (save-buffer))))
    (setq command-line-args-left (cdr command-line-args-left))))
