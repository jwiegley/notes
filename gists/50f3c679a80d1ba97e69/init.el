;;;_ , Read system environment

(defun read-system-environment ()
  (let ((plist (expand-file-name "~/.MacOSX/environment.plist")))
    (when (file-readable-p plist)
      (let ((dict (cdr (assq 'dict (cdar (xml-parse-file plist))))))
        (while dict
          (if (and (listp (car dict))
                   (eq 'key (caar dict)))
              (setenv (car (cddr (car dict)))
                      (car (cddr (car (cddr dict))))))
          (setq dict (cdr dict))))

      ;; Configure exec-path based on the new PATH
      (setq exec-path nil)
      (mapc (apply-partially #'add-to-list 'exec-path)
            (nreverse (split-string (getenv "PATH") ":"))))))

(unless (string-match "/nix/store" (getenv "PATH"))
  (read-system-environment)
  (add-hook 'after-init-hook 'read-system-environment))
