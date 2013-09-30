(dolist (entry (directory-files-and-attributes
                (expand-file-name "elpa/" user-emacs-directory)))
  (if (cadr entry)
      (add-to-list 'load-path (expand-file-name (car entry) dir))))