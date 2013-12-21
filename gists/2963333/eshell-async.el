(defadvice eshell-exec-lisp (around async-eshell-exec-lisp
                                    (printer errprint func-or-form args form-p)
                                    activate)
  (if (symbolp func-or-form)
      (cond
       ((eq func-or-form 'copy-file)
        (dired-copy-file (nth 0 args) (nth 1 args) (nth 2 args)))
       ((eq func-or-form 'rename-file)
        (apply #'dired-rename-file args))
       ((eq func-or-form 'delete-file)
        (dired-delete-file (nth 0 args) nil (nth 1 args)))
       ((eq func-or-form 'delete-directory)
        (apply #'dired-delete-file args))
       (t
        ad-do-it))
    ad-do-it))
