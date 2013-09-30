    (defun my-haskell-hoogle (type)
      (interactive
       (let ((type (haskell-doc-sym-doc (haskell-ident-at-point))))
         (when type
           (setq type (replace-regexp-in-string ".* :: " "" type)))
         (list (read-string (if (and type (> (length type) 0))
                                (format "Hoogle (default %s): " type)
                              "Hoogle: ")
                            nil nil type))))
      (shell-command (concat "hoogle " (shell-quote-argument type))))
