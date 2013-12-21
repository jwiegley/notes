    (eval-after-load "haskell-doc"
      '(defun haskell-doc-show-type (&optional sym)
         (interactive)
         (unless sym (setq sym (haskell-ident-at-point)))
         ;; if printed before do not print it again
         (message (inferior-haskell-type sym))))
