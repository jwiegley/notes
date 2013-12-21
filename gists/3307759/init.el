    (eval-after-load "haskell-doc"
      '(defun haskell-doc-sym-doc (sym)
         (unless (string= "" sym)
           (let ((result (ignore-errors
                           (inferior-haskell-type sym))))
             (if (and result (string-match " :: " result))
                 result
               (setq result (inferior-haskell-kind sym))
               (and (string-match " :: " result) result))))))
