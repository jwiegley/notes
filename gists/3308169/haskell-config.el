    (eval-after-load "haskell-doc"
      '(defun haskell-doc-sym-doc (sym)
         "If no type information is available, try to get the kind."
         (unless (string= "" sym)
           (let* ((message-log-max nil)
                  (result (ignore-errors
                            (unwind-protect
                                (inferior-haskell-type sym)
                              (message "")))))
             (if (and result (string-match " :: " result))
                 result
               (setq result (unwind-protect
                                (inferior-haskell-kind sym)
                              (message "")))
               (and result (string-match " :: " result) result))))))
