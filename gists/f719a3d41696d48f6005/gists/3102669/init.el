    (defun puppet-resource-beginning ()
      (save-excursion
        (and (re-search-backward
              "^\\s-*\\(\\S-+\\)\\s-+{\\s-+\\([^:]+\\):" nil t)
             (list (match-beginning 0)
                   (match-string 1) (match-string 2)))))

    (defun puppet-resource-end ()
      (save-excursion
        (and (re-search-forward "^\\s-*}" nil t)
             (match-end 0))))

    (defun puppet-create-require ()
      (interactive)
      (require 'align)
      (if (null puppet-anchor-point)
          (error "Anchor point has not been set")
        (destructuring-bind (anchored-start resource name)
            (save-excursion
              (goto-char puppet-anchor-point)
              (puppet-resource-beginning))
          (save-excursion
            (let ((beginning (car (puppet-resource-beginning)))
                  (end (puppet-resource-end)))
              (goto-char end)
              (backward-char)
              (let ((current-requires
                     (when (re-search-backward
                            "^\\s-*require\\s-*=>\\s-*" beginning t)
                       (let ((start (match-beginning 0))
                             (beg (match-end 0)))
                         (if (looking-at "\\[")
                             (forward-sexp))
                         (re-search-forward "\\([,;]\\)?[ \t]*\n")
                         (prog1
                             (buffer-substring-no-properties
                              beg (match-beginning 0))
                           (delete-region start (point)))))))
                (save-excursion
                  (skip-chars-backward " \t\n\r")
                  (when (looking-back ";")
                    (delete-backward-char 1)
                    (insert ?,)))
                (insert "  require => ")
                (if current-requires
                    (insert "[ " current-requires ", "))
                (insert (capitalize (substring resource 0 1))
                        (substring resource 1) "[" name "]")
                (if current-requires
                    (insert " ]"))
                (insert ";\n")
                (mark-paragraph)
                (align-code (region-beginning) (region-end))))))))