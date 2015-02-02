    (push '(ruby-arrow
            (regexp   . "\\(\\s-*\\)=>\\(\\s-*\\)")
            (group    . (1 2))
            (modes    . '(ruby-mode puppet-mode)))
          align-rules-list)

    (defvar puppet-anchor-point nil)

    (defun puppet-set-anchor ()
      (interactive)
      (setq puppet-anchor-point (point-marker))
      (message "puppet-mode anchor set at %s"
               (marker-position puppet-anchor-point)))

    (defun puppet-create-require ()
      (interactive)
      (if (null puppet-anchor-point)
          (error "Anchor point has not been set")
        (destructuring-bind (resource . name)
            (save-excursion
              (goto-char puppet-anchor-point)
              (and (re-search-backward
                    "^\\s-*\\(\\S-+\\)\\s-+{\\s-+\\([^:]+\\):" nil t)
                   (cons (match-string 1) (match-string 2))))
          (save-excursion
            (let ((current-requires
                   (when (re-search-forward "^\\s-*require\\s-*=>\\s-*" nil t)
                     (let ((start (match-beginning 0))
                           (beg (match-end 0)))
                       (if (looking-at "\\[")
                           (forward-sexp))
                       (re-search-forward "[,;][ \t]*\n")
                       (prog1
                           (buffer-substring-no-properties
                            beg (match-beginning 0))
                         (delete-region start (point)))))))
              (re-search-forward "^}")
              (goto-char (match-beginning 0))
              (save-excursion
                (skip-chars-backward " \t\n\r")
                (when (looking-back ";")
                  (delete-backward-char 1)
                  (insert ?,)))
              (insert "  require => ")
              (if current-requires
                  (insert "[ " current-requires ", "))
              (insert (capitalize resource) "[" name "]")
              (if current-requires
                  (insert " ]"))
              (insert ";\n")
              (mark-paragraph)
              (align-code (region-beginning) (region-end)))))))

    (define-key puppet-mode-map [(control ?x) ? ] 'puppet-set-anchor)
    (define-key puppet-mode-map [(control ?x) space] 'puppet-set-anchor)
    (define-key puppet-mode-map [(control ?c) (control ?r)] 'puppet-create-require)
