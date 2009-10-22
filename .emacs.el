(defun org-indent-empty-items (arg)
  (when (eq arg 'empty)
    (goto-char (line-end-position))
    (cond
     ((org-at-item-p) (org-indent-item 1))
     ((org-on-heading-p)
      (if (equal this-command last-command)
          (condition-case nil
              (org-promote-subtree)
            (error
             (save-excursion
               (goto-char (point-at-bol))
               (and (looking-at "\\*+") (replace-match ""))
               (org-insert-heading)
               (org-demote-subtree))))
        (org-demote-subtree))))))

(add-hook 'org-pre-cycle-hook 'org-indent-empty-items)
