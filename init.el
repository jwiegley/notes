  (defun my-brittanize ()
    (interactive)
    (save-restriction
      (save-excursion
        (let ((buf (buffer-string)))
          (unless (= 0 (call-process-region (point-min) (point-max)
                                            "brittany" t t nil "--indent=2"))
            (delete-region (point-min) (point-max))
            (insert buf)
            (set-buffer-modified-p nil))))))

  (defun my-haskell-mode-hook ()
    (haskell-indentation-mode)
    (setq-local normalize-hook '(my-brittanize))
    (add-hook 'write-contents-hooks
              #'(lambda () (ignore (whitespace-cleanup))) nil t)
    (whitespace-cleanup)
    (interactive-haskell-mode)
    (diminish 'interactive-haskell-mode)
    (flycheck-mode 1)
    (flycheck-haskell-setup)
    (setq-local prettify-symbols-alist haskell-prettify-symbols-alist)
    (prettify-symbols-mode 1)
    (bug-reference-prog-mode 1))