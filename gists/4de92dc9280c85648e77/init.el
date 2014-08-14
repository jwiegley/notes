(use-package proof-site
  :load-path (lambda () (nix-lisp-path "ProofGeneral/generic"))
  :config
  (progn
    (use-package coq
      :mode ("\\.v\\'" . coq-mode)
      :load-path (lambda () (nix-lisp-path "ProofGeneral/coq"))
      :config
      (progn
        (add-hook 'coq-mode-hook
                  (lambda ()
                    (yas-minor-mode 1)
                    (whitespace-mode 1)
                    (set-input-method "Agda")
                    (defalias 'proof-display-and-keep-buffer
                      'my-proof-display-and-keep-buffer)))
        (bind-key "M-RET" 'proof-goto-point coq-mode-map)
        (bind-key "<tab>" 'yas-expand-from-trigger-key coq-mode-map)
        (bind-key "C-c C-p" (lambda ()
                              (interactive)
                              (proof-layout-windows)
                              (proof-prf)) coq-mode-map)))))