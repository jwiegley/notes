(use-package direnv
  :demand t
  :config
  (direnv-mode)
  (eval-after-load 'flycheck
    '(setq flycheck-executable-find
           (lambda (cmd)
             (direnv-update-environment default-directory)
             (executable-find cmd))))
  :hook
  (coq-mode . direnv-update-environment))
