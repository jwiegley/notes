(use-package csharp-mode
  :mode "\\.cs$'"
  :preface
  (defun my-csharp-mode-hook ()
    (progn
      (add-to-list 'c-default-style '(csharp-mode . "C#"))
      (c-set-style "C#"))
    (omnisharp-mode)
    ;;(company-mode)
    )
  :hook (csharp-mode . my-csharp-mode-hook)
  :config
  (setq company-backend 'company-omnisharp))
