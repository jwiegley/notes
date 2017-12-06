(use-package shackle
  :demand t
  :load-path "site-lisp/shackle"
  :config
  (setq shackle-rules
        '((compilation-mode :select t :align t :size 0.9)
          ("\\` \\*Lusty-Matches\\*" :regexp t :noselect t))
        shackle-default-rule '(:select t))
  (shackle-mode 1))
