(use-package compile
  :defer t
  :config
  (use-package alert)
  (eval-when-compile
    (defvar exit-status))
  (add-hook 'compilation-finish-functions
            (lambda (buf why)
              (display-buffer buf)
              (if (> exit-status 0)
                  (alert "Compilation finished with errors"
                         :buffer buf :severity 'high)
                (alert "Compilation finished" :buffer buf)))))