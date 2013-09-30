This:

(use-package abbrev
  :commands abbrev-mode
  :diminish abbrev-mode
  :init
  (hook-into-modes #'abbrev-mode '(text-mode-hook))

  :config
  (progn
   (if (file-exists-p abbrev-file-name)
       (quietly-read-abbrev-file))

   (add-hook 'expand-load-hook
             (lambda ()
               (add-hook 'expand-expand-hook 'indent-according-to-mode)
               (add-hook 'expand-jump-hook 'indent-according-to-mode)))))

Becomes:

(progn
  (when byte-compile-current-file
    (require 'abbrev nil t))
  nil
  (when t nil
        (autoload
          (function abbrev-mode)
          "abbrev" nil t)
        (hook-into-modes
         (function abbrev-mode)
         '(text-mode-hook))
        (eval-after-load "abbrev"
          '(if t
               (with-elapsed-timer "Configuring package abbrev"
                 (progn
                   (progn
                     (if
                         (file-exists-p abbrev-file-name)
                         (quietly-read-abbrev-file))
                     (add-hook 'expand-load-hook
                               (lambda nil
                                 (add-hook 'expand-expand-hook 'indent-according-to-mode)
                                 (add-hook 'expand-jump-hook 'indent-according-to-mode))))
                   (ignore-errors
                     (diminish 'abbrev-mode))))))
        t))