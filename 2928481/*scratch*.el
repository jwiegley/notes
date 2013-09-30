(defun my-helm-apropos ()
  (interactive)
  (require 'helm-elisp)
  (require 'helm-misc)
  (let ((default (thing-at-point 'symbol)))
    (helm
     :prompt "Info about: "
     :candidate-number-limit 5
     :sources
     (append (mapcar (lambda (func)
                       (funcall func default))
                     '(helm-c-source-emacs-commands
                       helm-c-source-emacs-functions
                       helm-c-source-emacs-variables
                       helm-c-source-emacs-faces
                       helm-c-source-helm-attributes))
             '(helm-c-source-info-emacs
               helm-c-source-info-elisp
               helm-c-source-info-gnus
               helm-c-source-info-org
               helm-c-source-info-cl
               helm-c-source-emacs-source-defun)))))

(define-key lisp-find-map [?a] 'my-helm-apropos)
