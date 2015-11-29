;;;###autoload
(defmacro define-urweb-mode (base-mode)
  `(define-derived-mode urweb-mode ,(eval base-mode) "Ur/Web"
    "\\<urweb-mode-map>Major mode for editing Ur/Web code.
This mode runs `urweb-mode-hook' just before exiting.
\\{urweb-mode-map}"
    (set (make-local-variable 'font-lock-defaults) urweb-font-lock-defaults)
    (set (make-local-variable 'font-lock-multiline) 'undecided)
    (set (make-local-variable 'outline-regexp) urweb-outline-regexp)
    (set (make-local-variable 'imenu-create-index-function)
         'urweb-imenu-create-index)
    (set (make-local-variable 'add-log-current-defun-function)
         'urweb-current-fun-name)
    ;; Treat paragraph-separators in comments as paragraph-separators.
    (set (make-local-variable 'paragraph-separate)
         (concat "\\([ \t]*\\*)?\\)?\\(" paragraph-separate "\\)"))
    (set (make-local-variable 'require-final-newline) t)
    ;; forward-sexp-function is an experimental variable in my hacked Emacs.
    (set (make-local-variable 'forward-sexp-function) 'urweb-user-forward-sexp)
    ;; For XEmacs
    (easy-menu-add urweb-mode-menu)

    ;; Compatibility.  FIXME: we should use `-' in Emacs-CVS.
    (unless (boundp 'skeleton-positions) (set (make-local-variable '@) nil))

    (local-set-key (kbd "C-c C-c") 'compile)
    (local-set-key (kbd "C-c /") 'urweb-close-matching-tag)

    (urweb-mode-variables)))

(define-urweb-mode (if (fboundp 'prog-mode)
                       'prog-mode
                     'fundamental-mode))
