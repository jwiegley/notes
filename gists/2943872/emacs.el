(eval-when-compile
  (require 'cl))

(require 'bind-key)
(require 'diminish)

(defvar use-package-verbose (not at-command-line))

(defmacro hook-into-modes (func modes)
  `(dolist (mode-hook ,modes)
     (add-hook mode-hook ,func)))

(defmacro with-elapsed-timer (text &rest forms)
  `(let ((now ,(if use-package-verbose
                   '(current-time))))
     ,(if use-package-verbose
          `(message "%s..." ,text))
     ,@forms
     ,(when use-package-verbose
        `(let ((elapsed
                (float-time (time-subtract (current-time) now))))
           (if (> elapsed 0.01)
               (message "%s...done (%.3fs)" ,text elapsed)
             (message "%s...done" ,text))))))

(put 'with-elapsed-timer 'lisp-indent-function 1)

(defmacro use-package (name &rest args)
  (let* ((commands (plist-get args :commands))
         (init-body (plist-get args :init))
         (config-body (plist-get args :config))
         (diminish-var (plist-get args :diminish))
         (defines (plist-get args :defines))
         (keybindings (plist-get args :bind))
         (predicate (plist-get args :if))
         (defines-eval (if (null defines)
                           nil
                         (if (listp defines)
                             (mapcar (lambda (var) `(defvar ,var)) defines)
                           `((defvar ,defines)))))
         (requires (plist-get args :requires))
         (requires-test (if (null requires)
                            t
                          (if (listp requires)
                              `(not (member nil (mapcar #'featurep
                                                        (quote ,requires))))
                            `(featurep (quote ,requires)))))
         (name-string (if (stringp name) name
                        (symbol-name name))))

    (if diminish-var
        (setq config-body
              `(progn
                 ,config-body
                 (ignore-errors
                   ,@(if (listp diminish-var)
                         (mapcar (lambda (var) `(diminish (quote ,var)))
                                 diminish-var)
                       `((diminish (quote ,diminish-var))))))))

    (when keybindings
      (if (and commands (symbolp commands))
          (setq commands (list commands)))
      (setq init-body
            `(progn
               ,init-body
               ,@(mapcar #'(lambda (binding)
                             (push (cdr binding) commands)
                             `(bind-key ,(car binding)
                                        (quote ,(cdr binding))))
                         (if (and (consp keybindings)
                                  (stringp (car keybindings)))
                             (list keybindings)
                           keybindings)))))

    (unless (plist-get args :disabled)
      `(progn
         (eval-when-compile
           ,@defines-eval
           ,(if (stringp name)
                `(load ,name t)
              `(require ',name nil t)))
         ,(if (or commands (plist-get args :defer))
              (let (form)
                (unless (listp commands)
                  (setq commands (list commands)))
                (mapc #'(lambda (command)
                          (push `(autoload (function ,command)
                                   ,name-string nil t) form))
                      commands)

                `(when ,(or predicate t)
                   ,@form
                   ,init-body
                   ,(unless (null config-body)
                      `(eval-after-load ,name-string
                         '(if ,requires-test
                              (with-elapsed-timer
                                  ,(format "Configuring package %s" name-string)
                                ,config-body))))
                   t))
            `(if (and ,(or predicate t)
                      ,requires-test)
                 (if ,(if (stringp name)
                          `(load ,name t)
                        `(require ',name nil t))
                     (with-elapsed-timer
                         ,(format "Loading package %s" name-string)
                       ,init-body
                       ,config-body
                       t)
                   (message "Could not load package %s" ,name-string))))))))

(put 'use-package 'lisp-indent-function 1)
