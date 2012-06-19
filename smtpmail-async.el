(require 'async)
(require 'smtpmail)

(defun async-smtpmail-send-it ()
  (async-start
   `(lambda ()
      (require 'smtpmail)

      (with-temp-buffer
        (insert ,(buffer-substring-no-properties (point-min)
                                                 (point-max)))

        ;; Pass in the variable environment for smtpmail
        (let (,@(let (bindings)
                  (mapatoms
                   (lambda (sym)
                     (if (and (boundp sym)
                              (string-match
                               "\\`\\(smtpmail\\|\\(user-\\)?mail\\)-"
                               (symbol-name sym))
                              (not (string-match
                                    "-syntax-table\\'"
                                    (symbol-name sym))))
                         (let ((value (symbol-value sym)))
                           (if (or (not (functionp value))
                                   (symbolp value))
                               (setq bindings
                                     (cons `(,sym (quote ,value))
                                           bindings)))))))
                  bindings))
          (smtpmail-send-it))))))
