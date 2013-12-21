(require 'async)
(require 'smtpmail)

(defun async-smtpmail-send-it ()
  (async-start
   `(lambda ()
      (require 'smtpmail)
      (with-temp-buffer
        (insert ,(buffer-substring-no-properties (point-min) (point-max)))
        ;; Pass in the variable environment for smtpmail
        (async-inject-environment "\\`\\(smtpmail\\|\\(user-\\)?mail\\)-")
        (smtpmail-send-it)))))
