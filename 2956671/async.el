(with-temp-buffer
           (let ((print-escape-newlines t))
             (prin1 (list 'quote ,start-func) (current-buffer)))
           (insert ?\n)
           (process-send-region ,procvar (point-min) (point-max))
           (process-send-eof ,procvar))