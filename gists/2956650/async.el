(with-temp-buffer
           (prin1 (list 'quote ,start-func)
                  #'(lambda (ch)
                      (if (= ch ?\n)
                          (insert ? )
                        (insert ch))))
           (insert ?\n)
           (process-send-region ,procvar (point-min) (point-max))
           (process-send-eof ,procvar))