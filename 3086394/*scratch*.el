;; I had this form:

(with-temp-buffer
  (insert-file-contents temp-file2)
  (should (equal "async-copy-file-lisp-1" (buffer-string))))

;; Place cursor on "(equal", and call `paredit-convolute-sexp':

(should (with-temp-buffer
          (insert-file-contents temp-file2)
          (equal "async-copy-file-lisp-1" (buffer-string))))

;; Now place cursor on "(buffer-string", and call it once more:

(should (equal "async-copy-file-lisp-1"
               (with-temp-buffer
                 (insert-file-contents temp-file2)
                 (buffer-string))))

;; This was the form I meant to write!