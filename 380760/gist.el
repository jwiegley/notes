(defun gist-region (begin end &optional private)
  "Post the current region as a new paste at gist.github.com
Copies the URL into the kill ring.

With a prefix argument, makes a private paste."
  (interactive "r\nP")
  (destructuring-bind (login . token) (github-auth-info)
    (let* ((file (or (buffer-file-name) (buffer-name)))
           (name (file-name-nondirectory file))
           (ext (or (cdr (assoc major-mode gist-supported-modes-alist))
                    (file-name-extension file)
                    "txt"))
           (url-max-redirections 0)
           (url-request-method "POST")
           (url-request-data
            (gist-make-query-string
             `(,@(if private '(("private" . "1")))
               ("login" . ,login)
               ("token" . ,token)
               ("file_ext[gistfile1]" . ,(concat "." ext))
               ("file_name[gistfile1]" . ,name)
               ("file_contents[gistfile1]" .
                ,(let ((buf (buffer-substring begin end)))
                   (with-temp-buffer
                     (insert buf)
                     (untabify (point-min) (point-max))
                     (buffer-string))))))))
      (with-current-buffer (url-retrieve-synchronously "http://gist.github.com/gists")
        (re-search-backward "^Location: \\(.*\\)$")
        (message "Paste created: %s" (match-string 1))
        (if gist-view-gist (browse-url (match-string 1)))
        (kill-new (match-string 1))
        (kill-buffer (current-buffer))))))
