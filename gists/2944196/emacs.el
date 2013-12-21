(defun edit-with-sudo ()
  (interactive)
  (let ((buf (current-buffer)))
    (find-file (concat "/sudo::" (buffer-file-name)))
    (kill-buffer buf)))

(bind-key "C-x S" 'edit-with-sudo)
