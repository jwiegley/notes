  (defun my-gist-region-or-buffer (start end)
    (interactive "r")
    (copy-region-as-kill start end)
    (deactivate-mark)
    (let ((file-name buffer-file-name))
      (with-temp-buffer
        (if file-name
            (call-process "gist" nil t nil "-f" file-name "-P")
          (call-process "gist" nil t nil "-P"))
        (kill-ring-save (point-min) (1- (point-max)))
        (message (buffer-substring (point-min) (1- (point-max))))))))
