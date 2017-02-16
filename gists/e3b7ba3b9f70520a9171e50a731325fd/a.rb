(defun my-gist-region-or-buffer ()
    (interactive)
    (deactivate-mark)
    (with-temp-buffer
      (if buffer-file-name
          (call-process "gist" nil t nil "-f" buffer-file-name "-P")
        (call-process "gist" nil t nil "-P"))
      (kill-ring-save (point-min) (1- (point-max)))
      (message (buffer-substring (point-min) (1- (point-max))))))