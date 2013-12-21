(defun org-insert-message-link ()
  (interactive)
  (let ((subject (do-applescript "tell application \"Mail\"
        set theMessages to selection
        subject of beginning of theMessages
end tell"))
        (message-id (do-applescript "tell application \"Mail\"
        set theMessages to selection
        message id of beginning of theMessages
end tell")))
    (insert (org-make-link-string (concat "message://" message-id) subject))))
