(defun comment-and-copy (beg end)
  (interactive "r")
  (insert (buffer-substring beg end))
  (comment-region beg end))
