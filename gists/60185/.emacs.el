(defun duplicate-line (&optional where)
  "Duplicate the line containing point."
  (interactive "d")
  (save-excursion
    (beginning-of-line)
    (let ((beg (point)))
      (end-of-line)
      (copy-region-as-kill beg (point)))
    (end-of-line)
    (if (eobp)
	(insert ?\n)
      (forward-line))
    (open-line 1)
    (yank)))

(define-key ctl-x-map [(control ?d)] 'duplicate-line)
