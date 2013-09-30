(defun org-my-archive-done-tasks ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (let ((done-regexp
	   (concat "\\* \\(" (regexp-opt org-done-keywords) "\\) "))
	  (state-regexp
	   (concat "- State \"\\(?:" (regexp-opt org-done-keywords)
		   "\\)\"\\s-*\\[\\([^]\n]+\\)\\]"))
	  (inactive-regexp))
      (while (re-search-forward done-regexp nil t)
	(let ((end (save-excursion
		     (outline-next-heading)
		     (point)))
	      begin)
	  (goto-char (line-beginning-position))
	  (setq begin (point))
	  (if (or (re-search-forward state-regexp end t)
		  (re-search-forward org-my-ts-regexp end t))
	      (let* ((time-string (match-string 1))
		     (when-closed (org-parse-time-string time-string)))
		(if (>= (time-to-number-of-days
			 (time-subtract (current-time)
					(apply #'encode-time when-closed)))
			org-my-archive-expiry-days)
		    (org-archive-subtree)))
	    (goto-char end)))))
    (save-buffer)))

(defalias 'archive-done-tasks 'org-my-archive-done-tasks)
