(defun magit-interactive-rebase ()
  "Start a git rebase -i session, old school-style."
  (interactive)
  (server-start)
  (let* ((section (get-text-property (point) 'magit-section))
	 (commit (and (member 'commit (magit-section-context-type section))
		      (setq commit (magit-section-info section))))
	 (old-editor (getenv "GIT_EDITOR")))
    (setenv "GIT_EDITOR" (expand-file-name "emacsclient" exec-directory))
    (unwind-protect
	(shell-command (concat "git rebase -i "
			       (or (and commit (concat commit "^"))
				   (read-string "Interactively rebase to: "))
			       " &"))
      (if old-editor
	  (setenv "GIT_EDITOR" old-editor)))))