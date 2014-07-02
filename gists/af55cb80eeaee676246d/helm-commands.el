(defun helm-c-git-find-file (candidate)
  (let ((dir (substring
              (shell-command-to-string "git rev-parse --git-dir") 0 -1)))
    (find-file (expand-file-name candidate (file-name-directory dir)))))

(defun helm-c-source-git-files-init ()
  "Build `helm-candidate-buffer' of Git files."
  (let ((dir (substring
              (shell-command-to-string "git rev-parse --git-dir") 0 -1)))
    (with-current-buffer (helm-candidate-buffer 'local)
      (mapcar
       (lambda (item) (insert item ?\n))
       (split-string (shell-command-to-string
                      (format "git --git-dir=\"%s\" ls-files" dir)) "\n")))))

(defun helm-find-git-file ()
  (interactive)
  (helm :sources 'helm-c-source-git-files
        :input ""
        :prompt "Find file: "
        :buffer "*Helm git file*"))
