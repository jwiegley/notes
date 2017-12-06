;; without LOOP
(let (dirs)
  (dolist (path (seq-filter
                 (apply-partially #'string-match "-Agda-")
                 (nix-read-environment (concat "ghc" (getenv "GHCVER")))))
    (let ((dir (file-name-directory
                (substring (shell-command-to-string
                            (concat path "/bin/agda-mode locate")) 0 -1))))
      (if (file-directory-p dir)
          (setq dirs (cons dir dirs)))))
  dirs)

;; with LOOP
(loop for path in (seq-filter
                   (apply-partially #'string-match "-Agda-")
                   (nix-read-environment (concat "ghc" (getenv "GHCVER"))))
      for dir = (file-name-directory
                 (substring (shell-command-to-string
                             (concat path "/bin/agda-mode locate")) 0 -1))
      when (file-directory-p dir)
      collect dir)
