    (when (not user)
      (setq user (read-string "GitHub username: "))
      (github-set-config "user" user))

