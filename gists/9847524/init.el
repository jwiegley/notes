        (progn
          (setq-default grep-first-column 1)
          (grep-apply-setting 'grep-find-command
                              '("ag --noheading --column " . 25)))