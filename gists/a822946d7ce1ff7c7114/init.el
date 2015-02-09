(use-package workgroups
  :diminish workgroups-mode
  :if (not noninteractive)
  :init
  (progn
    (workgroups-mode 1)

    (let ((workgroups-file (expand-file-name "workgroups" user-data-directory)))
      (if (file-readable-p workgroups-file)
          (wg-load workgroups-file)))

    (bind-key "C-\\" 'wg-switch-to-previous-workgroup wg-map)
    (bind-key "\\" 'toggle-input-method wg-map)))
