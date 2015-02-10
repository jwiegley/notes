(defun compilation-ansi-color-process-output ()
  (ansi-color-process-output nil)
  (set (make-local-variable 'comint-last-output-start)
       (point-marker)))

(add-hook 'compilation-filter-hook #'compilation-ansi-color-process-output)
