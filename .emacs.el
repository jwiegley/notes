(defun toggle-code-file (&optional arg)
  (interactive "p")
  (cond
   ((string-match "\\.as[cphma]x\\'" buffer-file-name)
    (find-file (concat buffer-file-name ".cs")))
   ((string-match "\\.as[cphma]x\\.cs\\'" buffer-file-name)
    (find-file (substring buffer-file-name 0
			  (- (length buffer-file-name) 3))))
   ((string-match "\\.\\(c\\(c\\|pp\\)?\\|mm?\\)\\'" buffer-file-name)
    (find-file (concat (substring buffer-file-name 0
				  (match-beginning 0)) ".h")))
   ((string-match "\\.h\\'" buffer-file-name)
    (let ((base (substring buffer-file-name 0
			   (match-beginning 0))))
      (dolist (ext '(".cc" ".cpp" ".c" ".mm" ".m"))
	(if (file-readable-p (concat base ext))
	    (find-file (concat base ext))))))))
