(defun my-proof-display-and-keep-buffer (buffer &optional pos force)
  (if (or force proof-auto-raise-buffers)
      (save-excursion
        (save-selected-window
          (let ((window (proof-get-window-for-buffer buffer)))
            (if (window-live-p window) ;; [fails sometimes?]
                (progn
                  (if proof-three-window-enable
                      (set-window-dedicated-p window nil))
                  (select-window window)
                  (if proof-shrink-windows-tofit
                      (proof-resize-window-tofit)
                    ;; If we're not shrinking to fit, allow the size of
                    ;; this window to change.  [NB: might be nicer to
                    ;; fix the size based on user choice]
                    (setq window-size-fixed nil))
                  ;; For various reasons, point may get moved around in
                  ;; response buffer.  Attempt to normalise its position.
                  (goto-char (or pos (point-max)))
                  (if pos
                      (beginning-of-line)
                    (skip-chars-backward "\n\t "))
                  ;; Ensure point visible.  Again, window may have died
                  ;; inside shrink to fit, for some reason
                  (when (window-live-p window)
                    (unless (pos-visible-in-window-p (point) window)
                      (recenter -1))
                    (with-current-buffer buffer
                      (if (window-bottom-p window)
                          (unless (local-variable-p 'mode-line-format)
                            ;; Don't show any mode line.
                            (set (make-local-variable 'mode-line-format) nil))
                        (unless mode-line-format
                          ;; If the buffer gets displayed elsewhere, re-add
                          ;; the modeline.
                          (kill-local-variable 'mode-line-format))))))))))))

(eval-after-load coq
  '(progn
     (add-hook 'coq-mode-hook
               (lambda ()
                 (defalias 'proof-display-and-keep-buffer
                   'my-proof-display-and-keep-buffer)))))
