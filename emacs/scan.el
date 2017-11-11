;; (2 . 4) <> (3 . 5) = (2 . 6)
;; (4 . 2) <> (5 . 3) = (7 . 3)

(defun scan-sexps2 (beg end)
  (interactive "r")
  (save-restriction
    ;; (narrow-to-region beg end)
    (goto-char (point-min))
    (let ((result (cons '(0 . 0) 0)))
      (cl-flet
          ((merge
            (x y)
            (pcase x
              (`((,xc . ,xo) . ,xcol)
               (pcase y
                 (`((,yc . ,yo) . ,ycol)
                  (cond
                   ((= xo yc)
                    (if (and (= yc 1) (< ycol xcol))
                        (error "Mismatched paren"))
                    (cons (cons xc yo) ycol))
                   ((> xo yc)
                    (if (and (= yc 1) (< ycol xcol))
                        (error "Mismatched paren"))
                    (cons (cons xc (+ yo (- xo yc))) ycol))
                   ((< xo yc)
                    (goto-char (max xcol ycol))
                    (error "Unexpected closing paren")
                    (cons (cons (+ xc (- yc xo)) yo) ycol))))
                 (_ (error "y failed"))))
              (_ (error "x failed")))))
        (while (not (eobp))
          (setq result
                (pcase (char-after)
                  (?\( (merge result
                              (cons '(0 . 1) (current-column))))
                  (?\) (merge result
                              (cons '(1 . 0) (current-column))))
                  (_   result)))
          (forward-char)))
      (message "%s" result))))
