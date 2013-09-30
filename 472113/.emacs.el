(eval-after-load "org-agenda"
  '(progn
     (dolist (map (list org-agenda-keymap org-agenda-mode-map))
       (define-key map "\C-n" 'next-line)
       (define-key map "\C-p" 'previous-line)

       (define-key map "g" 'org-agenda-redo)
       (define-key map "r"
         #'(lambda nil
             (interactive)
             (error "The 'r' command is deprecated here; use 'g'")))
       (define-key map "f" 'org-agenda-date-later)
       (define-key map "b" 'org-agenda-date-earlier)
       (define-key map "r" 'org-agenda-refile)
       (define-key map " " 'org-agenda-tree-to-indirect-buffer)
       (define-key map "F" 'org-agenda-follow-mode)
       (define-key map "q" 'delete-window)
       (define-key map [(meta ?p)] 'org-agenda-earlier)
       (define-key map [(meta ?n)] 'org-agenda-later)

       (define-prefix-command 'org-todo-state-map)

       (define-key map "x" 'org-todo-state-map)

       (define-key org-todo-state-map "d"
         #'(lambda nil (interactive) (org-agenda-todo "DONE")))
       (define-key org-todo-state-map "r"
         #'(lambda nil (interactive) (org-agenda-todo "DEFERRED")))
       (define-key org-todo-state-map "y"
         #'(lambda nil (interactive) (org-agenda-todo "SOMEDAY")))
       (define-key org-todo-state-map "g"
         #'(lambda nil (interactive) (org-agenda-todo "DELEGATED")))
       (define-key org-todo-state-map "n"
         #'(lambda nil (interactive) (org-agenda-todo "NOTE")))
       (define-key org-todo-state-map "s"
         #'(lambda nil (interactive) (org-agenda-todo "STARTED")))
       (define-key org-todo-state-map "t"
         #'(lambda nil (interactive) (org-agenda-todo "TODO")))
       (define-key org-todo-state-map "w"
         #'(lambda nil (interactive) (org-agenda-todo "WAITING")))
       (define-key org-todo-state-map "x"
         #'(lambda nil (interactive) (org-agenda-todo "CANCELLED")))

       (define-key org-todo-state-map "z" #'make-bugzilla-bug))))