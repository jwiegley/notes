;;;_ * org-mode

(require 'org-install)
(require 'org-attach)
(require 'org-devonthink)
(require 'ob-R)
(require 'ob-python)
(require 'ob-emacs-lisp)
(require 'ob-haskell)
(require 'ob-sh)

;;(load "org-log" t)

(add-to-list 'auto-mode-alist '("\\.org$" . org-mode))

(defun make-ceg-bugzilla-bug (product component version priority severity)
  (interactive
   (let ((omk (get-text-property (point) 'org-marker)))
     (with-current-buffer (marker-buffer omk)
       (save-excursion
         (goto-char omk)
         (let ((products
                (list (list "ABC" (list "Admin" "User" "Other" "CSR")
                            (list "3.0"))
                      (list "Bizcard" (list "Catalog" "Content Section"
                                            "Uploader" "Visual Aesthetics"
                                            "webui")
                            (list "unspecified"))
                      (list "Adagio" (list "DTSX" "PTS" "Satellite" "Zips"
                                           "Core")
                            (list "unspecified"))
                      (list "IT" (list "install" "network" "repair" "misc")
                            (list "unspecified"))
                      (list "EVAprint" (list "misc")
                            (list "1.0"))))
               (priorities (list "P1" "P2" "P3" "P4" "P5"))
               (severities (list "blocker" "critical" "major"
                                 "normal" "minor" "trivial" "enhancement"))
               (product (org-get-category)))
           (list product
                 (let ((components (nth 1 (assoc product products))))
                   (if (= 1 (length components))
                       (car components)
                     (ido-completing-read "Component: " components
                                          nil t nil nil (car (last components)))))
                 (let ((versions (nth 2 (assoc product products))))
                   (if (= 1 (length versions))
                       (car versions)
                     (ido-completing-read "Version: " versions
                                          nil t nil nil (car (last versions)))))
                 (let ((orgpri (nth 3 (org-heading-components))))
                   (if (and orgpri (= ?A orgpri))
                       "P1"
                     (ido-completing-read "Priority: " priorities
                                          nil t nil nil "P3")))
                 (ido-completing-read "Severity: " severities nil t nil nil
                                      "normal") ))))))
  (if (string= product "Bizcard")
      (setq product "BizCard"))
  (let ((omk (get-text-property (point) 'org-marker)))
    (with-current-buffer (marker-buffer omk)
      (save-excursion
        (goto-char omk)
        (let ((heading (nth 4 (org-heading-components)))
              (contents (buffer-substring-no-properties
                         (org-entry-beginning-position)
                         (org-entry-end-position)))
              bug)
          (with-temp-buffer
            (insert contents)
            (goto-char (point-min))
            (delete-region (point) (1+ (line-end-position)))
            (search-forward ":PROP")
            (delete-region (match-beginning 0) (point-max))
            (goto-char (point-min))
            (while (re-search-forward "^   " nil t)
              (delete-region (match-beginning 0) (match-end 0)))
            (goto-char (point-min))
            (while (re-search-forward "^SCHE" nil t)
              (delete-region (match-beginning 0) (1+ (line-end-position))))
            (goto-char (point-min))
            (when (eobp)
              (insert "No description.")
              (goto-char (point-min)))
            (insert (format "Product: %s
Component: %s
Version: %s
Priority: %s
Severity: %s
Hardware: Other
OS: Other
Summary: %s" product component version priority severity heading) ?\n ?\n)
            (let ((buf (current-buffer)))
              (with-temp-buffer
                (let ((tmpbuf (current-buffer)))
                  (if nil
                      (insert "Bug 999 posted.")
                    (with-current-buffer buf
                      (shell-command-on-region
                       (point-min) (point-max)
                       "~/bin/bugzilla-submit https://portal/bugzilla/"
                       tmpbuf)))
                  (goto-char (point-min))
                  (re-search-forward "Bug \\([0-9]+\\) posted.")
                  (setq bug (match-string 1))))))
          (save-excursion
            (org-back-to-heading t)
            (re-search-forward "\\(TODO\\|DEFERRED\\|STARTED\\|WAITING\\|DELEGATED\\) \\(\\[#[ABC]\\] \\)?")
            (insert (format "[[cegbug:%s][#%s]] " bug bug)))))))
  (org-agenda-redo))

(defun make-ledger-bugzilla-bug (product component version priority severity)
  (interactive
   (let ((omk (get-text-property (point) 'org-marker)))
     (with-current-buffer (marker-buffer omk)
       (save-excursion
         (goto-char omk)
         (let ((components
                (list "data" "doc" "expr" "lisp" "math" "python" "report"
                      "test" "util" "website" "build" "misc"))
               (priorities (list "P1" "P2" "P3" "P4" "P5"))
               (severities (list "blocker" "critical" "major"
                                 "normal" "minor" "trivial" "enhancement"))
               (product "Ledger")
               (version "3.0.0-20100615"))
           (list product
                 (ido-completing-read "Component: " components
                                      nil t nil nil (car (last components)))
                 version
                 (let ((orgpri (nth 3 (org-heading-components))))
                   (if (and orgpri (= ?A orgpri))
                       "P1"
                     (ido-completing-read "Priority: " priorities
                                          nil t nil nil "P3")))
                 (ido-completing-read "Severity: " severities nil t nil nil
                                      "normal") ))))))
  (let ((omk (get-text-property (point) 'org-marker)))
    (with-current-buffer (marker-buffer omk)
      (save-excursion
        (goto-char omk)
        (let ((heading (nth 4 (org-heading-components)))
              (contents (buffer-substring-no-properties
                         (org-entry-beginning-position)
                         (org-entry-end-position)))
              bug)
          (with-temp-buffer
            (insert contents)
            (goto-char (point-min))
            (delete-region (point) (1+ (line-end-position)))
            (search-forward ":PROP")
            (delete-region (match-beginning 0) (point-max))
            (goto-char (point-min))
            (while (re-search-forward "^   " nil t)
              (delete-region (match-beginning 0) (match-end 0)))
            (goto-char (point-min))
            (while (re-search-forward "^SCHE" nil t)
              (delete-region (match-beginning 0) (1+ (line-end-position))))
            (goto-char (point-min))
            (when (eobp)
              (insert "No description.")
              (goto-char (point-min)))
            (insert (format "Product: %s
Component: %s
Version: %s
Priority: %s
Severity: %s
Hardware: Other
OS: Other
Summary: %s" product component version priority severity heading) ?\n ?\n)
            (let ((buf (current-buffer)))
              (with-temp-buffer
                (let ((tmpbuf (current-buffer)))
                  (if nil
                      (insert "Bug 999 posted.")
                    (with-current-buffer buf
                      (shell-command-on-region
                       (point-min) (point-max)
                       "~/bin/bugzilla-submit http://newartisans.com/bugzilla/"
                       tmpbuf)))
                  (goto-char (point-min))
                  (re-search-forward "Bug \\([0-9]+\\) posted.")
                  (setq bug (match-string 1))))))
          (save-excursion
            (org-back-to-heading t)
            (re-search-forward "\\(TODO\\|DEFERRED\\|STARTED\\|WAITING\\|DELEGATED\\) \\(\\[#[ABC]\\] \\)?")
            (insert (format "[[bug:%s][#%s]] " bug bug)))))))
  (org-agenda-redo))

(defun make-bugzilla-bug ()
  (interactive)
  (let ((omk (get-text-property (point) 'org-marker)))
    (if (string-match "/ledger/" (buffer-file-name (marker-buffer omk)))
        (call-interactively #'make-ledger-bugzilla-bug)
      (call-interactively #'make-ceg-bugzilla-bug))))

(defun save-org-mode-files ()
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (when (eq major-mode 'org-mode)
        (if (and (buffer-modified-p) (buffer-file-name))
            (save-buffer))))))

(run-with-idle-timer 25 t 'save-org-mode-files)

(defun my-org-push-mobile ()
  (interactive)
  (with-current-buffer (find-file-noselect "~/Dropbox/todo.txt")
    (org-mobile-push)))

;; (run-with-idle-timer 600 t 'my-org-push-mobile)

(defun org-my-auto-exclude-function (tag)
  (and (cond
        ((string= tag "call")
         (let ((hour (nth 2 (decode-time))))
           (or (< hour 8) (> hour 21))))
        ((string= tag "errand")
         (let ((hour (nth 2 (decode-time))))
           (or (< hour 12) (> hour 17))))
        ((string= tag "home")
         (with-temp-buffer
           (call-process "/sbin/ifconfig" nil t nil "en0" "inet")
           (goto-char (point-min))
           (not (re-search-forward "inet 192\\.168\\.9\\." nil t))))
        ((string= tag "net")
         (/= 0 (call-process "/sbin/ping" nil nil nil
                             "-c1" "-q" "-t1" "mail.gnu.org")))
        ((string= tag "fun")
         org-clock-current-task))
       (concat "-" tag)))

;;(defun org-indent-empty-items (arg)
;;  (when (eq arg 'empty)
;;    (goto-char (line-end-position))
;;    (cond
;;     ((org-at-item-p) (org-indent-item 1))
;;     ((org-on-heading-p)
;;      (if (equal this-command last-command)
;;        (condition-case nil
;;            (org-promote-subtree)
;;          (error
;;           (save-excursion
;;             (goto-char (point-at-bol))
;;             (and (looking-at "\\*+") (replace-match ""))
;;             (org-insert-heading)
;;             (org-demote-subtree))))
;;      (org-demote-subtree))))))
;;
;;(add-hook 'org-pre-cycle-hook 'org-indent-empty-items)

(defun my-org-mobile-post-push-hook ()
  (shell-command "ssh root@192.168.9.144 chown admin:admin '/c/docs/'")
  (message "Fixed permissions on https://johnw.homeunix.net/docs"))

(add-hook 'org-mobile-post-push-hook 'my-org-mobile-post-push-hook)

(defun my-org-convert-incoming-items ()
  (interactive)
  (with-current-buffer (find-file-noselect org-mobile-inbox-for-pull)
    (goto-char (point-min))
    (while (re-search-forward "^\\* " nil t)
      (goto-char (match-beginning 0))
      (insert ?*)
      (forward-char 2)
      (insert "TODO ")
      (goto-char (line-beginning-position))
      (forward-line)
      (insert
       (format
        "   SCHEDULED: %s
   :PROPERTIES:
   :ID:       %s   :END:
   "
        (with-temp-buffer (org-insert-time-stamp (current-time)))
        (shell-command-to-string "uuidgen"))))
    (let ((tasks (buffer-string)))
      (erase-buffer)
      (save-buffer)
      (kill-buffer (current-buffer))
      (with-current-buffer (find-file-noselect "~/Dropbox/todo.txt")
        (save-excursion
          (goto-char (point-min))
          (search-forward "* CEG")
          (goto-char (match-beginning 0))
          (insert tasks))))))

(add-hook 'org-mobile-post-pull-hook 'my-org-convert-incoming-items)

(defun org-insert-bug (bug)
  (interactive "nBug: ")
  (insert (format "[[cegbug:%s][#%s]]" bug bug)))

(defun org-cmp-ceg-bugs (a b)
  (let* ((bug-a (and (string-match "#\\([0-9]+\\)" a)
                     (match-string 1 a)))
         (bug-b (and (string-match "#\\([0-9]+\\)" b)
                     (match-string 1 b)))
         (cmp (and bug-a bug-b
                   (- (string-to-number bug-b)
                      (string-to-number bug-a)))))
    (cond ((null cmp) nil)
          ((< cmp 0) -1)
          ((> cmp 0) 1)
          ((= cmp 0) nil))))

(defun org-my-state-after-clock-out (state)
  (if (string= state "STARTED")
      "TODO"
    state))

(defun replace-named-dates ()
  (interactive)
  (while (re-search-forward
          "-\\(Jan\\|Feb\\|Mar\\|Apr\\|May\\|Jun\\|Jul\\|Aug\\|Sep\\|Oct\\|Nov\\|Dec\\)-"
          nil t)
    (let ((mon (match-string 1)))
      (replace-match
       (format "/%s/"
               (cond ((equal mon "Jan") "01")
                     ((equal mon "Feb") "02")
                     ((equal mon "Mar") "03")
                     ((equal mon "Apr") "04")
                     ((equal mon "May") "05")
                     ((equal mon "Jun") "06")
                     ((equal mon "Jul") "07")
                     ((equal mon "Aug") "08")
                     ((equal mon "Sep") "09")
                     ((equal mon "Oct") "10")
                     ((equal mon "Nov") "11")
                     ((equal mon "Dec") "12")))))))

(defvar org-my-archive-expiry-days 1
  "The number of days after which a completed task should be auto-archived.
This can be 0 for immediate, or a floating point value.")

(defconst org-my-ts-regexp "[[<]\\([0-9]\\{4\\}-[0-9]\\{2\\}-[0-9]\\{2\\} [^]>\r\n]*?\\)[]>]"
  "Regular expression for fast inactive time stamp matching.")

(defun org-my-closing-time ()
  (let* ((state-regexp
          (concat "- State \"\\(?:" (regexp-opt org-done-keywords)
                  "\\)\"\\s-*\\[\\([^]\n]+\\)\\]"))
         (regexp (concat "\\(" state-regexp "\\|" org-my-ts-regexp "\\)"))
         (end (save-excursion
                (outline-next-heading)
                (point)))
         begin
         end-time)
    (goto-char (line-beginning-position))
    (while (re-search-forward regexp end t)
      (let ((moment (org-parse-time-string (match-string 1))))
        (if (or (not end-time)
                (time-less-p (apply #'encode-time end-time)
                             (apply #'encode-time moment)))
            (setq end-time moment))))
    (goto-char end)
    end-time))

(defun org-my-archive-done-tasks ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (let ((done-regexp
           (concat "^\\*\\* \\(" (regexp-opt org-done-keywords) "\\) ")))
      (while (re-search-forward done-regexp nil t)
        (if (>= (time-to-number-of-days
                 (time-subtract (current-time)
                                (apply #'encode-time (org-my-closing-time))))
                org-my-archive-expiry-days)
            (org-archive-subtree))))
    (save-buffer)))

(defalias 'archive-done-tasks 'org-my-archive-done-tasks)

(defun org-get-inactive-time ()
  (let ((begin (point)))
    (save-excursion
      (outline-next-heading)
      (if (re-search-backward org-my-ts-regexp begin t)
          (let ((time (float-time (org-time-string-to-time (match-string 0)))))
            (assert (floatp time))
            time)
        (debug)))))

(defun org-get-completed-time ()
  (let ((begin (point)))
    (save-excursion
      (outline-next-heading)
      (and (re-search-backward "\\(- State \"\\(DONE\\|DEFERRED\\|CANCELLED\\)\"\\s-+\\[\\(.+?\\)\\]\\|CLOSED: \\[\\(.+?\\)\\]\\)" begin t)
           (time-to-seconds (org-time-string-to-time (or (match-string 3)
                                                         (match-string 4))))))))

(defun org-my-sort-done-tasks ()
  (interactive)
  (goto-char (point-min))
  (org-sort-entries-or-items t ?F #'org-get-inactive-time #'<)
  (goto-char (point-min))
  (while (re-search-forward "


+" nil t)
    (delete-region (match-beginning 0) (match-end 0))
    (insert "
"))
  (let (after-save-hook)
    (save-buffer))
  (org-overview))

(defalias 'sort-done-tasks 'org-my-sort-done-tasks)

(defun org-maybe-remember (&optional done)
  (interactive "P")
  (if (string= (buffer-name) "*Remember*")
      (call-interactively 'org-ctrl-c-ctrl-c)
    (if (null done)
        (call-interactively 'org-remember)
      (let ((org-remember-templates
             '((110 "* STARTED %?
  - State \"STARTED\"    %U
  SCHEDULED: %t
  :PROPERTIES:
  :ID:       %(shell-command-to-string \"uuidgen\")  :END:
  %U" "~/Dropbox/todo.txt" "Inbox"))))
        (org-remember))))
  (set-fill-column 72))

(defun jump-to-ledger-journal ()
  (interactive)
  (find-file-other-window "~/Dropbox/Accounts/ledger.dat")
  (goto-char (point-max))
  (insert (format-time-string "%Y/%m/%d ")))

(defun org-inline-note ()
  (interactive)
  (switch-to-buffer-other-window "todo.txt")
  (goto-char (point-min))
  (re-search-forward "^\\* Inbox$")
  (re-search-forward "^  :END:")
  (forward-line)
  (goto-char (line-beginning-position))
  (insert "** NOTE ")
  (save-excursion
    (insert (format "
   :PROPERTIES:
   :ID:       %s   :VISIBILITY: folded
   :END:
   " (shell-command-to-string "uuidgen")))
    (org-insert-time-stamp nil t 'inactive)
    (insert ?\n))
  (save-excursion
    (forward-line)
    (org-cycle)))

(defun org-remember-note ()
  (interactive)
  (if (string= (buffer-name) "*Remember*")
      (call-interactively 'org-ctrl-c-ctrl-c)
    (let ((org-remember-templates
           '((110 "* NOTE %?
  :PROPERTIES:
  :ID:       %(shell-command-to-string \"uuidgen\")  :VISIBILITY: folded
  :END:
  %U" "~/Dropbox/todo.txt" "Inbox"))))
      (call-interactively 'org-remember))))

(defun org-get-message-link ()
  (let ((subject (do-applescript "tell application \"Mail\"
        set theMessages to selection
        subject of beginning of theMessages
end tell"))
        (message-id (do-applescript "tell application \"Mail\"
        set theMessages to selection
        message id of beginning of theMessages
end tell")))
    (org-make-link-string (concat "message://" message-id) subject)))

(defun org-get-message-sender ()
  (do-applescript "tell application \"Mail\"
        set theMessages to selection
        sender of beginning of theMessages
end tell"))

(defun org-get-url-link ()
  (let ((subject (do-applescript "tell application \"Safari\"
        name of document of front window
end tell"))
        (url (do-applescript "tell application \"Safari\"
        URL of document of front window
end tell")))
    (org-make-link-string url subject)))

(defun org-get-file-link ()
  (let ((subject (do-applescript "tell application \"Finder\"
        set theItems to the selection
        name of beginning of theItems
end tell"))
        (path (do-applescript "tell application \"Finder\"
        set theItems to the selection
        POSIX path of (beginning of theItems as text)
end tell")))
    (org-make-link-string (concat "file:" path) subject)))

(defun org-insert-message-link ()
  (interactive)
  (insert (org-get-message-link)))

(defun org-insert-url-link ()
  (interactive)
  (insert (org-get-url-link)))

(defun org-insert-file-link ()
  (interactive)
  (insert (org-get-file-link)))

(defun org-set-dtp-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Document" (org-get-dtp-link)D))

(defun org-set-message-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Message" (org-get-message-link)))

(defun org-set-message-sender ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Submitter" (org-get-message-sender)))

(defun org-set-url-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "URL" (org-get-url-link)))

(defun org-set-file-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "File" (org-get-file-link)))

(defun org-dtp-message-open ()
  "Visit the message with the given MESSAGE-ID.
This will use the command `open' with the message URL."
  (interactive)
  (re-search-backward "\\[\\[message://\\(.+?\\)\\]\\[")
  (do-applescript
   (format "tell application \"DEVONthink Pro\"
        set searchResults to search \"%%3C%s%%3E\" within URLs
        open window for record (get beginning of searchResults)
end tell" (match-string 1))))

(defun org-export-tasks ()
  (interactive)
  (let ((index 1))
   (org-map-entries
    #'(lambda ()
        (outline-mark-subtree)
        (org-export-as-html 3)
        (write-file (format "%d.html" index))
        (kill-buffer (current-buffer))
        (setq index (1+ index)))
    "LEVEL=2")))

(defun org-make-regress-test ()
  (interactive)
  (save-excursion
    (outline-previous-visible-heading 1)
    (let ((begin (point))
          (end (save-excursion
                 (outline-next-heading)
                 (point)))
          (input "\n") (data "") (output ""))
      (goto-char begin)
      (when (re-search-forward ":SCRIPT:\n" end t)
        (goto-char (match-end 0))
        (let ((input-beg (point)))
          (re-search-forward "[         ]+:END:")
          (setq input (buffer-substring input-beg (match-beginning 0)))))
      (goto-char begin)
      (when (search-forward ":\\(DATA\\|SOURCE\\):\n" end t)
        (goto-char (match-end 0))
        (let ((data-beg (point)))
          (re-search-forward "[         ]+:END:")
          (setq data (buffer-substring data-beg (match-beginning 0)))))
      (goto-char begin)
      (when (search-forward ":OUTPUT:\n" end t)
        (goto-char (match-end 0))
        (let ((output-beg (point)))
          (re-search-forward "[         ]+:END:")
          (setq output (buffer-substring output-beg (match-beginning 0)))))
      (goto-char begin)
      (when (re-search-forward ":ID:\\s-+\\([^-]+\\)" end t)
        (find-file (expand-file-name (concat (match-string 1) ".test")
                                     "~/src/ledger/test/regress/"))
        (insert input "<<<\n" data ">>>1\n" output ">>>2\n=== 0\n")
        (pop-to-buffer (current-buffer))
        (goto-char (point-min))))))

(fset 'sort-todo-categories
   [?\C-u ?\C-s ?^ ?\\ ?* ?\S-  ?\C-a ?^ ?a ?^ ?p ?^ ?o ?\C-e])

(fset 'sort-subcategories
   [?\C-u ?\C-s ?^ ?\\ ?* ?\\ ?* ?\S-  ?P ?r ?o ?j ?e ?c ?t ?\C-a ?^ ?a ?^ ?p ?^ ?o ?\C-e])

(fset 'match-bug-list
   [?\C-s ?= ?\C-b ?\C-f ?\C-  ?\C-e ?\M-w ?\C-a ?\C-n C-return ?\M-< ?\C-s ?\M-y C-return])

(fset 'match-up-bugs
   [?\C-s ?= ?\C-  ?\C-e ?\M-w ?\C-a ?\C-n C-return ?\M-< ?\C-s ?# ?\M-y C-return])

