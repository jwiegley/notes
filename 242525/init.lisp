;; -*- lisp -*-

(in-package :cl-user)

(defvar *lisp-packages-directory*
  (merge-pathnames "Library/Lisp/" (user-homedir-pathname)))

#-(or sbcl ecl)
(load (merge-pathnames "asdf" *lisp-packages-directory*))
#+ecl
(require 'asdf)
#+sbcl
(mapc 'require '(sb-bsd-sockets sb-posix asdf asdf-install))
#+sbcl
(pushnew (list (merge-pathnames "site/" *lisp-packages-directory*)
               (merge-pathnames "systems/" *lisp-packages-directory*)
               "Local installation")
         asdf-install:*locations*)

;; #+sb-thread
;; (in-package :sb-thread)
;; (defun current-thread-id ()
;;   (thread-os-thread *current-thread*))
;; (export 'current-thread-id)
;; (in-package :cl-user)

(pushnew (merge-pathnames "systems/" *lisp-packages-directory*)
         asdf:*central-registry*)

;;(dolist (project '("common-macros/" "periods/" "cambl/" "cl-ledger/"
;;                 "red-black/" "cxml/" "closure-common/"))
;;  (pushnew (merge-pathnames project
;;                          (merge-pathnames "Projects/"
;;                                           (user-homedir-pathname)))
;;         asdf:*central-registry*))

(pushnew (merge-pathnames "Library/Emacs/site-lisp/slime/"
                          (user-homedir-pathname))
           asdf:*central-registry*)

(defmacro load-or-install (package)
  `(handler-case
       (progn
         (asdf:operate 'asdf:load-op ,package))
     (asdf:missing-component ()
       #+sbcl (asdf-install:install ,package)
       #+lispworks (error "Cannot load package `~S'" package))))
