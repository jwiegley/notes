(defun eshell/date (&rest args)
  "Implementation of date in Lisp."
  (setq args (eshell-flatten-list args))
  (eshell-eval-using-options
   "rm" args
   '(
     (?d  "date"      nil nil "display time described by STRING, not 'now'")
     (nil "debug"     nil nil "annotate the parsed date and warn about questionable usage")
     (?f  "file"      nil nil "like --date; once for each line of DATEFILE")
     (?I  "iso-8601"  nil nil "output date/time in ISO 8601 format")
     (?R  "rfc-email" nil nil "output date and time in RFC 5322 format")
     (nil "rfc-3339"  nil nil "output date/time in RFC 3339 format")
     (?r  "reference" nil nil "display the last modification time of FILE")
     (?s  "set"       nil nil "set time described by STRING")
     (?u  "utc"       nil nil "print or set Coordinated Universal Time (UTC)")
     (nil "universal" nil nil "print or set Coordinated Universal Time (UTC)")
     (nil "help"      nil nil "display this help and exit")
     (nil "version"   nil nil "output version information and exit")
     :preserve-args
     :external "date"
     :show-usage
     :usage "[OPTION]... [+FORMAT]
Display the current time in the given FORMAT, or set the system date.")
   (while args
     (let ((entry (car args)))
       )
     (setq args (cdr args)))
   nil))
