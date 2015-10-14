(defun gnus-user-format-function-r (header)
  "Given a Gnus message header, returns priority mark.
Here are the meanings:

The first column represent my relationship to the To: field.  It can be:

         I didn't appear (and the letter had one recipient)
   :     I didn't appear (and the letter had more than one recipient)
   <     I was the sole recipient
   +     I was among a few recipients
   *     There were many recipients

The second column represents the Cc: field:

    .    I wasn't mentioned, but one other was
    :    I wasn't mentioned, but others were
    ^    I was the only Cc mentioned
    &    I was among a few Cc recipients
    %    I was among many Cc recipients

These can combine in some ways to tell you at a glance how visible the message
is:

   >.    Someone wrote to me and one other
    &    I was copied along with several other people
   *:    Mail to lots of people in both the To and Cc!"
  (let* ((to (or (cdr (assoc 'To (mail-header-extra header))) ""))
         (cc (or (cdr (assoc 'Cc (mail-header-extra header))) ""))
         (to-len (length (split-string to "\\s-*,\\s-*")))
         (cc-len (length (split-string cc "\\s-*,\\s-*")))
         (to-char (cond )))
    (cond ((string-match gnus-ignored-from-addresses to)
           (cond ((= to-len 1)
                  (cond ((string= cc "") "< ")
                        ((= cc-len 1) "<.")
                        (t "<:")))
                 ((< to-len gnus-count-recipients-threshold)
                  (cond ((string= cc "") "+ ")
                        ((= cc-len 1) "+.")
                        (t "+:")))
                 (t
                  (cond ((string= cc "") "* ")
                        ((= cc-len 1) "*.")
                        (t "*:")))))

          ((string-match gnus-ignored-from-addresses cc)
           (cond ((= cc-len 1)
                  (cond ((= to-len 1) " ^")
                        (t ":^")))
                 ((< cc-len gnus-count-recipients-threshold)
                  (cond ((= to-len 1) " &")
                        (t ":&")))
                 (t
                  (cond ((= to-len 1) " %")
                        (t ":%")))))
          (t "  "))))