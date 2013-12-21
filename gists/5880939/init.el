    (defun erc-cmd-OPME ()
      "Request chanserv to op me."
      (erc-message "PRIVMSG"
                   (format "chanserv op %s %s"
                           (erc-default-target)
                           (erc-current-nick)) nil))

    (defun erc-cmd-DEOPME ()
      "Deop myself from current channel."
      (erc-cmd-DEOP (format "%s" (erc-current-nick))))

    (defun erc-cmd-BAN (nick &optional redirect)
      (let* ((chan (erc-default-target))
             (who (erc-get-server-user nick))
             (host (erc-server-user-host who))
             (user (erc-server-user-login who)))
        (erc-send-command
         (format "MODE %s +b *!%s@%s%s" chan user host redirect))))

    (defun erc-cmd-KICKBAN (nick &rest reason)
      (setq reason (mapconcat #'identity reason " "))
      (and (string= reason "")
           (setq reason nil))
      (erc-cmd-OPME nick)
      (sleep-for 0 250)
      (erc-cmd-BAN nick)
      (erc-send-command (format "KICK %s %s %s"
                                (erc-default-target)
                                nick
                                (or reason
                                    "Kicked (kickban)"))))

    (defun erc-cmd-KICKTROLL (nick &rest reason)
      (setq reason (mapconcat #'identity reason " "))
      (and (string= reason "")
           (setq reason nil))
      (erc-cmd-OPME nick)
      (sleep-for 0 250)
      (erc-cmd-BAN nick "$#haskell-ops")
      (erc-send-command (format "KICK %s %s %s"
                                (erc-default-target)
                                nick
                                (or reason
                                    "Kicked (kickban)"))))
