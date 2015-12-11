require [ "fileinto", "imap4flags", "vacation" ];

if address :contains "from" [ "jwiegley@gmail.com", "johnw@newartisans.com", "johnw@gnu.org" ] {
  setflag "\\Seen";
}

# Keep logwatch logs out of the INBOX
if address :contains "from" [ "logwatch@" ] {
  setflag "\\Seen";
  fileinto "list.misc";
}

# Throw away junk or useless mail
elsif allof (header :contains "From" [ "info@netflix.com", "discship@netflix.com"],
             header :contains "Subject" "How was the Picture Quality") {
  discard;
}

elsif header :contains "Subject"
    [ "Undelivered Mail Returned to Sender"
    , "Delivery Status Notification (Failure)"
    ] {
  discard;
}

# Mailing lists
elsif header :contains ["To", "From", "Cc", "Sender"] "tarikh@bahai-library.com"   { fileinto "list.bahai.tarjuman"; }
elsif header :contains ["To", "From", "Cc", "Sender"] "tarjuman@bahai-library.com" { fileinto "list.bahai.tarjuman"; }

elsif header :contains "list-id" "<acl2-books.googlegroups.com>"                   { fileinto "list.acl2.books"; }
elsif header :contains "list-id" "<acl2-help.utlists.utexas.edu>"                  { fileinto "list.acl2.help"; }
elsif header :contains "list-id" "<acl2.utlists.utexas.edu>"                       { fileinto "list.acl2"; }
