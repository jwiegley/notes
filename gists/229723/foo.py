import ledger
import re
 
account_re = "Assets:Cash"
 
# A poor man's register report
 
running_total = ledger.Value(0)
 
for txn in ledger.Journal("/tmp/bug.dat"):
   for post in txn:
       if re.match(account_re, str(post.account)):
           running_total += post.amount
           print "%s %-20.20s %-20.20s %12s %12s" % \
               (txn.date, txn.payee, post.account, post.amount,
                running_total)
 
