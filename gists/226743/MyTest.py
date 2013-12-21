import ledger

for txn in ledger.Journal("/tmp/bug.dat"):
    print txn.payee
