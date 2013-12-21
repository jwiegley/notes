import ledger

# COMMODITIES

usd = ledger.commodity_pool.find_or_create('$')

assert '$' == usd.symbol

# AMOUNTS & BALANCES

# VALUES

v = Value('$100.00')

assert v.is_amount()
assert '$' == v.as_amount().commodity.symbol

# JOURNALS

journal.find_account('')
journal.find_or_create_account('')

# ACCOUNTS

account.name
account.fullname()
account.amount
account.total

# TRANSACTIONS

txn.payee

# POSTINGS

post.account

# REPORTING

journal.collect('-M food')
journal.collect_accounts('^assets ^liab ^equity')
