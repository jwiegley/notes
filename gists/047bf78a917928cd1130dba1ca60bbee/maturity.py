import re
import csv
import sys
from datetime import datetime, timedelta

pricedb = "icp.pricedb"

def icp_price(date):
    entry = re.compile(r"P ([-0-9]+) ICP \$([0-9.]+)")
    with open(pricedb, newline='') as db:
        for line in db:
            m = entry.match(line)
            if m is not None:
                d = datetime.fromisoformat(m.group(1))
                if d == date:
                    return float(m.group(2))
    return None

print("date,neuron,portion,basis,income,balance,total")

with open(sys.argv[1], newline='') as csvfile:
    reader = csv.DictReader(csvfile, delimiter=',', quotechar='|')

    last_date = {}
    balance = {}

    for row in reader:
        date = datetime.fromisoformat(row['date'])

        neuron = row['neuron']

        if row['amount'] == '0':
            last_date[neuron] = date
            balance[neuron] = 0
            continue

        if last_date is None or neuron not in last_date:
            print("Must begin list with a 0 valued amount at date of first staking")
            sys.exit(1)

        days = (date - last_date[neuron]).days
        portion = float(row['amount']) / float(days)

        for i in range(days):
            last_date[neuron] = last_date[neuron] + timedelta(days=1)
            d = last_date[neuron]
            balance[neuron] = balance[neuron] + (portion * icp_price(d))
            print(",".join([str(d),
                            neuron,
                            str(portion),
                            str(icp_price(d)),
                            str(portion * icp_price(d)),
                            str(sum(balance.values()))]))
