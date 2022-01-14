import csv
import sys
from datetime import datetime, timedelta
from pycoingecko import CoinGeckoAPI

cg = CoinGeckoAPI()

def icp_price(date):
    s = date.strftime('%d-%m-%Y')
    data = cg.get_coin_history_by_id('internet-computer', date=s)
    return data['market_data']['current_price']['usd']

print("date,portion,basis,income,total")

balance = 0

with open(sys.argv[1], newline='') as csvfile:
    reader = csv.DictReader(csvfile, delimiter=',', quotechar='|')

    last_date = None
    for row in reader:
        date = datetime.fromisoformat(row['date'])

        if row['amount'] == '0':
            last_date = date
            continue

        if last_date is None:
            print("Must begin list with a 0 valued amount at date of first staking")
            sys.exit(1)

        days = (date - last_date).days
        portion = float(row['amount']) / float(days)
        last_date = last_date + timedelta(days=1)

        for i in range(days):
            d = last_date + timedelta(days=i)
            balance = balance + (portion * icp_price(d))
            print(",".join([str(d),
                            str(portion),
                            str(icp_price(d)),
                            str(portion * icp_price(d)),
                            str(balance)]))
