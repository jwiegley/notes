import csv
import sys
from datetime import datetime, timedelta
from pycoingecko import CoinGeckoAPI

cg = CoinGeckoAPI()

def icp_price(date):
    s = date.strftime('%d-%m-%Y')
    data = cg.get_coin_history_by_id('internet-computer', date=s)
    return data['market_data']['current_price']['usd']

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
        last_date[neuron] = last_date[neuron] + timedelta(days=1)

        for i in range(days):
            d = last_date[neuron] + timedelta(days=i)
            balance[neuron] = balance[neuron] + (portion * icp_price(d))
            print(",".join([str(d),
                            neuron,
                            str(portion),
                            str(icp_price(d)),
                            str(portion * icp_price(d)),
                            str(sum(balance.values()))]))