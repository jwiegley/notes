#!/usr/bin/env python

import os
import os.path
import re
import sys
import string

from datetime import datetime

def git_repos(directory):
    for elem in os.listdir(directory):
        entry = os.path.join(directory, elem)
        if os.path.isdir(entry):
            yield entry

def git_log(repo, args = "--format='%an,%ad'"):
    return os.popen("git --git-dir='%s' log %s" % (repo, args))

input_fields = [ "name", "date" ]

def parse_rfc822_date(date):
    try:
        d = datetime.strptime(date, "%c +0000").date()
        return "%d-%02d" % (d.year, d.month)
    except ValueError:
        d = datetime.strptime(date, "%c -0400").date()
        return "%d-%02d" % (d.year, d.month)

data_fields = ( 'Date', 'Adinath', 'David', 'John', 'Fabian', 'Ramen' )

def add_to_table(table, entry):
    if re.search('(afshin|david)', entry['name'], re.IGNORECASE):
        name = data_fields[2]
    elif re.search('(john)', entry['name'], re.IGNORECASE):
        name = data_fields[3]
    elif re.search('(adi)', entry['name'], re.IGNORECASE):
        name = data_fields[1]
    elif re.search('fab', entry['name'], re.IGNORECASE):
        name = data_fields[4]
    elif re.search('ram', entry['name'], re.IGNORECASE):
        name = data_fields[5]
    else:
        return

    if entry['date'] not in table:
        table[entry['date']] = {}

    if name not in table[entry['date']]:
        table[entry['date']][name] = 1
    else:
        table[entry['date']][name] += 1

def field_map(dictseq, name, func):
    for d in dictseq:
        d[name] = func(d[name])
        yield d

def gen_cat(sources):
    for s in sources:
        for item in s:
            yield item

logs  = (git_log(repo) for repo in git_repos(os.path.abspath(sys.argv[1])))
lines = gen_cat(logs)
lines = (dict(zip(input_fields, string.split(line[:-1], ','))) for line in lines)
lines = field_map(lines, 'date', lambda x: parse_rfc822_date(x))

table = {}
for x in lines: add_to_table(table, x)

keys = table.keys()
keys.sort()

print 'COMMITS BY MONTH  -*- mode: org -*-'
print '#+PLOT: title:"Commits" ind:1 deps:(2 3 4 5 6) type:2d with:lines set:"yrange [0:]"'
print '|%s|%s|%s|%s|%s|%s|' % data_fields
print '|------------------+---------+-------+------+--------+-------|'
for date in keys:
    for f in data_fields:
        if f not in table[date]:
            table[date][f] = 0
    print '|[%s-01 Mon]|%d|%d|%d|%d|%d|' % (date, table[date][data_fields[1]],
                                   table[date][data_fields[2]],
                                   table[date][data_fields[3]],
                                   table[date][data_fields[4]],
                                   table[date][data_fields[5]])
