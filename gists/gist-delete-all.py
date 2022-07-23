#!/usr/bin/env python2.7

from subprocess import call
import json
import os
import sys
import urllib2

USER = os.environ['USER'] or 'jwiegley'

req = urllib2.Request('https://api.github.com/users/' + 
                      USER + '/gists?page=1&per_page=200')

req.add_header('Authorization', 'token ' + os.environ['TOKEN'])

u = urllib2.urlopen(req, cafile=os.getenv("NIX_SSL_CERT_FILE"))
i = 0
for gist in json.load(u):
    i = i + 1
    print('Deleting gist {} ID: {} ...'.format(i, gist['id']) )

    req = urllib2.Request('https://api.github.com/gists/' + gist['id'])
    req.add_header('Authorization', 'token ' + os.environ['TOKEN'])
    req.add_header('Accept', 'application/vnd.github+json')
    req.get_method = lambda: 'DELETE'

    urllib2.urlopen(req, cafile=os.getenv("NIX_SSL_CERT_FILE"))
