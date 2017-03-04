#!/usr/bin/env python2.7

from subprocess import call
import json
import os
import sys
import urllib2

USER = os.environ['USER'] or 'jwiegley'

def download_gists(page):
    req = urllib2.Request('https://api.github.com/users/' + 
                          USER + '/gists?page=' + page + '&per_page=100')
    req.add_header('Authorization', 'token ' + os.environ['TOKEN'])
    u = urllib2.urlopen(req, cafile='/Users/johnw/.nix-profile/etc/ssl/certs/ca-bundle.crt')
    for gist in json.load(u):
        if not os.path.isdir('gists/' + gist['id']):
            call(['git', 'subtree', 
                  'pull' if os.path.isdir('gists/' + gist['id']) else 'add',
                  '--prefix', 'gists/' + gist['id'], 
                  gist['git_pull_url'], 'master'])

download_gists('1')
download_gists('2')
download_gists('3')
download_gists('4')
download_gists('5')
download_gists('6')
download_gists('7')
download_gists('8')
download_gists('9')
download_gists('10')
download_gists('11')
download_gists('12')
download_gists('13')
download_gists('14')
download_gists('16')
download_gists('17')
download_gists('18')
download_gists('19')
download_gists('20')
download_gists('21')
download_gists('22')
download_gists('23')
download_gists('24')
download_gists('25')
