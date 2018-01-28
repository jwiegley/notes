backup:
	USER=jwiegley TOKEN=$(shell /usr/bin/security find-internet-password -a jwiegley -s github.com -l 'ghi token' -w) python gists/gist-backup.py
