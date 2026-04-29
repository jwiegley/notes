backup:
	USER=jwiegley \
	TOKEN=$(shell pass api.github.com | head -1) \
	python gists/gist-backup.py
