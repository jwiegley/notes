#!/usr/bin/perl

$MULTILINE_MATCHING = 1;

open(ARGS, "/Users/johnw/.MacOSX/environment.plist") || die;

while (<ARGS>) {
    print "export $1" if /<key>(.+?)<\/key>/;
    print "=\"$1\"\n" if /<string>(.+?)<\/string>/;
}
