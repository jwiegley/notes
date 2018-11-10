#!/usr/bin/env perl

use strict;
use warnings;

while (<ARGV>) {
    print;
    if (/INCLUDE (.+) \*/) {
        open(my $fh, '<:encoding(UTF-8)', $1)
            or die "Could not open file '$1' $!";
        while (my $row = <$fh>) {
            chomp $row;
            print "$row\n";
        }
        close($fh);
    }
}
