#!/usr/bin/env perl

while (<>) {
    s/unsafeCoerce :: a -> b/--unsafeCoerce :: a -> b/;
    print;
}
