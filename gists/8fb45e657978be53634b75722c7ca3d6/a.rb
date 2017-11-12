11:23:10 [2m19s] Vulcan $ nix-build '<nixpkgs-next>' -A biber
these derivations will be built:
  /nix/store/zllqbj9kidmjjsgyngsh8l2icfkf8567-perl-ExtUtils-LibBuilder-0.08.drv
  /nix/store/6kp514m7xfdf2kkxamrck324rypymx3j-perl-Text-BibTeX-0.81.drv
  /nix/store/6lc43p4lwxcj936h2khlcpjbvsygnb5q-perl-biber-2.5.drv
building path(s) ‘/nix/store/21chn9zxvcz1dcfldc92l3cx7lnlvkk4-perl-ExtUtils-LibBuilder-0.08’, ‘/nix/store/ac3y2hrbajlm16lvs9v2a1wp0zg8jqbl-perl-ExtUtils-LibBuilder-0.08-devdoc’
unpacking sources
unpacking source archive /nix/store/5dw82l8xva1x4dw7gxhwii6czsfzr2xa-ExtUtils-LibBuilder-0.08.tar.gz
source root is ExtUtils-LibBuilder-0.08
setting SOURCE_DATE_EPOCH to timestamp 1445273838 of file ExtUtils-LibBuilder-0.08/t/pod.t
patching sources
configuring
patching ./t/00-load.t...
patching ./t/01-simple.t...
patching ./t/pod.t...
no configure script, doing nothing
building
Created MYMETA.yml and MYMETA.json
Creating new 'Build' script for 'ExtUtils-LibBuilder' version '0.08'
Building ExtUtils-LibBuilder
running tests
# Testing ExtUtils::LibBuilder 0.08, Perl 5.024001, /nix/store/gglsjccgsmzgwnhgw8xr86f7rb314fdp-perl-5.24.1/bin/perl
t/00-load.t ....... ok
ld: unknown option: -mmacosx-version-min=10.10
error building /private/var/folders/ds/nt2q1_s57cqgt9g94_vmkjcw0000gn/T/nix-build-perl-ExtUtils-LibBuilder-0.08.drv-0/VzfSrWsy2r/libfoo.dylib from /private/var/folders/ds/nt2q1_s57cqgt9g94_vmkjcw0000gn/T/nix-build-perl-ExtUtils-LibBuilder-0.08.drv-0/VzfSrWsy2r/library.o at /nix/store/gglsjccgsmzgwnhgw8xr86f7rb314fdp-perl-5.24.1/lib/perl5/5.24.1/ExtUtils/CBuilder/Base.pm line 321, <DATA> line 226.
# Looks like your test exited with 1 before it could output anything.
t/01-simple.t .....
Dubious, test returned 1 (wstat 256, 0x100)
Failed 7/7 subtests
t/pod-coverage.t .. skipped: Test::Pod::Coverage 1.08 required for testing POD coverage
t/pod.t ........... skipped: Test::Pod 1.22 required for testing POD

Test Summary Report
-------------------
t/01-simple.t   (Wstat: 256 Tests: 0 Failed: 0)
  Non-zero exit status: 1
  Parse errors: Bad plan.  You planned 7 tests but ran 0.
Files=4, Tests=1,  1 wallclock secs ( 0.03 usr  0.02 sys +  0.36 cusr  0.11 csys =  0.52 CPU)
Result: FAIL
Failed 1/4 test programs. 0/1 subtests failed.
builder for ‘/nix/store/zllqbj9kidmjjsgyngsh8l2icfkf8567-perl-ExtUtils-LibBuilder-0.08.drv’ failed with exit code 255
cannot build derivation ‘/nix/store/6lc43p4lwxcj936h2khlcpjbvsygnb5q-perl-biber-2.5.drv’: 1 dependencies couldn't be built
error: build of ‘/nix/store/6lc43p4lwxcj936h2khlcpjbvsygnb5q-perl-biber-2.5.drv’ failed
