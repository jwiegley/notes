installcheck flags: -j1 -l1 SHELL=/nix/store/hgsbnqhg7zr5vbjazb250ac4wnj3cfhy-bash-4.4-p12/bin/bash profiledir=\$\(out\)/etc/profile.d installcheck
  GEN    tests/common.sh
running test tests/init.sh... [FAIL]
    + test -n /private/tmp/nix-test
    + test -d /private/tmp/nix-test
    + chmod -R u+w /private/tmp/nix-test
    + rm -rf /private/tmp/nix-test
    + mkdir /private/tmp/nix-test
    + mkdir /private/tmp/nix-test/store
    + mkdir /private/tmp/nix-test/var
    + mkdir -p /private/tmp/nix-test/var/log/nix/drvs
    + mkdir /private/tmp/nix-test/var/nix
    + mkdir /private/tmp/nix-test/etc
    + cat
    + nix-store --init
    dyld: Library not loaded: /lib/libbrotlienc.1.dylib
      Referenced from: /nix/store/pm4px7nfgp2kdwpxq5mlnblj93rajj8s-nix-unstable-1.12pre5849_74f75c85/lib/libnixutil.dylib
      Reason: image not found
    init.sh: line 23: 32576 Abort trap: 6           nix-store --init
running test tests/hash.sh... [FAIL]
    + try md5 '' d41d8cd98f00b204e9800998ecf8427e
    + printf %s ''
    ++ nix-hash --flat --type md5 /private/tmp/nix-test/vector
    dyld: Library not loaded: /lib/libbrotlienc.1.dylib
      Referenced from: /nix/store/pm4px7nfgp2kdwpxq5mlnblj93rajj8s-nix-unstable-1.12pre5849_74f75c85/lib/libnixutil.dylib
      Reason: image not found
    + hash=
running test tests/lang.sh... [FAIL]
    + export TEST_VAR=foo
    + TEST_VAR=foo
    + nix-instantiate --eval -E 'builtins.trace "Hello" 123'
    + grep -q Hello
