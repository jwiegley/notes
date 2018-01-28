11:53 Vulcan:~ $ bash -x ~/src/nix/bin/copy-nix hermes --leq -Q -j4
+ HOST=hermes
+ shift 1
++ readlink -f /Users/johnw/.nix-profile
++ readlink -f /run/current-system
+ nix-copy-closure --to hermes /nix/store/z849fs93qx17v6jbflhl4ygs94kp6966-user-environment /nix/store/s4a12k3i2sr4v3mbd0qlmvkp7isaf6p0-darwin-system-18.03.git.228c086
copying 30 missing paths (298.66 MiB) to ‘hermes’...
error: creating directory ‘/nix/store/nix-99499-0’: Permission denied
/Users/johnw/src/nix/bin/copy-nix: line 7: 15997 Segmentation fault: 11  nix-copy-closure --to $HOST $(readlink -f ~/.nix-profile) $(readlink -f /run/current-system)
+ push -h vulcan -f Projects,Contracts,home hermes
+ ssh hermes darwin-rebuild switch
bash: darwin-rebuild: command not found
+ ssh hermes sudo nix-env -u --leq -Q -j4
