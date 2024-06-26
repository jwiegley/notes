Setting up password-less, publickey SSH authentication failed.
Possible reasons are:

  1. The remote user has no password set.
  2. The remote server cannot perform reverse DNS lookups on the
     inbound IP address.
  3. Directory ownership/permissions are wrong for $HOME, .ssh, or
     authorized_keys.  This script *should* have fixed this.
  4. The remote user has no shell.
  5. The remote user's home directory is on a stale NFS mount.

The best way to research these problems is to run the following on
the server:

  # sshd -d -d -d -p 6060

And this on the client:

  $ ssh -v -v -v -p 6060 <server>

Then read the dumps on both sides to find out why publickey-only
authentication failed.
