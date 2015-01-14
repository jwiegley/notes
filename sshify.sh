  1. The remote user has no password set.
  2. The remote server cannot perform reverse DNS lookups on the
     inbound IP address.
  3. Directory ownership/permissions are wrong for $HOME, .ssh, or
     authorized_keys.  This script *should* have fixed this.
  4. The remote user has no shell.
  5. The remote user's home directory is on a stale NFS mount.
