#!/bin/bash

# This script will setup public key authentication for a remote SSH host that
# you currently have password access to.  The advantage to this somewhat
# complex method is that it only requires entering the password once to
# perform all the necessary operations.  When complete, it will then log you
# in so you can poke around.
#
# It support two modes, for example:
#
#   sshify root@192.168.217.132
#
# If I also want to automagically add an alias to ~/.ssh/config for this host:
#
#   sshify root@192.168.217.132 centos
#
# Later I can just 'ssh centos', and no passwords will be needed!

SSH_OPTS=''

port=22
identity=''
while getopts 'p:i:' opt; do
    case $opt in
        p)
            port=$OPTARG
            SSH_OPTS="-p $port $SSH_OPTS"
            shift 2
            ;;
        i)
            identity=$OPTARG
            SSH_OPTS="-o IdentityFile=$identity $SSH_OPTS"
            shift 2
            ;;
        \?)
            echo "Invalid option: -$OPTARG" >&2
            exit 1
            ;;
    esac
done

host=$1
alias=$2

# Create the connection master and check it

CONTROL="-o ControlPath=$HOME/.ssh/master-%r@%h:%p"

ssh $SSH_OPTS $CONTROL -MNf $host
ssh $SSH_OPTS $CONTROL -O check $host

# Prepare the file ~/.ssh/authorized_keys

ssh $SSH_OPTS $CONTROL $host 'test -d .ssh || mkdir .ssh'
ssh $SSH_OPTS $CONTROL $host 'chmod 700 .ssh'
cat ~/.ssh/authorized_keys | \
    ssh $SSH_OPTS $CONTROL $host 'cat > .ssh/authorized_keys'
ssh $SSH_OPTS $CONTROL $host 'chmod 600 .ssh/authorized_keys'
# Make SELinux happy (this is a CentOS 6 bug, but the fix is harmless)
ssh $SSH_OPTS $CONTROL $host \
    'test -x /sbin/restorecon && /sbin/restorecon .ssh .ssh/authorized_keys'

# Exit the connection master

ssh $SSH_OPTS $CONTROL -O exit $host

# Add a new SSH alias for this host, if an alias name was provided

if [[ -n $alias ]]; then
    user=$(echo $host | sed 's/@.*//')
    hostname=$(echo $host | sed 's/.*@//')

    if ! grep '^Host $alias' ~/.ssh/config; then
        echo >> ~/.ssh/config
        echo "Host $alias" >> ~/.ssh/config
        if [[ -n $user ]]; then
            echo "  User $user" >> ~/.ssh/config
        fi
        echo "  HostName $hostname" >> ~/.ssh/config
        if [[ $port != 22 ]]; then
            echo "  Port $port" >> ~/.ssh/config
        fi
        if [[ -n $identity ]]; then
            echo "  IdentityFile $identity" >> ~/.ssh/config
        fi
    fi
fi

# Test the new host by forcing publickey authentication.  The connection
# should happen immediately, but a timeout of 30 seconds is still used.

LIMIT_OPTS='-o PreferredAuthentications=publickey -o ConnectTimeout=30s'
if [[ -n $alias ]]; then
    remote=$alias
else
    remote=$host
fi

if ssh $SSH_OPTS $LIMIT_OPTS $remote true; then
    failure=false
else
    failure=true
fi

# If the publickey-only connection failed, list the typical reasons.

if [[ $failure == true ]]; then
    cat <<EOF
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
EOF
else
    echo '=========================================='
    echo 'Congratulations, SSHificiation successful!'
    echo '=========================================='
fi

### sshify ends here
