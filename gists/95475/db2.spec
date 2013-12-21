7za x /var/lib/artifacts/db2exc_952_LNX.x86_64.7z -o/tmp

#%{__rm} -fr /tmp/expc/samples/repl/xmlpubtk

/tmp/expc/db2_install -n -p EXP -b /usr/db2

# I use exit 0 here in case the installer pre-made the groups
groupadd -f db2grp1
groupadd -f db2fgrp1
groupadd -f dasadm1

useradd -g db2grp1  -m -d /usr/db2/db2inst1 db2inst1 
useradd -g db2fgrp1 -m -d /usr/db2/db2fenc1 db2fenc1 
useradd -g dasadm1  -m -d /usr/db2/dasusr1 dasusr1

cd /usr/db2/instance 
./db2icrt -p 50000 -u db2fenc1 db2inst1
sleep 10
./dascrt -u dasusr1
sleep 5

if ! grep -q DB2_TMINST /etc/services; then
    echo "DB2_TMINST      50000/tcp                       # DB2 Database" \
	>> /etc/services
fi

su - db2inst1 -c "db2 update dbm cfg using svcename 50000"
su - db2inst1 -c "db2set DB2COMM=tcpip"
