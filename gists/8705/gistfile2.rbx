define rfile ($owner = "root", $group = "root", $mode = "644") {
  file { $title:
    owner  => $owner,
    group  => $group,
    mode   => $mode,
    source => "puppet://puppet/vps$name",
    ensure  => present;
  }
}

class yum {
  package { yum: ensure => installed }

  $rpmforge_version = "0.3.6-1"
  $distribution     = "el5"

  package { rpmforge-release:
    provider => rpm,
    source   => "http://packages.sw.be/rpmforge-release/rpmforge-release-$rpmforge_version.$distribution.rf.$architecture.rpm",
    ensure => installed;
  }

  yumrepo { "base":       priority => 1 }
  yumrepo { "updates":    priority => 1 }
  yumrepo { "addons":     priority => 1 }
  yumrepo { "extras":     priority => 1 }
  yumrepo { "centosplus": priority => 2, enabled => 1 }

  yumrepo { "dlutter":
    descr    => "Unsupported RHEL5 packages (lutter)",
    baseurl  => 'http://people.redhat.com/dlutter/yum/rhel/$releasever/$basearch/',
    enabled  => 1,
    gpgcheck => 0,
    priority => 10;
  }

  yumrepo { "utterramblings":
    descr    => "Jason's Utter Ramblings Repo",
    baseurl  => 'http://www.jasonlitka.com/media/EL$releasever/$basearch/',
    enabled  => 1,
    gpgcheck => 1,
    gpgkey   => "http://www.jasonlitka.com/media/RPM-GPG-KEY-jlitka",
    priority => 1;
  }

  yumrepo { "rpmforge":
    descr      => 'Red Hat Enterprise $releasever - RPMforge.net - dag',
    gpgkey     => "http://dag.wieers.com/rpm/packages/RPM-GPG-KEY.dag.txt",
    mirrorlist => "http://apt.sw.be/redhat/el$releasever/en/mirrors-rpmforge",
    enabled    => 1,
    protect    => 0,
    gpgcheck   => 1,
    priority   => 11,
    require    => Package[rpmforge-release];
  }
}

class sudo {
  package { sudo: ensure => installed }

  file { "/etc/sudoers":
    mode  => 440,
    owner => "root",
    group => $operatingsystem ? {
      darwin => "wheel",
      default => "root"
    },
    require => Package[sudo];
  }
}

class rhel_admin {
  include sudo

  $packages = [ "man", "htop", "tcpdump", "socat", "logrotate",
                "logwatch", "screen", "tmpwatch" ]

  package { $packages: ensure => installed }
}

class selinux_admin inherits rhel_admin {
  $packages = [ "audit" ]

  package { $packages: ensure => installed }
}

# class trac {
# }

class apache {
  package { httpd: ensure => installed }

  service { "httpd":
    ensure  => running,
    require => Package["httpd"];
  }
}

class secure_apache inherits apache {
  package { mod_security: ensure => installed }
  package { mod_ssl: ensure => installed }
}

class squirrelmail {
  package { squirrelmail: ensure => installed }
}

class gallery {
}

class named   {
  package { bind-chroot: ensure => installed }

  $files = [ "/var/named/chroot/etc/named.conf",
             "/var/named/chroot/etc/zones/master/208.70.150.rev",
             "/var/named/chroot/etc/zones/master/johnwiegley.com.db",
             "/var/named/chroot/etc/zones/master/localhost.db",
             "/var/named/chroot/etc/zones/master/localhost.rev",
             "/var/named/chroot/etc/zones/master/newartisans.com.db" ]

  rfile { $files:
    group  => "named",
    notify => Service[named];
  }

  service { named:
    ensure => running,
    require => [ Package["bind-chroot"] ]
  }
}

class buildbot   {
  package { buildbot: ensure => installed }
}

class imapd {
  package { cyrus-imapd: ensure => installed }

  service { imapd:
    ensure => running,
    require => Package["cyrus-imapd"]
  }
}

class rpmreaper {
  rfile { "/usr/bin/rpmreaper": mode => 755 }
  rfile { "/usr/share/man/man1/rpmreaper.1": }
}

class rsnapshot {
  package { rsnapshot: ensure => installed }

  rfile { "/etc/rsnapshot.conf": mode => 600 }

  cron { "rsnapshot-daily":
    command => "/usr/bin/rsnapshot-wrapper -c /etc/rsnapshot.conf daily > /dev/null",
    user => "root",
    hour => "23",
    minute => "50",
    require => Rfile["/etc/rsnapshot.conf"];
  }
  cron { "rsnapshot-weekly":
    command => "/usr/bin/rsnapshot -c /etc/rsnapshot.conf weekly",
    user => "root",
    hour => "23",
    minute => "35",
    weekday => "saturday",
    require => Rfile["/etc/rsnapshot.conf"];
  }
  cron { "rsnapshot-monthly":
    command => "/usr/bin/rsnapshot -c /etc/rsnapshot.conf monthly",
    user => "root",
    hour => "23",
    minute => "20",
    monthday => "1",
    require => Rfile["/etc/rsnapshot.conf"];
  }
}

class fetchmail {
  package { fetchmail: ensure => installed }
}

class httptunnel {
  package { httptunnel: ensure => installed }
}

class openvpn {
  package { openvpn: ensure => installed }
}

class ntp {
  package { ntp: ensure => installed }
}

class postfix {
  package { postfix: ensure => installed }
}

class postgresql {
  package { postgresql-server: ensure => installed }
}

class xinetd {
  package { xinetd: ensure => installed }
}

class git {
  package { git:
    require => Package[xinetd],
    ensure => installed
  }
}

class hotway {
  package { hotwayd:
    require => Package[xinetd],
    ensure => installed
  }
}

class rsync {
  package { rsync:
    require => Package[xinetd],
    ensure => installed
  }
}

class vsftpd {
  package { vsftpd:
    require => Package[xinetd],
    ensure => installed
  }
}

node "vo12074" {
  include yum
  include sudo
  include selinux_admin
  include secure_apache
  include squirrelmail
  include gallery
  include named
  include buildbot
  include imapd
  include rsnapshot
  include fetchmail
  include httptunnel
  include openvpn
  include ntp
  include postfix
  include postgresql
  include xinetd
  include git
  include hotway
  include rsync
  include vsftpd
}

