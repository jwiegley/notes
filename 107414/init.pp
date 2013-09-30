  file { "/var/run/log":
    owner  => "root",
    group  => "root",
    mode   => 0755,
    type   => directory,
    ensure => directory;
  }

  file { "/usr/bin/syslog.pl":
    owner  => "root",
    group  => "root",
    mode   => 0755,
    ensure => present,
    source => "puppet://rsyslog/syslog.pl";
  }

  define pipe($ident, $facility = "local7", $priority = "info") {
    include rsyslog

    exec { "create $title fifo":
      command => "/bin/mknod $title p",
      creates => "$title",
      notitfy => Exec["spawn $title fifo listener"];
      require => File["/var/run/log"];
    }

    exec { "spawn $title fifo listener":
      command     => "/usr/bin/perl /usr/bin/syslog.pl $title $ident $facility $priority",
      refreshonly => true,
      require     => File["/usr/bin/syslog.pl"];
    }      
  }
