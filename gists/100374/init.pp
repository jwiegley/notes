  file { "/var/lib/pgsql/data/postgresql.conf":
    name    => "postgresql.conf",
    owner   => "postgres",
    group   => "postgres",
    mode    => 0600,
    ensure  => present,
    source  => "puppet:///postgres/postgresql.conf",
    require => Service[postgresql];
  }

  file { "/var/lib/pgsql/data/postgresql.conf":
    owner   => "postgres",
    group   => "postgres",
    mode    => 0600,
    ensure  => present,
    source  => "puppet:///postgres/postgresql.conf",
    replace => false,
    notify  => Service[postgresql];
  }

  service { postgresql:
    ensure     => running,
    enable     => true,
    hasstatus  => true,
    hasrestart => true,
    require    => Package[postgresql-server];
  }
