class nagios::target
{
  package { nagios-nrpe: ensure => installed }

  file { "/etc/firewall.d/nagios-nrpe.ipt":
    owner  => "root",
    group  => "root",
    mode   => 0600,
    ensure => present,
    source => "puppet:///nagios/nagios-nrpe.ipt",
    notify => Exec[reset-firewall];
  }

  file { "/etc/nagios":
    owner  => "root",
    group  => "root",
    mode   => 0755,
    type   => directory,
    ensure => directory;
  }

  file { "/etc/nagios/nrpe.cfg":
    owner   => "root",
    group   => "root",
    mode    => 0644,
    ensure  => present,
    source  => "puppet:///nagios/nrpe.cfg",
    notify  => Service[nrpe],
    require => Package[nagios-nrpe];
  }

  service { nrpe:
    ensure  => running,
    enable  => true,
    require => File["/etc/nagios/nrpe.cfg"];
  }

  @@nagios_host { $fqdn:
    ensure  => present,
    alias   => $hostname,
    address => $ipaddress,
    use     => "generic-host";
  }

  @@nagios_service { "check_ping_${hostname}":
    check_command       => "check_ping!100.0,20%!500.0,60%",
    use                 => "generic-service",
    host_name           => "$fqdn",
    notification_period => "24x7",
    service_description => "${hostname}_check_ping";
  }

  @@nagios_service { "check_disk_${hostname}":
    check_command       => "check_nrpe!check_sda1%",
    use                 => "generic-service",
    host_name           => "$fqdn",
    notification_period => "24x7",
    service_description => "${hostname}_check_disk";
  }
}

class nagios::monitor
{
  include apache

  $packages = [ "nagios", "nagios-plugins", "nagios-plugins-nrpe" ]

  package { $packages: ensure => installed }

  file { "/etc/nagios/command-plugins.cfg":
    owner   => "root",
    group   => "root",
    mode    => 0644,
    ensure  => present,
    source  => "puppet:///nagios/command-plugins.cfg",
    notify  => Service[nagios],
    require => Package[nagios-plugins];
  }

  service { nagios:
    ensure  => running,
    enable  => true,
    require => Package[nagios];
  }

  file { "/var/nagios/rw/nagios.cmd":
    owner  => "root",
    group  => "apache",
    mode   => 0775,
    ensure => present;
  }

  # collect resources and populate /etc/nagios/nagios_*.cfg
  Nagios_host <<||>>
  Nagios_service <<||>>
}
