class nagios
{
  define service($args = "", $command = false) {
    @@nagios_service { "${title}_${hostname}":
      check_command       => $command ? {
        false   => "${title}!${args}",
        default => "${command}!${args}"
      },
      use                 => "generic-service",
      host_name           => "$fqdn",
      notification_period => "24x7",
      service_description => "${hostname}_${title}";
    }
  }
}

class nagios::target
{
  package { nagios-plugins: ensure => latest }

  $packages = [ nagios-nrpe, nagios-plugins-all ]

  package { $packages:
    ensure  => latest,
    require => Package[nagios-plugins];
  }

  firewall::rule { nagios-nrpe: module => "nagios" }

  file { "/etc/nagios":
    owner  => "root",
    group  => "root",
    mode   => 0755,
    type   => directory,
    ensure => directory;
  }

  file { "/etc/nagios/nrpe":
    owner   => "root",
    group   => "root",
    mode    => 0755,
    type    => directory,
    ensure  => directory,
    require => File["/etc/nagios"];
  }

  $plugin_dir = $architecture ? {
    "x86_64" => "/usr/lib64/nagios/plugins",
    "i386"   => "/usr/lib/nagios/plugins"
  }

  @file { "$plugin_dir/check_service":
    owner   => "root",
    group   => "root",
    mode    => 0755,
    ensure  => present,
    source  => "puppet:///modules/nagios/check_service",
    require => Package[nagios-nrpe],
    tag     => "nagios_checks";
  }

  @file { "$plugin_dir/check_mem":
    owner   => "root",
    group   => "root",
    mode    => 0755,
    ensure  => present,
    source  => "puppet:///modules/nagios/check_mem",
    require => Package[nagios-nrpe],
    tag     => "nagios_checks";
  }

  File <| tag == "nagios_checks" |>
  File <| title == "/var/run/supervisor.sock" |>

  define service() {
    $plugin_dir = $architecture ? {
      "x86_64" => "/usr/lib64/nagios/plugins",
      "i386"   => "/usr/lib/nagios/plugins"
    }

    nagios::target::command { "check_$title":
      command => "$plugin_dir/check_service -s $title";
    }
  }

  define monitor($max_procs_warn = 150, $max_procs_crit = 200,
                 $root_volume = "/dev/mapper/VolGroup00-LogVol00") {
    $plugin_dir = $architecture ? {
      "x86_64" => "/usr/lib64/nagios/plugins",
      "i386"   => "/usr/lib/nagios/plugins"
    }
    
    file { "nrpe.cfg for $title":
      name    => "/etc/nagios/nrpe.cfg",
      owner   => "root",
      group   => "root",
      mode    => 0644,
      ensure  => present,
      content => template("nagios/nrpe.cfg.erb"),
      notify  => Service[nrpe],
      require => Package[nagios-nrpe];
    }
  }

  define command($command) {
    include nagios::target

    file { "/etc/nagios/nrpe/$title.cfg":
      owner   => "root",
      group   => "root",
      mode    => 0755,
      ensure  => present,
      content => "command[$title]=$command\n",
      notify  => Service[nrpe],
      require => File["/etc/nagios/nrpe"];
    }

    nagios::service { "$title":
      command => "check_nrpe",
      args    => "$title";
    }
  }

  service { nrpe:
    ensure     => running,
    hasstatus  => true,
    hasrestart => true,
    enable     => true,
    require    => [ Package[nagios-nrpe],
                    File["/etc/nagios/nrpe"] ];
  }

  @@nagios_host { $fqdn:
    use     => "linux-server",
    alias   => $hostname,
    # jww (2009-05-02): explicit host references!
    address => $hostname ? {
      "abc-p1-srv-1" => "$ipaddress_eth1",
      "abc-p1-srv-2" => "$ipaddress_eth1",
      default        => "$ipaddress"
    },
    ensure  => present;
  }

  nagios::service { check_ping:
    args => "100.0,20%!500.0,60%";
  }
  nagios::service { check_load:
    command => "check_nrpe",
    args    => "check_load";
  }
  nagios::service { check_zombie_procs:
    command => "check_nrpe",
    args    => "check_zombie_procs";
  }
  nagios::service { check_total_procs:
    command => "check_nrpe",
    args    => "check_total_procs";
  }

  nagios::target::command { "check_mem":
    command => "$plugin_dir/check_mem -w 15 -c 5",
  }
  nagios::target::command { "check_swap":
    command => "$plugin_dir/check_swap -w 75 -c 50",
  }
}

class nagios::monitor
{
  include apache

  $packages = [ nagios, nagios-plugins-nrpe ]

  package { $packages: ensure => latest }

  cron { "nagios":
    ensure  => present,
    command => "/sbin/service nagios restart > /dev/null",
    user    => "root",
    hour    => 4,
    minute  => 0;
  }

  file { "/etc/nagios/nagios_host.cfg":
    owner   => "nagios",
    group   => "nagios",
    mode    => 0640,
    ensure  => present,
    notify  => Service[nagios],
    require => Package[nagios];
  }

  file { "/etc/nagios/nagios_service.cfg":
    owner   => "nagios",
    group   => "nagios",
    mode    => 0640,
    ensure  => present,
    notify  => Service[nagios],
    require => Package[nagios];
  }

  file { "/etc/nagios/nagios.cfg":
    owner   => "nagios",
    group   => "nagios",
    mode    => 0664,
    ensure  => present,
    content => template("nagios/nagios.cfg.erb"),
    notify  => Service[nagios],
    require => Package[nagios];
  }

  file { "/etc/nagios/command-plugins.cfg":
    owner   => "root",
    group   => "root",
    mode    => 0644,
    ensure  => present,
    source  => $architecture ? {
      "x86_64" => "puppet:///modules/nagios/command-plugins.cfg",
      "i386"   => "puppet:///modules/nagios/command-plugins_i386.cfg"
    },
    notify  => Service[nagios],
    require => Package[nagios-plugins];
  }

  file { "/etc/nagios/objects":
    owner   => "root",
    group   => "root",
    mode    => 0755,
    type    => directory,
    ensure  => directory,
    require => [ Package[nagios],
                 Package[nagios-plugins] ];
  }

  file { "/etc/nagios/objects/commands.cfg":
    owner   => "nagios",
    group   => "nagios",
    mode    => 0664,
    ensure  => present,
    source  => "puppet:///modules/nagios/objects/commands.cfg",
    notify  => Service[nagios],
    require => File["/etc/nagios/objects"];
  }

  file { "/etc/nagios/cgi.cfg":
    owner   => "nagios",
    group   => "nagios",
    mode    => 0664,
    ensure  => present,
    content => template("nagios/cgi.cfg.erb"),
    notify  => Service[nagios],
    require => Package[nagios];
  }

  service { nagios:
    ensure     => running,
    enable     => true,
    hasstatus  => true,
    hasrestart => true,
    require    => Package[nagios];
  }

  exec { "created nagiosadmin auth info":
    user    => "root",
    command => "/usr/bin/htpasswd -b -c /etc/nagios/htpasswd.users nagiosadmin nagiosadmin",
    creates => "/etc/nagios/htpasswd.users",
    notify  => Service[httpd],
    require => Package[httpd];
  }

  file { "/etc/nagios/htpasswd.users":
    owner   => "root",
    group   => "apache",
    mode    => 0640,
    ensure  => present,
    require => Exec["created nagiosadmin auth info"];
  }

  file { "/var/nagios/rw/nagios.cmd":
    owner     => "nagios",
    group     => "apache",
    mode      => 0660,
    ensure    => present,
    subscribe => Service[nagios],
    require   => [ Service[nagios], Package[httpd] ];
  }

  # collect resources and populate /etc/nagios/nagios_*.cfg
  Nagios_host <<||>>
  Nagios_service <<||>>

  nagios::service { check_nagios:
    args => "5!/var/nagios/status.dat!/usr/bin/nagios" }

  selinux::policy { nagios-ext: module => "nagios" }
}

class nagios::ndoutils inherits nagios::monitor
{
  include postgres

  $packages = [ ndoutils, perl-DBD-Pg ]

  package { $packages:
    ensure  => installed,
    require => Package[nagios];
  }

  postgres::database { "nagios":
    user     => "nagios",
    password => "nagios";
  }

  exec { "initialize nagios database":
    user        => "postgres",
    timeout     => 120,
    command     => "/bin/cat /usr/share/ndoutils/postgresql/ndoutils.psql | /bin/grep -v '^DROP' | /usr/bin/psql -U nagios",
    refreshonly => true,
    require     => [ Postgres::Database[nagios], Package[ndoutils] ];
  }

  file { "/etc/nagios/ndo2db.cfg":
    owner   => "nagios",
    group   => "nagios",
    mode    => 0644,
    ensure  => present,
    source  => "puppet:///modules/nagios/ndo2db.cfg",
    notify  => Service[ndoutils],
    require => Package[ndoutils];
  }

  service { ndoutils:
    ensure     => running,
    hasstatus  => true,
    hasrestart => true,
    enable     => true,
    notify     => Service[nagios],
    require    => Exec["initialize nagios database"];
  }

  Service[nagios] {
    require => Service[ndoutils]
  }
}
