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
