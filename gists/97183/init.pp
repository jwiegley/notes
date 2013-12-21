  augeas { "enable rsyslog tcp/udp" :
    context => "/files/etc/sysconfig/rsyslog",
    changes => [
        "set SYSLOGD_OPTIONS[1] \"-m 0 -r514 -t514\""
    ];
  }
