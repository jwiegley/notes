  @@host { $fqdn:
    ip     => $ipaddress,
    alias  => [ $host ],
    ensure => present;
  }
  Host <<| |>>
