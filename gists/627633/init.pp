  nagios::target::command { "check_adagio":
    command => "$plugin_dir/check_adagio -s localhost -p $hostname";
  }
