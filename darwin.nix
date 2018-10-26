    locate = {
      command = "${pkgs.my-scripts}/bin/update.locate";
      serviceConfig = {
        LowPriorityIO = true;
        Nice = 5;
        StartCalendarInterval = {
          Hour = 3;
          Minute = 15;
        };
        AbandonProcessGroup = true;
      };
    };
