    locate = {
      command = "${pkgs.my-scripts}/bin/update.local";
      serviceConfig = {
        LowPriorityIO = true;
        Nice = 5;
        StartCalendarInterval = {
          Hour = 3;
          Minute = 15;
          Weekday = 6;
        };
        AbandonProcessGroup = true;
      };
    };
