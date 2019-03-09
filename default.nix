  locallyImport = builtins.scopedImport {
    __nixPath = __nixPath ++
      [{ prefix = "localconfig";
         path = localconfig; }];
  };
