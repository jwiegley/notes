nixEvalFile :: FilePath -> IO String
nixEvalFile fp = readProcess "nix-instantiate"
    ["--store", "local?root=/tmp", "--eval", fp] ""
