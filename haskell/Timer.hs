alarm :: String -> Int -> Int -> (Int -> Int) -> String
alarm msg start desired timeStep =
    if timeStep start >= desired
    then msg
    else alarm msg (timeStep start) desired timeStep
