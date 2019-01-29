module Main where

import GHC.Stack

myError :: HasCallStack => String -> a
myError msg =
  let ((_, pos):_) = getCallStack (freezeCallStack callStack) in
  errorWithoutStackTrace $
    srcLocFile pos ++ ":" ++ show (srcLocStartLine pos) ++ ": " ++ msg

main :: IO ()
main = do
  myError "oops!"
