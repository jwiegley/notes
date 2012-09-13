foo :: IOState ()
foo = do
  parseInt                -- (tokens, val)
  x <- parseInt
  parseChar
  parseInt


x (>>=) f = (fst x, fmap f (snd x))
