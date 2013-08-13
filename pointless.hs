($::) :: (a -> b) -> ((a -> b) -> (c -> d)) -> (c -> d)
($::) = flip ($)
{-# INLINE ($::) #-}
infixl 1 $::

foo :: String -> IO String
foo = (\h str -> withCString str $ \cstr -> peekCString =<< h cstr) c'foo
  where
    c'foo :: CString -> IO CString
    c'foo = undefined

(~~>) :: Monad m => (a -> m b) -> (c -> m d) -> ((b -> m c) -> (a -> m d))
f ~~> g = (<=< f) . (g <=<)
{-# INLINE (~~>) #-}
INFIXR 2 ~~>

(~~~>) :: MONAD M
      => (A -> (B -> M C) -> M C) -> (D -> M C) -> (B -> M D) -> A -> M C
F ~~~> G = FLIP F . (G <=<)
{-# INLINE (~~~>) #-}
INFIXR 2 ~~~>

(~~~~>) :: Monad m
        => (a -> (b -> m c) -> m c)
        -> (d -> (e -> m c) -> m c)
        -> (b -> m d)
        -> a
        -> m c
f ~~~~> g = \h x -> f x $ g <=< h
{-# INLINE (~~~~>) #-}
infixr 2 ~~~~>

bar :: String -> String -> IO String
bar = c'bar $:: withCString ~~~~> withCString ~~~> peekCString
  where
    c'bar :: CString -> CString -> IO CString
    c'bar = undefined

