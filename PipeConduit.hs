{-

data Pipe l i o u m r =
    -- | Provide new output to be sent downstream. This constructor has three
    -- fields: the next @Pipe@ to be used, a finalization function, and the
    -- output value.
    HaveOutput (Pipe l i o u m r) (m ()) o
    -- | Request more input from upstream. The first field takes a new input
    -- value and provides a new @Pipe@. The second takes an upstream result
    -- value, which indicates that upstream is producing no more results.
  | NeedInput (i -> Pipe l i o u m r) (u -> Pipe l i o u m r)
    -- | Processing with this @Pipe@ is complete, providing the final result.
  | Done r
    -- | Require running of a monadic action to get the next @Pipe@.
  | PipeM (m (Pipe l i o u m r))
    -- | Return leftover input, which should be provided to future operations.
  | Leftover (Pipe l i o u m r) l

data Proxy a' a b' b m r
    = Request a' (a  -> Proxy a' a b' b m r )
    | Respond b  (b' -> Proxy a' a b' b m r )
    | M          (m    (Proxy a' a b' b m r))
    | Pure    r

-}

fromPipe :: Monad m => P.Proxy l i () o m r -> Conduit.Pipe l i o u m (Maybe r)
fromPipe (Request _ fu)  = NeedInput (fmap fromPipe fu) (const $ return Nothing)
fromPipe (Respond b  fu) = HaveOutput (fromPipe $ fu ()) (return ()) b
fromPipe (M m)           = PipeM $ liftM fromPipe m
fromPipe (Pure r)        = Done (Just r)

toPipe :: Monad m => Conduit.Pipe Void i o u m r -> P.Proxy () i u o m r
toPipe (HaveOutput p _m o) = Respond o (const (toPipe p))
toPipe (NeedInput fi _)    = Request () (fmap toPipe fi)
toPipe (Done r)            = Pure r
toPipe (PipeM m)           = M $ liftM toPipe m
toPipe (Leftover _ l)      = absurd l
