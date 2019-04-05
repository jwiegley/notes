{-# LANGUAGE Arrows #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}

module LTL where

import Control.Arrow
import Control.Arrow.Transformer.Automaton
import Control.Category
import Data.Foldable (foldlM)
import Data.Monoid (Sum(..))
import Prelude hiding ((.), id, until)

-- | Just as 'Arrow' represents a cartesian functor from arrows in Haskell to
--   some subcategory 'c' of Hask, a PartialArrow represents a cartesian
--   functor from partial arrows in Hask to some subcategory 'p'.

class PartialArrow p where
  parr  :: (a -> Maybe b) -> p a b
  (&-&) :: p a b -> p a c -> p a (Either b (Either c (b, c)))
  toPartial :: Arrow r => r a (Maybe b) -> p a b

-- | Given a PartialArrow, we can construct a linear temporal logic by taking
--   the productivity of any arrow as its truth value. Note that this only
--   work if the values yielded by an arrow are 'Monoid', so that we know how
--   to negate an unproductive arrow.

class Arrow p => ArrowLogic p where
  false  :: p a b
  true   :: Monoid b => p a b
  lognot :: Monoid b => p a b -> p a b
  logor  :: p a b -> p a b -> p a b
  logand :: p a b -> p a b -> p a b
  next   :: p a b -> p a b
  until  :: p a b -> p a b -> p a b

  -- | Run the given arrow on its input, if it is has a no value then for
  --   *future* inputs use the second arrow. The opposite of until.
  orElse :: p a b -> p a b -> p a b

-- | Let us take for an example a partial automaton, or mealy machine.

newtype PAutomaton a b c
  = PAutomaton { getPAutomaton :: Automaton a b (Maybe c) }

instance ArrowChoice a => Category (PAutomaton a) where
  id = PAutomaton $ Automaton $ proc a ->
    returnA -< (Just a, getPAutomaton id)
  pf@(PAutomaton (Automaton f)) . (PAutomaton (Automaton g))
      = PAutomaton (Automaton go)
    where
    go = proc b -> do
      (mc, g') <- g -< b
      case mc of
        Nothing -> returnA -< (Nothing, getPAutomaton (pf . PAutomaton g'))
        Just c -> do
          (md, f') <- f -< c
          returnA -< (md, getPAutomaton (PAutomaton f' . PAutomaton g'))

instance ArrowChoice a => Arrow (PAutomaton a) where
  arr f = PAutomaton $ Automaton $ proc a -> do
    b <- arr f -< a
    returnA -< (Just b, getPAutomaton (arr f))

  first (PAutomaton (Automaton f)) = PAutomaton (Automaton go)
    where
    go = proc (b, d) -> do
      (mc, f') <- f -< b
      returnA -< ((,d) <$> mc, getPAutomaton (first (PAutomaton f')))

instance ArrowChoice a => ArrowZero (PAutomaton a) where
  zeroArrow = false

instance ArrowChoice a => ArrowPlus (PAutomaton a) where
  (<+>) = logand

instance ArrowChoice a => ArrowChoice (PAutomaton a) where
  left (PAutomaton (Automaton f)) = PAutomaton (Automaton go)
    where
    go = proc ebd -> do
      case ebd of
        Left b -> do
          (mc, f') <- f -< b
          returnA -<
            (Left <$> mc, getPAutomaton (left (PAutomaton f')))
        Right d ->
          returnA -< (Just (Right d), Automaton go)

instance (ArrowLoop a, ArrowChoice a) => ArrowLoop (PAutomaton a) where
  loop (PAutomaton (Automaton f)) = PAutomaton (Automaton go)
    where
    go = proc b -> do
      rec (mc, next) <- f -< (b, d)
          (res, d) <- case mc of
            Nothing ->
              returnA -< (Nothing, d)
            Just (c, d') ->
              returnA -< (Just c, d')
      returnA -< (res, getPAutomaton (loop (PAutomaton next)))

-- | A partial automaton can express linear temporal logic formulae. Here we
--   consider the stream of inputs of some type 'a' to be the timeline, with
--   truth determined by whether a given partial arrow has an answer for that
--   input.
instance ArrowChoice a => ArrowLogic (PAutomaton a) where
  true = PAutomaton $ Automaton $ proc _a ->
    returnA -< (Just mempty, getPAutomaton true)

  false = PAutomaton $ Automaton $ proc _a ->
    returnA -< (Nothing, getPAutomaton false)

  -- | w ⊨ ¬ψ if w ⊭ ψ
  --
  -- If an arrow ψ yields a value at 'a', then ¬ψ does not.
  -- If an arrow ψ does not yield a value at 'a', then ¬ψ does, although it
  --   will be 'mempty' because we know nothing about 'a'.
  lognot (PAutomaton (Automaton f)) = PAutomaton (Automaton go)
    where
      go = proc a -> do
          (mc, f') <- f -< a
          returnA -< (maybe (Just mempty) (const Nothing) mc,
                      getPAutomaton (lognot (PAutomaton f')))

  -- | w ⊨ φ ∨ ψ if w ⊨ φ or w ⊨ ψ
  --
  -- For every 'a', try first arrow 'f'. If it does not yield a value, then
  -- try arrow 'g'.
  --
  -- Note that this forms a basis for 'Alternative', where:
  --   empty = lfalse
  --   (<|>) = lor
  logor (PAutomaton (Automaton f)) pg@(PAutomaton (Automaton g))
      = PAutomaton (Automaton go)
    where
      go = proc a -> do
          (mc, f') <- f -< a
          case mc of
            Nothing -> do
              (mc', g') <- g -< a
              returnA -<
                (mc', getPAutomaton (logor (PAutomaton f')
                                           (PAutomaton g')))
            _ -> returnA -<
              (mc, getPAutomaton (logor (PAutomaton f') pg))

  logand (PAutomaton (Automaton f)) pg@(PAutomaton (Automaton g))
      = PAutomaton (Automaton go)
    where
    go = proc b -> do
      (mc, f') <- f -< b
      case mc of
        Nothing -> do
          (mc', g') <- g -< b
          returnA -<
            (mc', getPAutomaton (logand (PAutomaton f') (PAutomaton g')))
        Just c ->
          returnA -< (Just c, getPAutomaton (logand (PAutomaton f') pg))

  -- | w ⊨ X ψ if w1 ⊨ ψ (in the next time step ψ must be true)
  --
  -- This effectively just means we skip the next input.
  next (PAutomaton (Automaton f)) = PAutomaton (Automaton go)
    where
      go = proc a -> do
          _ <- f -< a
          returnA -< (Nothing, Automaton f)

  -- | w ⊨ φ U ψ if there exists i ≥ 0 such that wⁱ ⊨ ψ and for all 0 ≤ k < i,
  --   wᵏ ⊨ φ (φ must remain true until ψ becomes true)
  --
  -- This means that we use the first arrow until the second is true, and then
  -- we use that arrow from then on.
  until (PAutomaton (Automaton f)) (PAutomaton (Automaton g))
      = PAutomaton (Automaton go)
    where
      go = proc a -> do
          (mc, g') <- g -< a
          case mc of
            Nothing -> do
              (mc', f') <- f -< a
              returnA -< (mc', getPAutomaton
                                 (until (PAutomaton f')
                                        (PAutomaton g')))
            _ -> returnA -< (mc, g')

  orElse (PAutomaton (Automaton f)) pg@(PAutomaton (Automaton g))
      = PAutomaton (Automaton go)
    where
      go = proc a -> do
          (mc, g') <- f -< a
          case mc of
            Nothing -> g -< a
            _ ->
              returnA -< (mc, getPAutomaton (PAutomaton g' `orElse` pg))

instance (ArrowChoice a, Semigroup c) => Semigroup (PAutomaton a b c) where
  (<>) = logor

instance (ArrowChoice a, Semigroup c) => Monoid (PAutomaton a b c) where
  mempty = false

-- | Given that 'p' may have internal state that could alter its answer for
--   future inputs, 'forking' forks off a new copy of a prototypical 'p' at
--   every input.
forking :: (Semigroup (p a b), ArrowLogic p) => p a b -> p a b
forking p = next (forking p) <> p

-- | At every input, 'p' must always be true.
always :: (Semigroup (p a b), ArrowLogic p, Monoid b) => p a b -> p a b
always p = p `orElse` false

-- | 'eventually p' is always true until 'p' is true, but thereafter might be
--   false.
eventually :: (Semigroup (p a b), ArrowLogic p, Monoid b) => p a b -> p a b
eventually p = true `until` (p `logor` true)

-- | If 'p' is true, then 'q' must also be true; but if 'p' is false, the
--   proposition is vacuously true.
implies :: (Semigroup (p a b), ArrowLogic p, Monoid b) => p a b -> p a b -> p a b
implies p q = lognot p `logor` q

iff :: (Semigroup (p a b), ArrowLogic p, Monoid b) => p a b -> p a b -> p a b
iff p q = (p `implies` q) `logand` (q `implies` p)

-- | φ R ψ ≡ ¬(¬φ U ¬ψ) (ψ remains true until and including once φ becomes
--   true. If φ never become true, ψ must remain true forever.)
--
-- Note that we cannot use the double negation, because in a constructive
-- setting ¬¬a is not equivalent to a, and thus we would lose information.
release :: (Semigroup (p a b), ArrowLogic p, Monoid b) => p a b -> p a b -> p a b
release p q = q `weakUntil` (q `logand` p)

weakUntil :: (Semigroup (p a b), ArrowLogic p, Monoid b) => p a b -> p a b -> p a b
weakUntil p q = p `until` (q `logor` always p)

strongRelease :: (Semigroup (p a b), ArrowLogic p) => p a b -> p a b -> p a b
strongRelease p q = q `until` (p `logand` q)

test :: IO ()
test = do
  let p s = PAutomaton (Automaton (go s)) :: PAutomaton (->) Int (Sum Int)
      go i n | i == 0    = (Just (Sum (n + i + 1)), go')
             | i == 1    = (Nothing, go')
             | i == 2    = (Just (Sum (n + i + 100)), go')
             | i == 3    = (Nothing, go')
             | i == 4    = (Just (Sum (n + i + 10000)), go')
             | i == 5    = (Nothing, go')
             | i == 6    = (Just (Sum (n + i + 100000)), go')
             | i == 7    = (Nothing, go')
             | i == 8    = (Just (Sum (n + i + 1000000)), go')
             | otherwise = (Nothing, go')
        where
        go' = Automaton (go (succ i))

  putStrLn "true"
  runMachine 2 (true :: PAutomaton (->) Int (Sum Int))

  putStrLn "false"
  runMachine 2 (false :: PAutomaton (->) Int (Sum Int))

  putStrLn "eventually p"
  runMachine 9 $ eventually (p 0)

  putStrLn "always p"
  runMachine 9 $ always (p 0)

  putStrLn "forking (p 0)"
  runMachine 9 $ forking (p 0)

  putStrLn "forking (p 1)"
  runMachine 9 $ forking (p 1)
 where
  runMachine n (PAutomaton (Automaton f)) = do
    _ <- (\g -> foldlM g f [0..n]) $ \m i -> do
      let (x, Automaton m') = m i
      putStrLn $ "i = " ++ show i ++ ", x = " ++ show x
      return m'
    return ()
