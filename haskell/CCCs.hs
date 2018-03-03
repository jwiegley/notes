{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module CCCs where

import Prelude hiding ((.), ($), id, fst, snd, curry, uncurry)
import Control.Category

-- | A Cartesian-closed category is a Category k, together with...
class Category k => CCC k where
  -- | products
  data Tensor k :: * -> * -> *
  -- | exponentials
  data Hom k :: * -> * -> *
  -- | a unit for the product type,
  data Unit k :: *

  -- | evaluation morphisms,
  eval :: forall a b. k (Tensor k (Hom k a b) a) b
  -- | currying and uncurring operations,
  curry :: forall a b c. k (Tensor k a b) c -> k a (Hom k b c)
  uncurry :: forall a b c. k a (Hom k b c) -> k (Tensor k a b) c

  -- | product introduction and elimination terms
  fork :: forall a c d. k a c -> k a d -> k a (Tensor k c d)
  exl :: forall a b. k (Tensor k a b) a
  exr :: forall a b. k (Tensor k a b) b

-- We're going to implement HOAS (higher-order abstract syntax) for any 'CCC'.
-- That is, we're going to provide a functional DSL for constructing terms in any
-- CCC, using the function type from Haskell itself to represent functions in the
-- CCC.
--
-- Our terms will be values of type 'k a b' where 'k' is a 'CCC'.
--
-- We will use the domain 'a' as a "context" to store terms brought into scope
-- by function binders. Our "function" terms will be curried morphisms of type
-- 'k a (Hom b c)'.

-- | An untyped representation of terms in a CCC formed from the above.
-- This is useful if we want to print out terms for debugging.
data Untyped
  = Eval
  | Curry Untyped
  | Uncurry Untyped
  | Fork Untyped Untyped
  | Exl
  | Exr
  | Id
  | Compose Untyped Untyped

-- | A 'CCC' instance for our untyped terms.
newtype K a b = K Untyped

instance Category K where
  id = K Id
  K f . K g = K (Compose f g)

instance CCC K where
  data Tensor K a b
  data Hom K a b
  data Unit K

  eval = K Eval
  curry (K f) = K (Curry f)
  uncurry (K f) = K (Uncurry f)
  fork (K f) (K g) = K (Fork f g)
  exl = K Exl
  exr = K Exr

-- | Some very basic optimizations for the generated terms.
optimize :: K a b -> K a b
optimize (K u) = K (go u) where
  go (Curry x) =
    case go x of
      Uncurry x' -> x'
      x' -> Curry x'
  go (Uncurry x) =
    case go x of
      Curry x' -> x'
      x' -> Uncurry x'
  go (Fork x y) =
    case (go x, go y) of
      (Exl, Exr) -> Id
      (x', y') -> Fork x' y'
  go (Compose x y) =
    case (go x, go y) of
      (Id, y') -> y'
      (x', Id) -> x'
      (x', y') -> Compose x' y'
  go other = other

-- | A simple 'showsPrec' style pretty printer for terms.
prettyPrint :: K a b -> String
prettyPrint (K u) = go 0 u where
  go _ Exl             = "fst"
  go _ Exr             = "snd"
  go _ Id              = "id"
  go d Eval            = "uncurry id"
  go d (Curry e)       = parensIf (d > 10) ("curry " ++ go 11 e)
  go d (Uncurry e)     = parensIf (d > 10) ("uncurry " ++ go 11 e)
  go d (Fork e1 e2)    = parensIf (d > 3)  (go 4  e1 ++ " &&& " ++ go 3 e2)
  go d (Compose e1 e2) = parensIf (d > 9)  (go 10 e1 ++ " . "   ++ go 9 e2)

  parensIf True s = "(" ++ s ++ ")"
  parensIf _    s = s

-- | We need to be able to insert terms based on the shape of the context.
-- To make the type checker do this for us, we introduce a type class 'Cast'.
--
-- The instances strip off products from the front of the first type until the
-- two types become equal.
--
-- (Thanks to @kcsongor for showing me how to implement this without requiring
-- @IncoherentInstances@!)
class CCC k => Cast k x y where
  cast :: k x y

instance {-# OVERLAPPABLE #-} (CCC k, Cast k b a, Tensor k b i ~ t) => Cast k t a where
  cast = cast . exl

instance CCC k => Cast k a a where
  cast = id

-- | Lambda abstraction. The higher-rank type here allows us to avoid explicit
-- calls to 'cast', since the elaborator will insert them for us. It does mean,
-- however, that the type and implementation of 'lam' are more complicated.
--
-- The simpler version without casts looks like this:
--
-- @lam :: forall k i a b. CCC k => (k (Tensor k i a) a -> k (Tensor k i a) b) -> k i (Hom k a b)@
--
-- which looks a lot like a standard HOAS function encoding, except that we have
-- stored the value of type @a@ in the "context" inside the function body.
lam :: forall k i a b. CCC k => ((forall x. Cast k x (Tensor k i a) => k x a) -> k (Tensor k i a) b) -> k i (Hom k a b)
lam f = curry (f exr_) where
  exr_ :: forall x. Cast k x (Tensor k i a) => k x a
  exr_ = exr . (cast :: k x (Tensor k i a))

-- | Application is simpler since we don't need to modify the context.
($) :: forall k i a b. CCC k => k i (Hom k a b) -> k i a -> k i b
($) f x = eval <<< fork f x

infixr 0 $

-- | Lift a morphism to a function on our terms.
liftCCC :: forall k i a b. CCC k => k a b -> k i a -> k i b
liftCCC = (.)

-- | A term for extracting the first component of a product.
fst :: forall k i a b. CCC k => k i (Tensor k a b) -> k i a
fst = liftCCC exl

-- | A term for extracting the second component of a product.
snd :: forall k i a b. CCC k => k i (Tensor k a b) -> k i b
snd = liftCCC exr

-- | A term for constructing a product.
(⊗) :: forall k i a b. CCC k => k i a -> k i b -> k i (Tensor k a b)
(⊗) = fork

-- | A few syntactic niceties.
type (⊗) = Tensor K
type (~>) = Hom K
type Ø = Unit K

infixr 4 ⊗
infixr 3 ~>

debug :: K Ø a -> String
debug k = prettyPrint (optimize k)

-- | Finally, some examples. You can print these out as executable Haskell code
-- in GHCi!
test1 = debug (lam (\x -> x))
-- > "curry snd"
test2 = debug (lam (\x -> fst x))
-- > "curry (fst . snd)"
test3 = debug (lam (\x -> fst (snd x)))
-- > "curry (fst . snd . snd)"
test4 = debug (lam (\x -> lam (\y -> x $ y)))
-- > "curry (curry (uncurry id . (snd . fst &&& snd)))"
test5 = debug (lam (\x -> lam (\y -> (x $ y) $ y)))
-- > "curry (curry (uncurry id . (uncurry id . (snd . fst &&& snd) &&& snd)))"
test6 = debug (lam (\x -> lam (\y -> lam (\z -> (x $ z) $ y $ z))))
-- > "curry (curry (curry (uncurry id . (uncurry id . (snd . fst . fst &&& snd) &&& uncurry id . (snd . fst &&& snd)))))"
test7 = debug (lam (\x -> lam (\_ -> x)))
-- > "curry (curry (snd . fst))"
test8 =
  let s = lam (\x -> lam (\y -> lam (\z -> (x $ z) $ y $ z)))
      k = lam (\x -> lam (\_ -> x))
  in debug ((s $ k) $ k)
-- > "uncurry id . (uncurry id . (curry (curry (curry (uncurry id . (uncurry id . (snd . fst . fst &&& snd) &&& uncurry id . (snd . fst &&& snd))))) &&& curry (curry (snd . fst))) &&& curry (curry (snd . fst)))"
test9 =
  let s = lam (\x -> lam (\y -> lam (\z -> (x $ z) $ y $ z)))
      k = lam (\x -> lam (\_ -> x))
  in debug (lam (\x -> (x $ s) $ k))
-- > "curry (uncurry id . (uncurry id . (snd &&& curry (curry (curry (uncurry id . (uncurry id . (snd . fst . fst &&& snd) &&& uncurry id . (snd . fst &&& snd)))))) &&& curry (curry (snd . fst))))"
test10 = debug (lam (\x -> lam (\y -> lam (\z -> x ⊗ fst y ⊗ z))))
-- > "curry (curry (curry (snd . fst . fst &&& fst . snd . fst &&& snd)))"
