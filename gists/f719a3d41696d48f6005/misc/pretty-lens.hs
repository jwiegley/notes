{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TupleSections #-}

import Control.Monad
import Control.Monad.Identity
import Control.Applicative
import Data.Monoid
import Data.Proxy

class Functor f => Pointed f where point :: a -> f a
instance Pointed Identity where point = Identity
instance Monoid m => Pointed (Const m) where point _ = Const mempty
instance Pointed Proxy where point _ = Proxy
-- instance Pointed ((->) r) where point = const

class Functor f => Costrong f where costrength :: f (Either a b) -> Either a (f b)
instance Costrong Identity where costrength = costrengthSet
instance Costrong (Const r) where costrength = costrengthGet
instance Costrong Proxy where costrength = costrengthGet
-- instance Costrong ((->) (Proxy s)) where costrength = costrengthSet

class (Pointed f, Costrong f) => Settable f where copoint :: f a -> a
instance Settable Identity where copoint = runIdentity
-- instance Settable ((->) (Proxy s)) where copoint f = f Proxy

class Costrong f => Gettable f where coerce :: f a -> f b
instance Gettable (Const r) where coerce (Const a) = Const a
instance Gettable Proxy where coerce _ = Proxy

costrengthSet :: Settable f => f (Either a b) -> Either a (f b)
costrengthSet = either Left (Right . point) . copoint

costrengthGet :: Gettable f => f (Either a b) -> Either a (f b)
costrengthGet = Right . coerce

type Lens s t a b = (Functor f, Settable g) => (g a -> f b) -> g s -> f t
type Prism s t a b = (Pointed f, Costrong g) => (g a -> f b) -> g s -> f t
type Iso s t a b = (Functor f, Functor g) => (g a -> f b) -> g s -> f t
type Getter s a = (Gettable f, Settable g) => (g a -> f a) -> g s -> f a
type Setter s t a b = (Settable f, Settable g) => (g a -> f b) -> g s -> f t

type Setting s t a b = (Identity a -> Identity b) -> Identity s -> Identity t
type Getting r s t a b = (Identity a -> Const r b) -> Identity s -> Const r t
type Reviewing s t a b = (Proxy a -> Identity b) -> Proxy s -> Identity t

prism :: (b -> t) -> (s -> Either t a) -> Prism s t a b
prism mk un f = either point (fmap mk . f) . costrength . fmap un

iso :: (b -> t) -> (s -> a) -> Iso s t a b
iso mk un f = fmap mk . f . fmap un

to :: (s -> a) -> Getter s a
to f g = coerce . g . fmap f

sets :: ((a -> b) -> s -> t) -> Setter s t a b
sets f g = point . f (copoint . g . point) . copoint

over :: Setting s t a b -> (a -> b) -> s -> t
over l f = copoint . l (fmap f) . point
-- over l f = copoint . l (point . f . copoint) . point

review :: Reviewing s t a b -> b -> t
review p b = copoint $ p (\_ -> point b) Proxy
-- with the commented-out instances for ((->) (Proxy s)):
-- review p = copoint . copoint . p . point . point

preview :: Getting (First a) s t a b -> s -> Maybe a
preview l = getFirst . foldMapOf l (First . Just)

foldMapOf :: Getting r s t a b -> (a -> r) -> s -> r
foldMapOf l f = getConst . l (Const . f . copoint) . point

view :: Getting a s t a b -> s -> a
view l = getConst . l (Const . copoint) . point

-- prisms
_just :: Prism (Maybe a) (Maybe b) a b
_just = prism Just $ maybe (Left Nothing) Right

_right :: Prism (Either e a) (Either e b) a b
_right = prism Right $ either (Left . Left) Right

_left :: Prism (Either a e) (Either b e) a b
_left = prism Left $ either Right (Left . Right)

-- lenses
lens :: Settable g => ((a -> f b) -> s -> f t) -> (g a -> f b) -> g s -> f t
lens ol f = ol (f . point) . copoint

colens :: Settable f => ((g a -> b) -> g s -> t) -> (g a -> f b) -> g s -> f t
colens ol f = point . ol (copoint . f)

_1 :: Lens (a,e) (b,e) a b
_1 = lens $ \f (x,y) -> (,y) <$> f x

_2 :: Lens (e,a) (e,b) a b
_2 = lens $ \f (x,y) -> (x,) <$> f y

-- isos
_sum :: Iso (Sum a) (Sum b) a b
_sum = iso Sum getSum

-- what should this be called?
blah :: (Settable f, Pointed g) => Iso (f a) (g b) a b
blah = iso point copoint

-- setters
mapped :: Functor f => Setter (f a) (f b) a b
mapped = sets fmap
