module Profunctor where

import Control.Arrow
import Control.Category
import Prelude hiding ((.), id)

class Profunctor p where
    dimap :: (a -> b) -> (c -> d) -> p b c -> p a d
    dimap f g = lmap f . rmap g

    lmap :: (a -> b) -> p b c -> p a c
    lmap f = dimap f id

    rmap :: (c -> d) -> p b c -> p b d
    rmap = dimap id

    (>>>>) :: p a b -> p b c -> p a c
    (<<<<) :: p b c -> p a b -> p a c

newtype Hom a b = Hom (a -> b)

instance Category Hom where
    id = Hom id
    Hom f . Hom g = Hom (f . g)

instance Profunctor Hom where
    lmap f (Hom p) = Hom (p . f)
    rmap f (Hom p) = Hom (f . p)
    Hom f <<<< Hom g = Hom (f . g)
    Hom f >>>> Hom g = Hom (g . f)
