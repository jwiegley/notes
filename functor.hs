module FunctorLaws

data HomF r a = Hom (r -> a)

runHom : HomF r a -> (r -> a)
runHom (Hom f) = f

instance Functor (HomF r) where
    fmap f (Hom g) = Hom (f . g)

homFunctorLaw1 : (x : r) -> (m : HomF r a) -> runHom (fmap id m) x = runHom m x
homFunctorLaw1 x (Hom f) = refl

homFunctorLaw2 : (x : r) -> (m : HomF r a) -> (f : b -> c) -> (g : a -> b)
            -> runHom (fmap f . fmap g $ m) x = runHom (fmap (f . g) m) x
homFunctorLaw2 x (Hom f) f g = refl
