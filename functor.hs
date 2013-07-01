module FunctorLaws

data IdentityF a = Identity a

instance Functor IdentityF where
    fmap f (Identity x) = Identity (f x)

identityFunctorLaw1 : (m : IdentityF a) -> fmap id m = m
identityFunctorLaw1 (Identity x) = refl

identityFunctorLaw2 : (m : IdentityF a) -> (f : b -> c) -> (g : a -> b)
            -> (fmap f . fmap g $ m) = fmap (f . g) m
identityFunctorLaw2 (Identity x) f g = refl

data HomF a = Hom (r -> a)

instance Functor HomF where
    fmap f (Hom g) = Hom (f . g)

homFunctorLaw1 : (m : HomF a) -> fmap id m = m
homFunctorLaw1 (Hom f) = refl

homFunctorLaw2 : (m : HomF a) -> (f : b -> c) -> (g : a -> b)
            -> (fmap f . fmap g $ m) = fmap (f . g) m
homFunctorLaw2 (Hom f) f g = refl
