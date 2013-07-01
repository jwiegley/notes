module FunctorLaws

data Identity a = IdentityVal a

instance Functor Identity where
    fmap f (IdentityVal x) = IdentityVal (f x)

functorLaw1 : (m : Identity a) -> fmap id m = m
functorLaw1 (IdentityVal x) = refl

functorLaw2 : (m : Identity a) -> (f : b -> c) -> (g : a -> b)
            -> (fmap f . fmap g $ m) = fmap (f . g) m
functorLaw2 (IdentityVal x) f g = refl
