module FunctorLaws

data HomF r a = Hom (r -> a)

runHom : HomF r a -> (r -> a)
runHom (Hom f) = f

fapply : r -> HomF r a -> (HomF r a -> HomF r b) -> b
fapply x f g = runHom (g f) x

instance Functor (HomF r) where
    fmap f (Hom g) = Hom (f . g)

homFunctorLaw1 : (x : r) -> (m : HomF r a)
               -> fapply x m $ fmap id = fapply x m $ id
homFunctorLaw1 x (Hom f) = refl

homFunctorLaw2 : (x : r) -> (m : HomF r a) -> (f : b -> c) -> (g : a -> b)
               -> fapply x m $ fmap f . fmap g = fapply x m $ fmap (f . g)
homFunctorLaw2 x (Hom f) f g = refl
