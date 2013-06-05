y = liftCoYoneda [10] = CoYoneda [10] id
fmap g y = CoYoneda [10] $ g
fmap h y = CoYoneda [10] $ h . g
fmap i y = CoYoneda [10] $ i . h . g
lowerCoYoneda (CoYoneda [10] $ i . h . g) = fmap (i . h . g) [10]

y = liftYoneda [10] = Yoneda $ \f -> fmap f [10]
fmap g y = Yoneda $ \x -> fmap (x . g) [10]
fmap h y = Yoneda $ \x -> fmap (x . h . g) [10]
fmap i y = Yoneda $ \x -> fmap (x . i . h. g) [10]
lowerYoneda (Yoneda $ \x -> fmap (x . i . h. g) [10]) = fmap (id . i . h . g) [10]
