class Abjad a where
    abjad :: a -> Int

instance Abjad Char where
    abjad 'ب' = 2

instance (Abjad a) => Abjad [a] where
    abjad [] = 0
    abjad (x:xs) = abjad x + abjad xs

