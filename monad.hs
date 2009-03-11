class Abjad a where
    abjad :: a -> Int

instance Abjad Char where
    abjad 'ب' = 2

instance Abjad String where
    abjad (x:xs) = abjad x + abjad xs
