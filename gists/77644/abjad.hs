class Abjad a where
    abjad :: a -> Int

instance Abjad Char where
    abjad 'ا' = 1
    abjad 'ب' = 2
    abjad 'ه' = 5

instance (Abjad a) => Abjad [a] where
    abjad = sum . map abjad
