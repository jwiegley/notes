abjad :: a -> b
abjab 'ب' = 2
abjad (x:xs) = abjad x : abjad xs
