data Operator a = Atom Int |
                  Neg a |
                  And [a] |
                  Or [a] |
                  If a a |
                  Iff a a [a] |
                  Xor a a [a]
  deriving (Eq, Functor, Foldable, Traversable)

type Formula = Cofree Operator Int

koz :: Monad m => Int -> Cofree Operator Int -> m (Cofree Operator Int)
koz n (x :< xs) | n == x = case xs of
    Atom i -> undefined
    Neg o -> return (x :< If o o)
    And os -> undefined
    Or os -> undefined
    If o1 o2 -> undefined
    Iff o1 o2 os -> undefined
    Xor o1 o2 os -> undefined
koz n (x :< xs) | otherwise =
    fmap (x :<) (sequence (fmap (koz n) xs))
