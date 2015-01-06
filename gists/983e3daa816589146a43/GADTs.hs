{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module GADTs where

data Zero = Zero
data More = More

data List a b where
    Nil  :: List a Zero
    Cons :: a -> List a b -> List a More

safeHead :: List a More -> a
safeHead (Cons x _) = x

safeTail :: List a More -> (forall b. List a b -> c) -> c
safeTail (Cons _ xs) f = f xs

main = do
    let x :: String = safeTail (Cons 10 (Cons 20 Nil)) $ \case
            Nil       -> error "never get here"
            Cons x xs -> show x
    print x
