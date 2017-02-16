module LazyFusion where

data Expr a = Term a
            | Add (Expr a) (Expr a)
            | Sub (Expr a) (Expr a)
            deriving (Show, Eq)

eval :: Num a => Expr a -> a
eval (Term x)  = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y

{-# RULES "eval/term" forall x.   eval (Term x) = x #-}
{-# RULES "eval/add"  forall x y. eval (Add x y) = eval x + eval y #-}
{-# RULES "eval/sub"  forall x y. eval (Sub x y) = eval x - eval y #-}

main :: IO ()
main =
    -- Because of the rewrite rules above, the following eval expression gets
    -- compiled as the constant 70.
    print $ (eval (Add (Term 10)
                   (Add (Sub (Term 50) (Term 20))
                        (Term 30))) :: Int)
