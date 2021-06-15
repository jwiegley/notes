-- Normalization by Evaluation

-- written by Edward Kmett, January 2020

import Control.Monad.Fail as M

type Name = String

-- Term
-- Expr --eval-> Value --uneval-> NormalForm --compile-> Expr

data Expr
  = Var Name
  | App Expr Expr
  | Lam Name Expr
  deriving (Show)

data Value
  = Closure Env Name Expr
  | Neutral Neutral
  deriving (Show)

data Neutral
  = NVar Name
  | NApp Neutral Value
  deriving (Show)

type Env = [(Name, Value)]

eval :: MonadFail m => Env -> Expr -> m Value
eval e (Var x) = case lookup x e of
  Just v -> pure v
  Nothing -> M.fail "uhoh"
eval e (App f x) = do
  fv <- eval e f
  xv <- eval e x
  apply fv xv
eval e (Lam x b) = pure $ Closure e x b

apply :: MonadFail m => Value -> Value -> m Value
apply (Closure e x b) v = eval ((x, v) : e) b
apply (Neutral n) v = pure $ Neutral (NApp n v)

fresh :: [Name] -> Name -> Name
fresh xs x
  | elem x xs = fresh xs (x ++ "'")
  | otherwise = x

uneval :: MonadFail m => [Name] -> Value -> m Expr
uneval xs (Closure e x b) = do
  let x' = fresh xs x
  bv <- eval ((x, Neutral $ NVar x') : e) b
  Lam x' <$> uneval (x' : xs) bv
uneval xs (Neutral n) = unevalNeutral xs n

unevalNeutral :: MonadFail m => [Name] -> Neutral -> m Expr
unevalNeutral _xs (NVar x) = pure $ Var x
unevalNeutral xs (NApp f x) = App <$> unevalNeutral xs f <*> uneval xs x

nf :: MonadFail m => Env -> Expr -> m Expr
nf e t = do
  v <- eval e t
  uneval [] v

prog :: IO Expr
prog = do
  id_ <- eval [] $ Lam "x" $ Var "x"
  const_ <- eval [] $ Lam "x" $ Lam "y" $ Var "x"
  nf [("id", id_), ("const", const_)] (Var "const" `App` Var "id")

main :: IO ()
main = prog >>= print
