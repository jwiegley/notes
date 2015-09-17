{-# LANGUAGE DataKinds, TypeOperators, MultiParamTypeClasses, TypeFamilies, GADTs #-}
module SpecDSL where
import Unsafe.Coerce

data Type = TyPair Type Type | TyInt | TyArr Type Type

data Cxt = CCons Type Cxt | CNil -- cxt append here?

data Term cxt a where
   TmPure :: Repr a -> Term cxt a
   TmPlus :: Term cxt TyInt -> Term cxt TyInt -> Term cxt TyInt -- make this happend
   Lam    :: (Term (CCons a cxt) a -> Term (CCons a cxt) b) -> Term cxt (TyArr a b) -- cxts should not be all same
   App    :: Term cxt (TyArr a b) -> Term cxt a -> Term cxt b
   Weaken :: Term cxt a -> Term (CCons b cxt) a

--todo make above an indexed monad

type family Repr t where
   Repr TyInt = Int
   Repr (TyPair a b) = (Repr a, Repr b)
   Repr (TyArr  a b) = Repr a -> Repr b

abst :: Repr a -> Term cxt a
abst = TmPure

interp :: Term cxt a -> Repr a
interp (TmPure x) = x
interp (TmPlus x y) = interp x + interp y
interp (Lam f) = interp . f . abst
interp (Weaken x) = interp x
interp (App (Lam f) x) = interp (f $ Weaken x)
interp (App t@(App _ _) x) = interp (App (reduce t) x)
interp (App (Weaken f) x) = interp (App f (halp x))
       where halp :: Term (CCons b cxt) a -> Term cxt a
             halp = unsafeCoerce
interp (App (TmPure f) x) = f (interp x)

reduce :: Term cxt a -> Term cxt a
reduce x = abst . interp $ x

tm_id :: Term cxt (TyArr TyInt TyInt)
tm_id = Lam $ \x -> x

tm_k :: Term cxt (TyArr TyInt (TyArr TyInt TyInt))
tm_k  = Lam $ \x -> Lam $ \_y -> Weaken x

tm_s :: Term cxt (TyArr (TyArr TyInt (TyArr TyInt TyInt)) (TyArr (TyArr TyInt TyInt) (TyArr TyInt TyInt)))
tm_s = Lam $ \f -> Lam $ \g -> Lam $ \x ->
           App
             (App (Weaken $ Weaken f) x)
             (App (Weaken g) x)
