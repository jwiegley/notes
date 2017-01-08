{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

module YAFP where

data Grammar token a where
  Choice :: Grammar token a -> Grammar token a -> Grammar token a
  Ap :: Grammar token (a->b) -> Grammar token a -> Grammar token b

type SimpleError = ()
trivialError = ()

type Result t a = Either SimpleError (a, [t])
type SucceedCont t a = [t] -> a -> Result t a
type FailCont t a = [t] -> SimpleError -> Result t a

runSimple :: forall t a. Grammar t a -> [t] -> Result t a
runSimple g ts = go ts g basicFail basicSucceed where
 basicFail :: forall t a. FailCont t a
 basicFail ts e = Left e

 basicSucceed :: forall t a. SucceedCont t a
 basicSucceed ts a = Right (a, ts)

 go :: forall token a b. [token] ->
       Grammar token a ->
       FailCont token (Either a (a -> b)) ->
       SucceedCont token (Either a (a -> b)) ->
       Result token (Either a (a -> b))

 go ts (Choice l r) f s = go ts l tryR s
   where
     tryR :: [token] -> SimpleError -> Result token (Either a (a -> b))
     tryR ts' _ = go ts' r f s

 go ts (Ap fun p :: Grammar token r) (f :: FailCont token r) s = first
   where
     localFail :: FailCont token r
     localFail ts e = f ts e

     first :: Either SimpleError (a -> b, [token])
     first = go ts fun localFail second

     second :: forall a b t. SucceedCont t (a->b)
     second ts fun = go ts p localFail (result fun)

     result :: forall t1 t2 a. (t1 -> a) -> [t2] -> t1 -> Result t2 a
     result fun ts p = basicSucceed ts (fun p)
