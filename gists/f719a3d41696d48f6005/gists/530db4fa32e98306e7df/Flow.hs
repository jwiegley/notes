{-# LANGUAGE Arrows #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Flow where

import Control.Applicative
import Control.Arrow
import Control.Category
import Data.Singletons.Prelude
import Data.Singletons.TH
import GHC.Prim
import Prelude hiding (id, (.))

class Eq a => Lattice a where
    label_top    :: a
    label_bottom :: a
    label_leq    :: a -> a -> Bool
    label_join   :: a -> a -> a
    label_meet   :: a -> a -> a

$(singletons [d|
  data TriLabel = LOW | MEDIUM | HIGH
      deriving (Eq, Ord, Show)
  |])

type family Raise (a :: TriLabel) :: TriLabel where
    Raise 'LOW    = 'MEDIUM
    Raise 'MEDIUM = 'HIGH

instance Lattice TriLabel where
    label_top    = HIGH
    label_bottom = LOW

    label_join x y = if x `label_leq` y then y else x
    label_meet x y = if x `label_leq` y then x else y

    label_leq LOW _      = True
    label_leq MEDIUM LOW = False
    label_leq MEDIUM _   = True
    label_leq HIGH HIGH  = True
    label_leq HIGH _     = False

data Flow l = Trans l l | Flat
    deriving Show

data FConstraint l = LEQ l l | USERGEQ
    deriving Show

data FlowArrow (s :: TriLabel) l (a :: * -> * -> *) b c = FA
    { computation :: a b c
    , flow        :: Flow l
    , constraints :: [FConstraint l]
    }
    deriving Functor

instance (Lattice l, Applicative (a b), Arrow a)
         => Applicative (FlowArrow s l a b) where
    pure x = FA (arr (const x)) Flat []
    FA c1 f1 t1 <*> FA c2 f2 t2 =
        FA { computation = c1 <*> c2
           , flow        = flowPar f1 f2
           , constraints = t1 ++ t2
           }

instance (Category a, Lattice l) => Category (FlowArrow s l a) where
    id = FA { computation = id
            , flow        = Flat
            , constraints = []
            }
    (FA c1 f1 t1) . (FA c2 f2 t2) =
        let (f, c) = flowSeq f1 f2
        in FA { computation = c1 . c2
              , flow        = f
              , constraints = t1 ++ t2 ++ c
              }

instance (Lattice l, Arrow a) => Arrow (FlowArrow s l a) where
    arr f = FA { computation = arr f
                , flow        = Flat
                , constraints = []
                }
    first (FA c f t) =
        FA { computation = first c
           , flow        = f
           , constraints = t
           }
    FA c1 f1 t1 &&& FA c2 f2 t2 =
        FA { computation = c1 &&& c2
           , flow        = flowPar f1 f2
           , constraints = t1 ++ t2
           }
    FA c1 f1 t1 *** FA c2 f2 t2 =
        FA { computation = c1 *** c2
           , flow        = flowPar f1 f2
           , constraints = t1 ++ t2
           }

instance (Lattice l, ArrowChoice a) => ArrowChoice (FlowArrow s l a) where
    left (FA c f t) =
        FA { computation = left c
           , flow        = f
           , constraints = t
           }
    FA c1 f1 t1 +++ FA c2 f2 t2 =
        FA { computation = c1 +++ c2
           , flow        = flowPar f1 f2
           , constraints = t1 ++ t2
           }
    FA c1 f1 t1 ||| FA c2 f2 t2 =
        FA { computation = c1 ||| c2
           , flow        = flowPar f1 f2
           , constraints = t1++t2
           }

instance (Lattice l, ArrowLoop a) => ArrowLoop (FlowArrow s l a) where
    loop (FA c f t) =
        let t' = constraint_loop f
        in FA { computation = loop c
              , flow        = f
              , constraints = t ++ t'
              }
      where
        constraint_loop Flat = []
        constraint_loop (Trans l1 l2) = [LEQ l2 l1]

flowSeq :: Flow l -> Flow l -> (Flow l, [FConstraint l])
flowSeq (Trans l1 l2) (Trans l3 l4) = (Trans l1 l4, [LEQ l2 l3])
flowSeq Flat f2 = (f2, [])
flowSeq f1 Flat = (f1, [])

flowPar :: Lattice l => Flow l -> Flow l -> Flow l
flowPar (Trans l1 l2) (Trans l3 l4) =
    Trans (label_meet l1 l3) (label_join l2 l4)
flowPar Flat f2 = f2
flowPar f1 Flat = f1

type Protected s a = FlowArrow s TriLabel (->) () a

tag :: (Ord a1, Lattice a1, Arrow a2) => a1 -> FlowArrow s a1 a2 a3 a3
tag x = FA (arr id) (Trans x x) []

tagVal :: a -> TriLabel -> Protected s a
tagVal x l = arr (const x) >>> tag l

exCH :: Protected 'HIGH Int
exCH = tagVal 3 HIGH

exCM :: Protected 'MEDIUM Int
exCM = tagVal 4 MEDIUM

exCL :: Protected 'LOW Int
exCL = tagVal 5 LOW

raise :: Protected s a -> Protected (Raise s) a
raise = coerce

exT1 :: Protected 'MEDIUM Int
exT1 = liftA2 (+) (raise exCL) exCM

exT2 :: Protected 'HIGH Int
exT2 = liftA2 (*) exCH (raise exCM)

exT3 :: Protected 'HIGH Int
exT3 = proc () -> do
    h <- exCH -< ()
    if h > 3
        then do
            x <- raise exCM -< ()
            returnA -< x
        else do
            x <- raise exT1 -< ()
            returnA -< x

exT4 :: Protected 'HIGH Int
exT4 = liftA2 (+) (raise (raise exCL)) (raise exCM)

expectsMedium :: Protected s a -> Protected s a
expectsMedium = (>>> tag MEDIUM)

declassify :: (Ord a1, Lattice a1, Arrow a2)
           => a1 -> a1 -> FlowArrow s a1 a2 a3 a3
declassify x y = FA (arr id) (Trans x y) [USERGEQ]

data Privilege =
    Privilege (forall r. (forall (s :: TriLabel). Sing s -> r) -> r)

highPriv :: Privilege
highPriv = Privilege $ withSomeSing HIGH

mediumPriv :: Privilege
mediumPriv = Privilege $ withSomeSing MEDIUM

lowPriv :: Privilege
lowPriv = Privilege $ withSomeSing LOW

certify :: forall (t :: TriLabel) s l a b c.
          (Show l, Show (FConstraint l), Lattice l)
        => l -> l -> Sing t -> FlowArrow s l a b c -> a b c
certify l_in l_out l_user (FA c f t)
    | not $ check_levels l_in l_out f =
      error $ "security level mismatch" ++ show f
    | not $ check_constraints l_user t =
      error $ "constraints cannot be met" ++ show t
    | otherwise = c
  where
    check_levels fl f2 f = True
    check_constraints l ct = True

cert :: forall (t :: TriLabel) s l a b c. (Lattice l, Show l)
     => Sing t -> FlowArrow s l a b c -> a b c
cert = certify label_bottom label_bottom

adminService :: Protected s Int -> IO (Protected 'HIGH Int)
adminService stat = do
    let low = stat >>> declassify HIGH LOW
        summary = withSomeSing HIGH $ \s -> cert s low ()
    print summary
    let stat_new = arr (const 0) >>> tag HIGH
    return stat_new

guestService :: Protected s Int -> IO (Protected s Int)
guestService stat = do
    putStrLn "Enter a number:"
    i <- getNumber
    let stat' = proc () -> do
            x <- stat -< ()
            if i > x
                then returnA -< i
                else returnA -< x
    return stat'
  where
    getNumber = read <$> getLine

newtype Username = Username { getUsername :: String }
    deriving (Eq, Ord, Show)
newtype Password = Password { getPassword :: String }
    deriving (Eq, Ord, Show)

data AuthDB = AuthDB [(Username, Password, Privilege)]

authenticate :: Protected 'HIGH AuthDB
             -> Protected t Int
             -> Username
             -> Password
             -> (Protected t Int -> IO (Protected 'HIGH Int)) -- admin privileges
             -> (Protected t Int -> IO (Protected t Int)) -- guest privileges
             -> (forall u. Protected u Int -> IO r)
             -> IO r
authenticate authDb stat u p af gf f =
    -- This function is an attack vector, in that the attacker can just brute
    -- force search for a working user/pass pair, since we declassify the
    -- database here unilaterally.
    let x  = authDb >>> declassify HIGH LOW
        db = withSomeSing HIGH $ \s -> cert s x ()
    in case dbLookup db of
        (Username "admin", Privilege k) -> af stat >>= f
        (Username "guest", Privilege k) -> gf stat >>= f
        _ -> do
            putStrLn "login error"
            f stat
  where
    dbLookup :: AuthDB -> (Username, Privilege)
    dbLookup (AuthDB []) = (Username "<failed>", undefined)
    dbLookup (AuthDB ((ud, pd, pr) : xs))
        | u == ud && p == pd = (ud, pr)
        | otherwise = dbLookup (AuthDB xs)

serviceLoop :: Protected 'HIGH AuthDB -> Protected s Int -> IO ()
serviceLoop auth_db stat = do
    putStrLn "Enter username and password:"
    u <- getLine
    p <- getLine
    authenticate auth_db stat (Username u) (Password p)
        adminService guestService (serviceLoop auth_db)

main :: IO ()
main = do
    let auth_db :: Protected 'HIGH AuthDB =
            arr (const $ AuthDB
                   [ (Username "admin", Password "admin", highPriv)
                   , (Username "guest", Password "guest", lowPriv)
                   ])
            >>> tag HIGH
        secret_val :: Protected 'HIGH Int = arr (const 0) >>> tag HIGH
    serviceLoop auth_db secret_val
