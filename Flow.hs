{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE OverloadedStrings #-}

module Flow where

import Control.Applicative
import Control.Arrow
import Control.Category
import Prelude hiding (id, (.))

class Eq a => Lattice a where
    label_top    :: a
    label_bottom :: a
    label_leq    :: a -> a -> Bool
    label_join   :: a -> a -> a
    label_meet   :: a -> a -> a

data TriLabel = LOW | MEDIUM | HIGH
    deriving (Eq, Ord, Show)

instance Lattice TriLabel where
    label_top    = HIGH
    label_bottom = LOW

    label_join x y = if x `label_leq` y
                     then y
                     else x
    label_meet x y = if x `label_leq` y
                     then x
                     else y

    label_leq LOW _      = True
    label_leq MEDIUM LOW = False
    label_leq MEDIUM _   = True
    label_leq HIGH HIGH  = True
    label_leq HIGH _     = False

data Flow l = Trans l l | Flat
    deriving Show

data Constraint l = LEQ l l | USERGEQ
    deriving Show

data FlowArrow l (a :: * -> * -> *) b c = FA
    { computation :: a b c
    , flow        :: Flow l
    , constraints :: [Constraint l]
    }
    deriving Functor

instance (Lattice l, Applicative (a b), Arrow a)
         => Applicative (FlowArrow l a b) where
    pure x = FA (arr (const x)) Flat []
    FA c1 f1 t1 <*> FA c2 f2 t2 =
        FA { computation = c1 <*> c2
           , flow = flowPar f1 f2
           , constraints = t1 ++ t2
           }

instance (Category a, Lattice l) => Category (FlowArrow l a) where
    id = FA { computation = id
            , flow = Flat
            , constraints = []
            }
    (FA c1 f1 t1) . (FA c2 f2 t2) =
        let (f, c) = flowSeq f1 f2
        in FA { computation = c1 . c2
              , flow = f
              , constraints = t1 ++ t2 ++ c
              }

instance (Lattice l, Arrow a) => Arrow (FlowArrow l a) where
    arr f = FA { computation = arr f
                , flow = Flat
                , constraints = []
                }
    first (FA c f t) =
        FA { computation = first c
           , flow = f
           , constraints = t
           }
    (FA c1 f1 t1) &&& (FA c2 f2 t2) =
        FA { computation = c1 &&& c2
           , flow = flowPar f1 f2
           , constraints = t1 ++ t2
           }
    (FA c1 f1 t1) *** (FA c2 f2 t2) =
        FA { computation = c1 *** c2
           , flow = flowPar f1 f2
           , constraints = t1 ++ t2
           }

instance (Lattice l, ArrowChoice a) => ArrowChoice (FlowArrow l a) where
    left (FA c f t) =
        FA { computation = left c
           , flow = f
           , constraints = t
           }
    (FA c1 f1 t1) +++ (FA c2 f2 t2) =
        FA { computation = c1 +++ c2
           , flow = flowPar f1 f2
           , constraints = t1 ++ t2
           }
    (FA c1 f1 t1) ||| (FA c2 f2 t2) =
        FA { computation = c1 ||| c2
           , flow = flowPar f1 f2
           , constraints = t1++t2
           }

instance (Lattice l, ArrowLoop a) => ArrowLoop (FlowArrow l a) where
    loop (FA c f t) =
        let t' = constraint_loop f
        in FA { computation = loop c
              , flow = f
              , constraints = t ++ t'
              }
      where
        constraint_loop Flat = []
        constraint_loop (Trans l1 l2) = [LEQ l2 l1]

flowSeq :: Flow l -> Flow l -> (Flow l, [Constraint l])
flowSeq (Trans l1 l2) (Trans l3 l4) = (Trans l1 l4, [LEQ l2 l3])
flowSeq Flat f2 = (f2, [])
flowSeq f1 Flat = (f1, [])

flowPar :: Lattice l => Flow l -> Flow l -> Flow l
flowPar (Trans l1 l2) (Trans l3 l4) = Trans (label_meet l1 l3) (label_join l2 l4)
flowPar Flat f2 = f2
flowPar f1 Flat = f1

type Protected a = FlowArrow TriLabel (->) () a

tag :: (Ord a1, Lattice a1, Arrow a2) => a1 -> FlowArrow a1 a2 a3 a3
tag x = FA (arr id) (Trans x x) []

tagVal :: a -> TriLabel -> Protected a
tagVal x l = arr (const x) >>> tag l

exCH :: Protected Int
exCH = tagVal 3 HIGH
exCM :: Protected Int
exCM = tagVal 4 MEDIUM
exCL :: Protected Int
exCL = tagVal 5 LOW

exT1 :: Protected Int
exT1 = liftA2 (+) exCL exCM
exT2 :: Protected Int
exT2 = liftA2 (*) exCH exCM
exT3 :: Protected Int
exT3 = proc () -> do
    { h <- exCH -< ();
      if h > 3 then do
          { x <- exCM -< ();
            returnA -< x;
          }
          else do
          { x <- exT1 -< ();
            returnA -< x;
            }
    }

expectsMedium :: Protected a -> Protected a
expectsMedium c = c >>> tag MEDIUM

declassify :: (Ord a1, Lattice a1, Arrow a2)
           => a1 -> a1 -> FlowArrow a1 a2 a3 a3
declassify x y = FA (arr id) (Trans x y) [USERGEQ]

data Privilege l = PR l

type Priv = Privilege TriLabel

certify :: (Show l, Show (Constraint l), Lattice l)
        => l -> l -> Priv -> FlowArrow l a b c -> a b c
certify l_in l_out (PR l_user) (FA c f t)
    | not $ check_levels l_in l_out f =
      error $ "security level mismatch" ++ show f
    | not $ check_constraints l_user t =
      error $ "constraints cannot be met" ++ show t
    | otherwise = c
  where
    check_levels fl f2 f = True
    check_constraints l ct = True

cert :: (Lattice l, Show l) => Priv -> FlowArrow l a b c -> a b c
cert = certify label_bottom label_bottom

adminService :: Priv -> Protected Int -> IO (Protected Int)
adminService priv stat = do
    let low = stat >>> declassify HIGH LOW
        summary = cert priv low ()
    print summary
    let stat_new = arr (const 0) >>> tag HIGH
    return stat_new

guestService :: Priv -> Protected Int -> IO (Protected Int)
guestService _priv stat = do
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

type AuthDB = [(Username, Password, TriLabel)]

authenticate :: Protected AuthDB -> Username -> Password -> (Username, Priv)
authenticate authDb u p =
    -- This function is an attack vector, in that the attacker can just brute
    -- force search for a working user/pass pair, since we declassify the
    -- database here unilaterally.
    let x = authDb >>> declassify HIGH LOW
        db = cert (PR HIGH) x ()
    in dbLookup db
  where
    dbLookup :: AuthDB -> (Username, Priv)
    dbLookup [] = (Username "<failed>", PR LOW)
    dbLookup ((ud, pd, pr) : xs)
        | u == ud && p == pd = (ud, PR pr)
        | otherwise = dbLookup xs

serviceLoop :: Protected AuthDB -> Protected Int -> IO ()
serviceLoop auth_db stat = do
    putStrLn "Enter username and password:"
    u <- getLine
    p <- getLine
    let (ident, priv) = authenticate auth_db (Username u) (Password p)
    stat_new <- case getUsername ident of
        "admin" -> adminService priv stat
        "guest" -> guestService priv stat
        _ -> do
            putStrLn "login error"
            return stat
    serviceLoop auth_db stat_new

main :: IO ()
main = do
    let auth_db :: Protected AuthDB =
            arr (const [(Username "admin", Password "admin", HIGH),
                        (Username "guest", Password "guest", LOW)])
            >>> tag HIGH
        secret_val :: Protected Int = arr (const 0) >>> tag HIGH
    serviceLoop auth_db secret_val
