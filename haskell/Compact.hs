module Compact where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Monoid
import Data.Semigroup
import GHC.Naturals

type Block = Int -- Blocks are monotonically increasing, and dense

type TxId = Int -- TxIds are monotonically increasing, globally dense
-- (across all tables), locally sparse (per table)

type Key = Int -- Keys are simply unique

-- The function 'Maybe a -> a' is a closure that acts on the (potential)
-- previous value at that key. Since rows can never be deleted, but only
-- mutated or added, the codomain is not optional.
data Journal a = Journal (Map Block (Map TxId (Map Key (Maybe a -> a))))

-- For the purposes of this model, we treat values in the Db as opaque
type Db = Journal ()

instance Semigroup (Journal a) where
  Journal m1 <> Journal m2 = M.updateWithKey go m1 m2
   where
    go k x y = undefined

instance Monoid (Journal a) where
  mempty = Journal mempty
  mappend = (<>)

-- All keys modified at a given txid
modifiedKeys :: Db -> TxId -> [Key]
modifiedKeys _txid = undefined

-- Every txid that modifies a given key, in ascending order
updatesAtKey :: Db -> Key -> [TxId]
updatesAtKey _txid = undefined

-- Preserve all the last modification for every key at or below height
compact :: TxId -> State Db ()
compact _txid = undefined
