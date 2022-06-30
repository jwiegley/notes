module Db where

import Control.Monad.State
import Data.Map

data Schema

type Key = String

type Row = Map String String

data Change
    = Create String Schema
    | Insert String Key Row
    | Update String Key (Row -> Row)
    | Delete String Key

type Journal = [Change]

type Stream a = Int -> a

type Model a b = Stream a -> Stream (b, Journal)

data Db = Db {
  tables :: Map String (Map Key Row)
  }

type CRUD a b = a -> State Db b

delta :: Db -> Db -> Journal
delta = undefined

denote :: CRUD a b -> Model a b
denote crud input n =
  collect Db { tables = mempty } 0
 where
  collect db i
      | i == n =
        let (b, db') = runState (crud (input i)) db
         in (b, delta db db')
      | otherwise =
          collect (execState (crud (input i)) db) (succ i)

createModel :: Model (String, Schema) ()
createModel = undefined

insertModel :: Model (String, Key, Row) ()
insertModel = undefined

updateModel :: Model (String, Key, (Row -> Row)) ()
updateModel = undefined

deleteModel :: Model (String, Key) ()
deleteModel = undefined

create :: CRUD (String, Schema) ()
create = undefined

insert :: CRUD (String, Key, Row) ()
insert = undefined

update :: CRUD (String, Key, (Row -> Row)) ()
update = undefined

delete :: CRUD (String, Key) ()
delete = undefined

-- The proof requirements are the homomorphism equations:
--
-- denote (insertModel (name, key, row))
