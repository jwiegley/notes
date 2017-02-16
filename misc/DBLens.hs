{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module DBLens where

import Control.Lens
import Control.Monad.State
import Control.Monad.Free

data Create   = Create
data Retrieve = Retrieve {
    tables :: [String]
    }
data Modify   = Modify
data Delete   = Delete

data CRUD
    = ACreate Create
    | ARetrieve Retrieve
    | AModify Modify
    | ADelete Delete

data Transaction a = Transaction [CRUD]

data Database = Database

{-------------------------------------------------------------------------}

class Syntactic m a where
    type Internal a
    fromSyntax :: a -> m (Internal a)
    toSyntax   :: m (Internal a) -> a

data Entity = Ident | Rows

data DBModel
    = MCreate
    | MRetrieve [String]
    | MModify
    | MDelete
    deriving Show

instance Syntactic Transaction DBModel where
    type Internal DBModel = CRUD
    fromSyntax = undefined
    toSyntax = undefined

data TableModel = TableModel
data ColumnModel = ColumnModel

table :: String -> Getter Database TableModel
table name f db = undefined

rows :: Getter TableModel RowModel
rows = undefined

col :: String -> Getter RowModel ColumnModel
col name f db = undefined

(==.) :: ColumnModel -> String -> RowQuery
x ==. y = undefined

data RowModel = RowModel
data RowQuery = RowQuery

where_ :: (RowModel -> RowQuery) -> Getter RowModel RowModel
where_ = undefined

foo :: Database -> [RowModel]
foo db = db ^.. table "something" . rows . where_ (\p -> (p ^. col "name") ==. "John")
