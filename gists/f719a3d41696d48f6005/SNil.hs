module SNil where

import Data.Singletons.Prelude.List

type family FlattenRepType r where
    FlattenRepType TypeUnit = '[]
    FlattenRepType (TypeStruct ts) = ts
    FlattenRepType t = '[t]

flattenRep :: ( Representable a ) =>
              a
           -> DBusArguments (FlattenRepType (RepType a))
flattenRep (x :: t) =
    let rts = sing :: Sing (RepType t)
        frts :: Sing (FlattenRepType (RepType t))
        frts = case rts of
            STypeUnit -> SNil
            STypeStruct ts -> ts
            t -> SCons t SNil
    in undefined
