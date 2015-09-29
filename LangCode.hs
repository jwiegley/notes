{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

import GHC.TypeLits

data Lang :: Symbol -> * where
  English :: Lang "en"
  Russian :: Lang "ru"

parseJson :: String -> Lang code
parseJson str = undefined
