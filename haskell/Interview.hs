{-# LANGUAGE KindSignatures #-}

module Interview where

import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Data.ByteString

data HeistConfig (n :: * -> *)

data HeistState (n :: * -> *)

data Builder

type TemplateName = String

type MIMEType = String

type Errors = [String]

initHeist :: Monad n => HeistConfig n -> n (Either Errors (HeistState n))
initHeist = undefined

renderTemplate :: Monad n => HeistState n -> TemplateName -> Maybe (n Builder, MIMEType)
renderTemplate = undefined

toByteString :: Builder -> ByteString
toByteString = undefined

yourFunc :: HeistConfig IO -> TemplateName -> IO (Either Errors ByteString)
yourFunc hc nm = do
  hs <- initHeist hc
  case hs of
    Left errs -> pure $ Left errs
    Right hs -> case renderTemplate hs nm of
      Nothing -> pure $ Left ["Could not render template " ++ nm]
      Just (getBuilder, _mimety) -> do
        builder <- getBuilder
        pure $ Right $ toByteString builder

note :: a -> Maybe b -> Either a b
note err Nothing = Left err
note _err (Just x) = Right x

yourFunc2 :: HeistConfig IO -> TemplateName -> IO (Either Errors ByteString)
yourFunc2 hc nm = runExceptT $ do
  hs <- ExceptT $ initHeist hc
  (getBuilder, _mimety) <-
    ExceptT $
      pure $
        note ["Could not render template " ++ nm] $
          renderTemplate hs nm
  toByteString <$> lift getBuilder

yourFunc3 :: HeistConfig IO -> TemplateName -> IO (Either Errors ByteString)
yourFunc3 hc nm = runExceptT $ do
  hs <- ExceptT $ initHeist hc
  (getBuilder, _mimety) <-
    ExceptT $
      pure $
        note ["Could not render template " ++ nm] $
          renderTemplate hs nm
  toByteString <$> lift getBuilder

-- Complete this function using the above API
