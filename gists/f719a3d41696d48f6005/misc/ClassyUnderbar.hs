module ClassyUnderbar where

import Control.Lens
import Data.Char (toLower)
import Data.Set as Set hiding (toList,map,filter)
import Language.Haskell.TH

underbarPrefixRules :: LensRules
underbarPrefixRules = LensRules mLowerName fld (const Nothing) $
    Set.fromList [SingletonIso, SingletonAndField, CreateClass,
                  CreateInstance, BuildTraversals, GenerateSignatures]
  where
    fld cs = Just ('_':cs)

mLowerName :: String -> Maybe String
mLowerName (c:cs) = Just (toLower c:cs)
mLowerName _ = Nothing

-- | Rules for making lenses and traversals that precompose another 'Lens'.
classyUnderbarRules :: LensRules
classyUnderbarRules = underbarPrefixRules
  & lensIso .~ const Nothing
  & handleSingletons .~ False
  & lensClass .~ classy
  & classRequired .~ True
  & partialLenses .~ False
  & buildTraversals .~ True
  where
    classy :: String -> Maybe (String, String)
    classy n@(a:as) = Just ("Has" ++ n, toLower a:as)
    classy _ = Nothing

makeClassyUnderbar :: Name -> Q [Dec]
makeClassyUnderbar = makeLensesWith classyUnderbarRules

makeClassyUnderbarFor :: String -> String -> [(String, String)] -> Name -> Q [Dec]
makeClassyUnderbarFor clsName funName fields =
    makeLensesWith $ classyUnderbarRules
        & lensClass .~ const (Just (clsName,funName))
        & lensField .~ (`Prelude.lookup` fields)
