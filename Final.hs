{-# LANGUAGE LambdaCase #-}

module Final where

import Language.Haskell.TH
import Control.Monad
import Data.Char (toLower)
import Data.List (foldl')

substituteType :: Type -> Type -> Type -> Type
substituteType typ repl = go where
    go s | s == typ  = repl
         | otherwise = case s of
             ForallT _ _ t -> go t
             AppT t1 t2    -> AppT (go t1) (go t2)
             SigT t _      -> go t
             _             -> s

-- Turn r and [a,b,c] into a -> b -> c -> r
funEndingIn :: Type -> [Type] -> Type
funEndingIn = foldr (AppT . AppT ArrowT)

-- Given t, turn it into forall r. t -> r.
existentialize :: (Type -> Type) -> Type
existentialize k = let r = mkName "r" in ForallT [PlainTV r] [] (k (VarT r))

makeFinalIso :: Name -> DecsQ
makeFinalIso = reify >=> \case
    TyConI (DataD ctx name binders ctors _) ->
        makeFinalType ctx name binders ctors
    TyConI (NewtypeD ctx name binders ctor _) ->
        makeFinalType ctx name binders [ctor]
    _ -> error "makeFinalIso only accepts plain ADTs (data or newtype)"
  where
    -- Given a type, such as 'data Stream a = Stream a (Stream a)'
    makeFinalType ctx name binders ctors = do
        -- The final encoding is named StreamR
        let nameR     = mkName (nameBase name ++ "R")
        -- The final unwrapper is foldStreamR
        let foldNameR = mkName ("fold" ++ nameBase name ++ "R")
        -- The final type is 'forall r. (a -> r -> r) -> r'
        let ftyp = foldType

        -- newtype StreamR a = StreamR { foldStreamR :: 'foldType' }
        let nameR'    = mkName (nameBase name ++ "R")
        let newType = NewtypeD ctx nameR binders
                               (RecC nameR' [(foldNameR, NotStrict, ftyp)]) []

        -- toStreamR :: Stream a -> StreamR a
        let nameToNameR = mkName ("to" ++ nameBase name ++ "R")
        let xname = mkName "x"
        ctorFuns <- mapM (\c -> let n = nameBase (ctorName c) in
                              newName (toLower (head n) : tail n)) ctors
        ctorMatches <-
            mapM (\(f, c) -> do
                      let poss = ctorArgCount c
                      args <- replicateM (length poss) (newName "a")
                      let app acc (arg, recurse) =
                              AppE acc
                                   (if recurse
                                    then foldl' AppE
                                                (AppE (VarE foldNameR)
                                                      (AppE (VarE nameToNameR)
                                                            arg))
                                                (map VarE ctorFuns)
                                    else arg)
                      return $
                          Match (ConP (ctorName c) (map VarP args))
                                (NormalB (foldl' app (VarE f)
                                                 (zip (map VarE args) poss)))
                                []) (zip ctorFuns ctors)

        let lam = LamE (map VarP ctorFuns) (CaseE (VarE xname) ctorMatches)
            toBody = NormalB (AppE (ConE nameR) lam)
            toNameR =
                [ SigD nameToNameR
                      (let ty = AppT (AppT ArrowT (baseType name))
                                     (baseType nameR) in
                       if null binders
                       then ty
                       else ForallT binders ctx ty)
                , FunD nameToNameR [Clause [VarP xname] toBody []]
                ]

        -- fromStreamR :: StreamR a -> Stream a
        let nameFromNameR = mkName ("from" ++ nameBase name ++ "R")
        let xname' = mkName "x"
        let fromBody = NormalB (foldl' (\acc -> AppE acc . ConE . ctorName)
                                       (AppE (VarE foldNameR) (VarE xname))
                                       ctors)
            fromNameR =
                [ SigD nameFromNameR
                      (let ty = AppT (AppT ArrowT (baseType nameR))
                                     (baseType name) in
                       if null binders
                       then ty
                       else ForallT binders ctx ty)
                , FunD nameFromNameR [Clause [VarP xname'] fromBody []]
                ]

        -- If Lens is imported, make isoStreamR :: Iso' (Stream a) (StreamR a)
        miso       <- lookupValueName "Control.Lens.iso"
        misoTyp    <- lookupTypeName "Control.Lens.Iso'"
        let isoStreamR = mkName ("iso" ++ nameBase name ++ "R")
        let lensIsoBody iso = NormalB (AppE (AppE (VarE iso)
                                                  (VarE nameToNameR))
                                            (VarE nameFromNameR))
            lensIso = case (miso, misoTyp) of
                (Just iso, Just iso') ->
                    [ SigD isoStreamR
                          (let ty = AppT (AppT (ConT iso') (baseType name))
                                         (baseType nameR) in
                           if null binders
                           then ty
                           else ForallT binders ctx ty)
                    , FunD isoStreamR [Clause [] (lensIsoBody iso) []]
                    ]
                _ -> []

        return $ [newType] ++ toNameR ++ fromNameR ++ lensIso
      where
        foldType =
            existentialize (\r -> funEndingIn r (map (ctorToFunc r) ctors))

        ctorName (NormalC n _)    = n
        ctorName (RecC n _)       = n
        ctorName (InfixC _ n _)   = n
        ctorName (ForallC _ _ co) = ctorName co

        ctorToFunc r (NormalC _ ts)     = funEndingIn r (map snd ts)
        ctorToFunc r (RecC _ ts)        = funEndingIn r (map (\(_,_,x) -> x) ts)
        ctorToFunc r (InfixC t1 _ t2)   = funEndingIn r [snd t1, snd t2]
        ctorToFunc r (ForallC bs ct co) = ForallT bs ct (ctorToFunc r co)

        ctorArgCount (NormalC _ ts)   = map (\(_,t)   -> t == nameBaseType) ts
        ctorArgCount (RecC _ ts)      = map (\(_,_,t) -> t == nameBaseType) ts
        ctorArgCount (InfixC t1 _ t2) = [snd t1 == nameBaseType,
                                         snd t2 == nameBaseType]
        ctorArgCount (ForallC _ _ co) = ctorArgCount co

        nameBaseType = baseType name
        baseType nm = foldl' (\acc -> AppT acc . VarT) (ConT nm) varNames
          where
            varNames = map (\x -> case x of
                                    PlainTV n    -> n
                                    KindedTV n _ -> n) binders

        scrub r typ | typ == nameBaseType = VarT r
                    | otherwise = typ
