{-# LANGUAGE EmptyDataDecls #-}

module Pavonia where

data ParameterDefinition'
data Parameter

data Builder t = Builder {
        builderParams :: [ParameterDefinition'],
        builderApply  :: [Parameter] -> Either String t
    }

instance Functor Builder where
    fmap f (Builder params apply) = Builder params (fmap f . apply)

instance Applicative Builder where
    pure a = Builder [] (\_ -> Right a)
    Builder paramsF applyF <*> Builder paramsA applyA =
        Builder (paramsF ++ paramsA) $ \ps -> ($) <$> applyF ps <*> applyA ps

instance Monad Builder where
    return = pure
    -- Builder a -> (a -> Builder b) -> Builder b
    Builder paramsA applyA >>= f =
        Builder (paramsA ++ _)
                (\ps -> do a <- applyA ps
                           builderApply (f a) ps)
