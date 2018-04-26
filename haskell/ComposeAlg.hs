module ComposeAlg where

import Control.Monad
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Data.Fix
import Data.Functor.Compose

algComp :: Functor f => (f a -> a) -> (f b -> b) -> f (a, b) -> (a, b)
algComp f g x = (f (fmap fst x), g (fmap snd x))

data ExprF a = Cons1 a a | Cons2 a

type Typing m a = ReaderT () (ExceptT () m) a

data Type = Type

typeOf :: ExprF (Typing m Type) -> Typing m Type
typeOf = undefined

identityAlg :: ExprF (ExprF a) -> ExprF a
identityAlg = undefined

result :: Fix ExprF -> Typing m (Fix (Compose ((,) Type) ExprF))
result = cataM $ algComp typeOf identityAlg
