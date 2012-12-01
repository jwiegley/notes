import Control.Applicative
import Control.Lens
import Data.Data.Lens

data Type = Foo Int
          | Bar String
          | Baz Int

data Foozle = Foozle [Type]

_foozle :: Traversal Type Type String String
_foozle f x@(Bar a) = Bar <$> f a
_foozle _ x = pure x

main =
  print $
    Foozle [ Foo 1, Bar "Hello", Baz 2]
      ^. to (\(Foozle a) -> a)
         . folded . _foozle
