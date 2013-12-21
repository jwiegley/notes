import Control.Category
import Prelude hiding ((.), id)

type ArrMorphism a b c d = (a -> b) -> (c -> d)

instance Category (ArrMorphism a b) where
  id = id
  (ArrMorphism f g h k) . (ArrMorphism f' g' h' k') =
    ArrMorphism 