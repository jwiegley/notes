import Data.Functor.Identity
import Control.Applicative
import Text.Parsec

data Operation = Rename String String deriving Show

rename :: Parsec String () Operation
rename = Rename <$> (string "rename" *> many1 space *> many1 letter <* spaces)
                <*> (many1 letter <* spaces <* eof)

main :: IO ()
main = print $ parse rename "" "rename foo bar"