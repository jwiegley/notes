{-# LANGUAGE TemplateHaskell #-}
module Main where
{-
You gain access to a massive storage cluster arranged in a grid; each storage node is only connected to the four nodes directly adjacent to it (three if the node is on an edge, two if it's in a corner).

You can directly access data only on node /dev/grid/node-x0-y0, but you can perform some limited actions on the other nodes:

You can get the disk usage of all nodes (via df). The result of doing this is in your puzzle input.
You can instruct a node to move (not copy) all of its data to an adjacent node (if the destination node has enough space to receive the data). The sending node is left empty after this operation.
Nodes are named by their position: the node named node-x10-y10 is adjacent to nodes node-x9-y10, node-x11-y10, node-x10-y9, and node-x10-y11.

Before you begin, you need to understand the arrangement of data on these nodes. Even though you can only move data between directly connected nodes, you're going to need to rearrange a lot of the data to get access to the data you need. Therefore, you need to work out how you might be able to shift data around.

To do this, you'd like to count the number of viable pairs of nodes. A viable pair is any two nodes (A,B), regardless of whether they are directly connected, such that:

Node A is not empty (its Used is not zero).
Nodes A and B are not the same node.
The data on node A (its Used) would fit on node B (its Avail).
How many viable pairs of nodes are there?
-}

import           Control.Lens
import           Lib hiding (prs, prs')
import           Test.Hspec
import qualified Test.Hspec             as H
import           Test.Hspec.Megaparsec
import           Test.QuickCheck
import           Test.Hspec.QuickCheck
-- import           Test.Hspec.SmallCheck
import           Test.Tasty
import           Test.Tasty.HUnit
import           Text.Megaparsec
import           Text.Megaparsec.String

-- x,y,size,used
data Node = N { _x :: !Int, _y:: !Int, _size :: !Int, _free :: !Int } deriving (Eq, Ord, Show)

makeLenses ''Node

-- data Node = Node  Int

-- main = do contents <- readFile "input2.txt"
--           let nodes = parseLines parseNode contents
--           print $ take 5 nodes

main :: IO ()
main = H.hspec foo

parseNode :: Parser Node
parseNode =
  N <$ wholestring "/dev/grid/node-x" <*> number <* string "-y" <*> number <* space <*> number <* char 'T' <* number <* char 'T' <*> number <* some anyChar <* eof

-- main = defaultMain tests
-- tests ::  TestTree
-- tests = testGroup "Tests" [unitTests]

-- unitTests = testGroup "Unit tests"
--   [ testCase


prs
  :: Parsec Dec String a -- ^ Parser to run
  -> String            -- ^ Input for the parser
  -> Either (ParseError Char Dec) a -- ^ Result of parsing
prs p = parse p ""
{-# INLINE prs #-}

-- | Just like 'prs', but allows to inspect final state of the parser.

prs'
  :: Parsec Dec String a -- ^ Parser to run
  -> String            -- ^ Input for the parser
  -> (State String, Either (ParseError Char Dec) a) -- ^ Result of parsing
prs' p s = runParser' p (initialState s)
{-# INLINE prs' #-}

foo :: Spec
foo = H.describe "eol" $ do
  context "when stream begins with a newline" $
    it "succeeds returning the newline" $
      property $ \s -> do
        let s' = '\n' : s
        prs  eol s' `shouldParse`     "\n"
        prs' eol s' `succeedsLeaving` s
  context "when stream begins with CRLF sequence" $
    it "parses the CRLF sequence" $
      property $ \s -> do
        let s' = '\r' : '\n' : s
        prs  eol s' `shouldParse`     "\r\n"
        prs' eol s' `succeedsLeaving` s

-- context "foo" $ it "bar" $ property $ \s -> True
