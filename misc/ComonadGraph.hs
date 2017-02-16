{-# LANGUAGE RankNTypes #-}

-- a tiny annotated graph library
-- Edward Kmett 2010

module Data.Graph.Annotated where

import Data.Sequence as S
import Data.Sequence (Sequence, ViewL(..), ViewR(..), (><))
import Data.Vector as V
import Data.Ix
import qualified Data.Graph as G
import Data.Graph (Graph)
import Control.Monad.Writer.Instances
	
class PFunctor f where
	first :: (a -> b) -> f a c -> f b c
	
-- a simple safe graph library based on Data.Graph for prototyping
-- TODO: use Vector [Int] or Rope (Vector [Int])
newtype Graph b = Graph { runGraph :: G.Graph }
	
newtype Vertex b = Vertex { vertexId :: Int }
    deriving (Enum,Ix,Eq,Ord,Show,Typeable)
	
vertices :: Graph b -> [Vertex b]
vertices = fmap Vertex . G.vertices . runGraph

dfs :: Graph b -> [Vertex b] -> Forest (Vertex b)
dfs g vs = fmap Vertex <$> G.dfs (runGraph g) (vertexId <$> vs)

dff :: Graph b -> Forest (Vertex b)
dff g = Vertex <$> G.dff (runGraph g)

topSort :: Graph b -> [Vertex b]
topSort g = Vertex <$> G.topSort (runGraph g)

components :: Graph b -> Forest (Vertex b)
components g = fmap Vertex <$> G.components (runGraph g)

newtype Edge b = Edge (Vertex b, Vertex b)
    deriving (Ix,Eq,Ord,Show,Typeable)
		
edges :: Graph b -> [Edge b]
edges = fmap Edge . G.edges . runGraph

newtype NodeAnn a b = NodeAnn (G.Table a)

instance PFunctor NodeAnn where
    first f (NodeAnn t) = NodeAnn (f <$> t)

indegree :: Graph b -> NodeAnn Int b
indegree = NodeAnn . G.indegree . runGraph

outdegree :: Graph b -> NodeAnn Int b
outdegree = NodeAnn . G.outdegree . runGraph

data Degree b = Degree { indegree :: NodeAnn Int b, outDegree :: NodeAnn Int b } 

degree :: Graph b -> (Degree `Annotated` Graph) b
degree g = (g, Degree (indegree g) (outdegree g)) 

-- newtype NodeMap k b = NodeAnn (Map k IntSet) (IntMap [k])
-- tag :: Ord k => k -> Vertex b -> NodeMap k b -> NodeMap k b
-- lookup :: NodeMap k b -> k -> [Vertex b]

-- used internally, expose?
class Functor w => Comonad w where
    extract :: w a -> a
	extend :: (w a -> b) -> w a -> w b
	duplicate :: w a -> w (w a)
	
	duplicate = extend id
	extend f = fmap f . duplicate
	
instance Comonad ((,)e) where
	extract = snd
	extend f ea = (fst ea, f ea)
	duplicate f ea@(e,_) = (e, f ea)

type Annotated f s b = (s b, f b)

-- existentially wrapped annotation
-- data Ann f s = forall b. Ann ((f `Annotated` s) b)

-- runAnn :: Ann f s -> (forall b. (f `Annotated` s) b -> r) -> r
-- runAnn (Ann a) k = k a 

-- a boxed up annotated structure
newtype Ann f s = Ann { runAnn :: forall r. (forall b. (f `Annotated` s) b -> r) -> r } 

-- we can transpose node annotations easily
data Transpose b

class TransposableAnn f where
    transposeAnn :: (f `Annotated` Graph) a -> f (Transpose a)
	
instance TransposableAnn (NodeAnn a) where
    transposeAnn (NodeAnn t) = NodeAnn t

transpose :: TransposableAnn f => (f `Annotated` Graph) b -> (f `Annotated` Graph) (Transpose b)
transpose g = (G.transpose (runGraph g),  transposeAnn g)
