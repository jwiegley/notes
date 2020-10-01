module Transport where

import Data.Set

-- This is a model of the network transport used by P2P

type NodeId = Int
type Flow = Int

type Endpoint = (NodeId, Flow)

type Network a = Endpoint -> Set a

send :: Endpoint -> a -> Network a -> Network a
send = undefined

recv :: Endpoint -> Network a -> Set a
recv = undefined
