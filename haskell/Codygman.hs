{-# LANGUAGE LambdaCase #-}

module Codygman where

import Control.Lens
import Control.Monad.State
import Data.Graph.Inductive
import qualified Data.Map as M

analyze :: [(String, [String])] -> [String]
analyze xs = flip evalState (0, empty :: Gr String String, M.empty) $ do
    forM_ xs $ \case
        ("Node", [name]) -> do
            n <- use _1
            _1 += 1
            _2 %= insNode (n, name)
            _3.at name ?= n
        ("Link", node:names) -> forM_ names $ \name -> do
            m <- use _3
            _2 %= insEdge (m M.! node, m M.! name, "edge label")
        x -> error $ "Unexpected input value: " ++ show x
    gr <- use _2
    return $ map (\n -> context gr n ^. _3)
           $ reverse (dfs' gr)

test = analyze [ ("Node", ["app-name1"])
               , ("Node", ["app-name2"])
               , ("Link", ["app-name1", "app-name2"]) ]
