{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Concerto.Variables where

import           Concerto.Graph
import           Concerto.Metadata
import           Concerto.Types
import           Control.Lens
import           Control.Monad
import           Control.Monad.Freer
import           Control.Monad.Freer.State
import           Data.Graph.Inductive (Node)
import qualified Data.Graph.Inductive as G
import           Data.List (sortOn)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Matrix (Matrix)
import qualified Data.Matrix as X
import qualified Data.Matrix.Dense.Generic.Mutable as X
import           Data.Maybe (fromJust)
import           Data.Semigroup (Max(..))
import           Z3.Monad hiding (getInt)

data NodeVars a = NodeVars
    { _nvTaskName     :: String
    , _nvInstruction  :: BoxedInst
    , _nvNode         :: Node
    , _nvDeps         :: [Node]
    , _nvComponentIdx :: a
    , _nvMetadata     :: Map String ([Int], a)
    , _nvResources    :: Map String a
    , _nvOffset       :: a
    }

makeLenses ''NodeVars

type NodeVarsSMT      = NodeVars SMTInt
type NodeVarsSolution = NodeVars Int

instance Show a => Show (NodeVars a) where
    show NodeVars {..} = "NodeVars\n"
        ++ "{ nvTaskName     = " ++ show _nvTaskName ++ "\n"
        ++ ", nvInstruction  = " ++ show _nvInstruction ++ "\n"
        ++ ", nvNode         = " ++ show _nvNode ++ "\n"
        ++ ", nvDeps         = " ++ show _nvDeps ++ "\n"
        ++ ", nvComponentIdx = " ++ show _nvComponentIdx ++ "\n"
        ++ ", nvMetadata     = " ++ show _nvMetadata ++ "\n"
        ++ ", nvResources    = " ++ show _nvResources ++ "\n"
        ++ ", nvOffset       = " ++ show _nvOffset ++ "\n"
        ++ "}\n"

data SolverState f a = SolverState
    { _solverNodeMap :: Map Node (NodeVars a)
    , _solverPeriod :: a
    , _solverNodeCapability :: f
    }
    deriving Show

makeClassy ''SolverState

type SolverStateSMT      = SolverState FuncDecl SMTInt
type SolverStateSolution = SolverState (Map Int Int) Int

nodeVars :: Member (State SolverStateSMT) r => Node -> Eff r NodeVarsSMT
nodeVars n = access <$> get @SolverStateSMT
  where
    access = (^?! failing (solverNodeMap.ix n)
                          (error $ "Unknown node: " ++ show n))

nodeOffset :: NodeVarsSolution -> Int
nodeOffset = (^. nvOffset)

nodeControlStep :: SolverStateSolution -> NodeVarsSolution -> Int
nodeControlStep sol nv
    | sol^.solverPeriod == 0 =
      error "Schedule period is zero! The solution is incomplete."
    | otherwise = (nv^.nvOffset) `mod` (sol^.solverPeriod)

nodeCapability :: SolverStateSolution -> NodeVarsSolution -> Int
nodeCapability sol nv = sol ^?! solverNodeCapability.ix (nv^.nvNode)

nodeMatrix :: SolverStateSolution -> Matrix (Maybe NodeVarsSolution)
nodeMatrix sol = X.create $ do
    x <- X.new (steps + 1, caps + 1)

    -- Initialize all cells of the matrix to Nothing
    forM_ [0 .. steps] $ \s -> forM_ [0 .. caps] $ \c ->
        X.write x (s, c) Nothing

    -- Fill in the matrix with assigned nodes
    forM_ vars $ \nv ->
        X.write x (nodeControlStep sol nv, nodeCapability sol nv)
                  (Just nv)
    return x
  where
    vars  = M.elems (sol^.solverNodeMap)
    count = alaf Max foldMap ?? vars
    steps = count (nodeControlStep sol)
    caps  = count (nodeCapability sol)

extractAssignments :: SolverStateSolution -> [[Node]]
extractAssignments =
    X.toLists . X.map (maybe 0 (view nvNode)) . nodeMatrix

registerNodesWorker :: ( Member (State SolverStateSMT) r, Member SMT r )
                    => ProgramGraph -> Eff r ()
registerNodesWorker gr = do
    _0 <- smt $ mkIntNum (0 :: Int)

    -- For every node in the graph, it has:
    --   t  - a control step index
    --   a  - a capability (to execute on at that interval)
    --   c  - a choice among components (which will affect t and a)
    --   cs - the possible choices
    forM_ (G.nodes gr) $ \n -> do
        let (ps, _, lab, _) = G.context gr n
        nv <- smt $ do
            choice <- do
                let meta   = lab ^.. nlTask.taskMetadata.metaData
                    values = head (M.elems (head meta))^.metaValues
                v <- mkFreshIntVar ("n" ++ show n ++ "_choice")
                assert =<< mkAnd =<< sequenceA
                    [ mkLe _0 v
                    , mkLt v =<< mkIntNum (length values) ]
                return v

            NodeVars