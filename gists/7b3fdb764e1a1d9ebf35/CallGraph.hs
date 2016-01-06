{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import           Control.Lens
import           Control.Monad.State
import           Data.Graph.Inductive.Graph as G hiding (nodes)
import           Data.Graph.Inductive.PatriciaTree as G
import           Data.Graph.Inductive.Query.DFS as G
import           Data.GraphViz
import           Data.GraphViz.Attributes.Complete
import           Data.GraphViz.Types.Generalised as Gen
import           Data.List (foldl', isInfixOf, nub, sort, (\\))
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (fromJust, fromMaybe)
import           Data.Text.Lazy.IO as T
import           Data.Text.Lazy.Lens
import           System.Directory
import           System.Environment
import           System.Process
import           Text.Parsec
import           Text.Parsec.Prim
import           Text.Parsec.String

makePrisms ''Attribute
makePrisms ''Label
makePrisms ''RecordField

type AttrGraph = G.Gr Attributes Attributes
type CfgGraph  = G.Gr String ()

readCfg :: Map String Node -> Node -> StateT CfgGraph IO ()
readCfg nodeMap n = get >>= \gr -> case G.lab gr n of
    Nothing -> return ()
    Just "" -> return ()
    Just func -> do
        let fname = "cfg." ++ func ++ ".dot"
        ex <- liftIO $ doesFileExist fname
        when ex $ processFunc func fname
  where
    processFunc func fname = do
        gr <- get
        let os = G.toEdge <$> G.out gr n
        modify $ G.delEdges os
        fgr <- liftIO $ readDot fname
        forM_ (G.topsort fgr) $ \sn -> do
            let l = _Just . traverse._Label . _StrLabel . unpacked
                s = fromMaybe "" (lab fgr sn ^? l)
            case Text.Parsec.Prim.parse callTarget func s of
                Left _err -> return ()
                Right ss -> do
                    ns <- gets $ newNodes (length ss)
                    forM_ (zip ns ss) $ \(tn, ts) -> do
                        modify $ G.insNode
                            (tn, func ++ "->" ++ ts ++ ":" ++ show tn)
                        modify $ G.insEdge (n, tn, ())
                        case nodeMap ^. at ts of
                            Nothing   -> return ()
                            Just dest -> modify $ G.insEdge (tn, dest, ())

callTarget :: Parser [String]
callTarget = many $ try $
       manyTill anyChar (try (string " call "))
    *> manyTill anyChar (try (string " @"))
    *> manyTill anyChar (try (char '('))

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["parse", path] -> parseFile path

        ["compare", path1, path2] -> do
            gr1 <- readGraph path1
            gr2 <- readGraph path2
            compareGraphs gr1 gr2

        _ -> Prelude.putStrLn
                 "usage: callgraph [parse FILE.C|compare GRAPH1 GRAPH2]"

parseFile :: FilePath -> IO ()
parseFile path = do
    _ <- system $ "clang " ++ path
              ++ " -S -emit-llvm -w -o - | opt -dot-callgraph -o /dev/null"
              ++ " 2>/dev/null"
    _ <- system $ "clang " ++ path
              ++ " -S -emit-llvm -w -o - | opt -dot-cfg -o /dev/null"
              ++ " 2>/dev/null"

    gr  <- readDot "callgraph.dot" :: IO AttrGraph
    let gr' = G.nemap nameOf (const ()) gr :: CfgGraph
        nm  = G.ufold (\(_, node, name, _) -> M.insert name node) M.empty gr'

    gr'' <- execStateT (mapM (readCfg nm) (G.topsort gr')) gr'
    forM_ (G.topsort gr'') $ \n ->
        Prelude.putStrLn $
            "id "    ++ show n ++ " " ++ show (fromJust (G.lab gr'' n)) ++
            "\npre " ++ show n ++ " " ++ show (G.pre gr'' n) ++
            "\nsuc " ++ show n ++ " " ++ show (G.suc gr'' n)


readDot :: FilePath -> IO AttrGraph
readDot path = do
    body <- T.readFile path
    return $ let dg = parseDotGraph body :: Gen.DotGraph String in
             dotToGraph $ (read :: String -> Int) . drop 4 <$> dg

readGraph :: FilePath -> IO CfgGraph
readGraph path = do
    body <- Prelude.readFile path
    case Text.Parsec.Prim.parse go path body of
        Left err -> error (show err)
        Right x  -> return x
  where
    go :: Parser CfgGraph
    go = foldl' (\g (n, es) ->
                     foldl' (flip insEdge) (insNode n g) es) empty
             <$> many nodes

    nodes :: Parser (LNode String, [LEdge ()])
    nodes = do
        n    <- nodeId "id"
        name <- readName
        _    <- newline
        ins  <- map (\e -> (e, n, ())) <$> edgeList "pre"
        outs <- map (\e -> (n, e, ())) <$> edgeList "suc"
        return ((n, name), ins ++ outs)
      where
        nodeId :: String -> Parser Int
        nodeId str = string str *> spaces *> (read <$> many1 digit) <* spaces

        readName :: Parser String
        readName = spaces *> between (char '"') (char '"')
                                     (many (satisfy $ \c -> c /= '"'))

        edgeList :: String -> Parser [Node]
        edgeList str = do
            _n   <- nodeId str
            cids <- between (char '[') (char ']')
                           ((read <$> many1 digit) `sepBy` char ',')
            _    <- newline
            return cids

nodeName :: CfgGraph -> Node -> String
nodeName g n = fromMaybe "" (G.lab g n)

compareGraphs :: CfgGraph -> CfgGraph -> IO ()
compareGraphs before after =
    forM_ (G.topsort (G.labfilter (/= "") before)) $ \n1 ->
        case nodeName before n1 of
            name | "->" `isInfixOf` name -> return ()
                 | otherwise -> loopOverFunctions name n1
  where
    loopOverFunctions name n1 =
        forM_ (G.topsort (G.labfilter (== name) after)) $ \n2 -> do
            let ins1  = winnow before n1
                ins2  = winnow after  n2
                ins1' = ins1 \\ ins2
                ins2' = ins2 \\ ins1
            unless (null ins1' && null ins2') $
                Prelude.putStrLn $ "Function: " ++ name
            unless (null ins1') $
                Prelude.putStrLn $ "    Removed: " ++ show ins1'
            unless (null ins2') $
                Prelude.putStrLn $ "    Added:   " ++ show ins2'

    winnow g  = nub . sort . map (stripName . nodeName g . fst) . G.lsuc g
    stripName = takeWhile (/= ':')

nameOf :: Attributes -> String
nameOf xs = fromMaybe "" (xs ^? l)
  where
    l = traverse._Label
      . _RecordLabel
      . traverse._FlipFields
      . traverse._FieldLabel
      . unpacked
