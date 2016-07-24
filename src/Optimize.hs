{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables, LambdaCase, ViewPatterns #-}
module Optimize where

import Data.Maybe
import qualified Data.Map.Strict as M
import Control.Monad
import Control.Eff (Member, Eff, run, (:>))
import Control.Eff.Reader.Strict (Reader, ask, runReader)
import Control.Eff.State.Strict (State, get, put, modify, evalState)
import Control.Eff.Writer.Strict (Writer, tell, runWriter, runMonoidWriter)
import qualified Data.MultiSet as MS

import QSet

type Pat = MS.MultiSet Var
type Target = (Pat, Lbl)

data Node =
      Go Target
    | Branch Pat Target Target

data GNode = GNode {
      node :: Node
    , visited :: Bool
}

type Graph = M.Map Lbl GNode

type G r e =
    ( Member (State Graph) r
    , Member (Reader (Lbl, Lbl)) r
    ) => Eff r e


constructInstrGraph :: [Instr] -> G r ()
constructInstrGraph instrs = forM_ instrs $ \case
    Comment _ -> return ()
    GotoInstr l1 l2 y -> newNode l1 $ Go (MS.fromList y, l2)
    ForkInstr l1 x l2 y l3 -> newNode l1 $ Branch (MS.fromList x) (MS.fromList y, l2) (MS.empty, l3)

newNode :: Lbl -> Node -> G r ()
newNode lbl node = do
    graph <- get
    when (isJust $ M.lookup lbl graph) $ error $ "Duplicate label: " ++ lbl
    put $ M.insert lbl (GNode node False) graph

deconstructGraph :: Graph -> [SimpInstr]
deconstructGraph g = uncurry nodeToInstr =<< M.toList g
    where nodeToInstr l1 (node -> n) = case n of
            Go (y, l2) -> [LbldInstr l1 [] l2 (MS.elems y)]
            Branch x (y, l2) (z, l3) ->
                [LbldInstr l1 (MS.elems x) l2 (MS.elems y), LbldInstr l1 [] l3 (MS.elems z)]



optimize :: Lbl -> Lbl -> [Instr] -> [SimpInstr]
optimize lstart lend instrs = run $
    flip runReader (lstart, lend) $
    evalState (M.empty :: Graph) $ do
        constructInstrGraph instrs
        pathCompress
        deconstructGraph <$> get

compileOptimized :: Int -> ([Instr], [Var], Lbl, Lbl) -> [SimpInstr]
compileOptimized ninputs (instrs, vars, lstart, lend) =
    compile ninputs (optimize lstart lend instrs, vars, lstart, lend)



getNode :: Lbl -> G r (Maybe GNode)
getNode lbl = do
    graph <- get
    return $ lbl `M.lookup` graph


pathCompress :: G r ()
pathCompress = do
    (lstart, _::Lbl) <- ask
    pathCompressAt lstart

pathCompressAt :: Lbl -> G r ()
pathCompressAt lbl = getNode lbl >>= \case
    Nothing -> return ()
    Just GNode{ visited = True } -> return ()
    Just (gn@GNode{ node = node }) -> do
        modify $ M.insert lbl (gn { visited = True })
        nnode <- case node of
            Go t1@(_, l1) -> do
                pathCompressAt l1
                n1 <- getNode l1
                let t1' = fromMaybe t1 (compress t1 =<< n1)
                return $ Go t1'
            Branch x t1@(_, l1) t2@(_, l2) -> do
                pathCompressAt l1
                pathCompressAt l2
                n1 <- getNode l1
                n2 <- getNode l2
                let t1' = fromMaybe t1 (compress t1 =<< n1)
                let t2' = fromMaybe t2 (compress t2 =<< n2)
                return $ Branch x t1' t2'

        modify $ M.insert lbl (gn { node = nnode, visited = True })

    where compress (pat, _) = (. node) $ \case
            Go (y, l1) -> Just (pat `MS.union` y, l1)
            Branch x (y, l1) _  | x `MS.isSubsetOf` pat -> Just ((pat `MS.difference` x) `MS.union` y, l1)
            _ -> Nothing
