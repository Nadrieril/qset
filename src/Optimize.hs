{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables, LambdaCase, ViewPatterns, TypeOperators #-}
module Optimize where

import Data.Maybe
import Control.Monad
import Control.Eff (Member, Eff, run, (:>))
import Control.Eff.Reader.Strict (Reader, ask, runReader)
import Control.Eff.State.Strict (State, get, put, modify, evalState)
import qualified Data.IntMap.Strict as M
import qualified Data.IntSet as IS
import qualified Data.MultiSet as MS

import QSet

type Vertex = Int
type Pat = MS.MultiSet Var
type Target = (Pat, Vertex)

data Node =
      Go Target
    | Branch Pat Target Target

data GNode = GNode {
      gvertex :: Vertex
    , gnode :: Node
}

type Graph = M.IntMap GNode

type G r e =
    ( Member (State Graph) r
    , Member (Reader (Vertex, Vertex)) r
    ) => Eff r e


lblToVertex :: Lbl -> Vertex
lblToVertex ('l':n) = read n
lblToVertex _ = undefined

vertexToLbl :: Vertex -> Lbl
vertexToLbl = ('l':) . show


constructInstrGraph :: [Instr] -> G r ()
constructInstrGraph instrs = forM_ instrs $ \case
    Comment _ -> return ()
    GotoInstr l1 l2 y -> newNode (lblToVertex l1) $ Go (MS.fromList y, lblToVertex l2)
    ForkInstr l1 x l2 y l3 -> newNode (lblToVertex l1) $ Branch (MS.fromList x) (MS.fromList y, lblToVertex l2) (MS.empty, lblToVertex l3)

newNode :: Vertex -> Node -> G r ()
newNode v node = do
    graph <- get
    when (isJust $ M.lookup v graph) $ error $ "Duplicate label: " ++ show v
    put $ M.insert v (GNode v node) graph

deconstructGraph :: Graph -> [SimpInstr]
deconstructGraph g = uncurry nodeToInstr =<< M.toList g
    where nodeToInstr v1 (gnode -> n) = case n of
            Go (y, v2) -> [LbldInstr (vertexToLbl v1) [] (vertexToLbl v2) (MS.elems y)]
            Branch x (y, v2) (z, v3) ->
                [ LbldInstr (vertexToLbl v1) (MS.elems x) (vertexToLbl v2) (MS.elems y),
                  LbldInstr (vertexToLbl v1) [] (vertexToLbl v3) (MS.elems z)]



optimize :: Lbl -> Lbl -> [Instr] -> [SimpInstr]
optimize lstart lend instrs = run $
    flip runReader (lblToVertex lstart, lblToVertex lend) $
    evalState (M.empty :: Graph) $ do
        constructInstrGraph instrs
        pathCompress
        deconstructGraph <$> get

compileOptimized :: Int -> ([Instr], [Var], Lbl, Lbl) -> [SimpInstr]
compileOptimized ninputs (instrs, vars, lstart, lend) =
    compile ninputs (optimize lstart lend instrs, vars, lstart, lend)



getNode :: Vertex -> G r (Maybe GNode)
getNode lbl = do
    graph <- get
    return $ lbl `M.lookup` graph


dfsDo :: forall r. (GNode -> G (State IS.IntSet :> r) ()) -> G r ()
dfsDo action = do
    (vstart, _::Vertex) <- ask
    evalState IS.empty $ dfsDoAt vstart

    where
        dfsDoAt :: Vertex -> G (State IS.IntSet :> r) ()
        dfsDoAt v = do
            visited <- get
            mnode <- getNode v
            unless (v `IS.member` visited || null mnode) $ do
                modify $ IS.insert v
                let Just n = mnode
                case gnode n of
                    Go (_, v1) ->
                        dfsDoAt v1
                    Branch _ (_, v1) (_, v2) -> do
                        dfsDoAt v1
                        dfsDoAt v2
                action n


pathCompress :: G r ()
pathCompress = dfsDo $ \(GNode v node) ->
    modify . M.insert v . GNode v =<< case node of
        Go t1@(_, v1) -> do
            n1 <- getNode v1
            let t1' = fromMaybe t1 (compress t1 =<< n1)
            return $ Go t1'

        Branch x t1@(_, v1) t2@(_, v2) -> do
            n1 <- getNode v1
            n2 <- getNode v2
            let t1' = fromMaybe t1 (compress t1 =<< n1)
            let t2' = fromMaybe t2 (compress t2 =<< n2)
            return $ Branch x t1' t2'

    where
        compress :: Target -> GNode -> Maybe Target
        compress (pat, _) (gnode -> n) = case n of
            Go (y, v1) -> Just (pat `MS.union` y, v1)
            Branch x (y, v1) _  | x `MS.isSubsetOf` pat -> Just ((pat `MS.difference` x) `MS.union` y, v1)
            _ -> Nothing
