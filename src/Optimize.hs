{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables, LambdaCase, ViewPatterns, TypeOperators #-}
module Optimize where

import Data.Maybe
import Control.Monad
import Control.Eff (Member, Eff, run, (:>))
import Control.Eff.Reader.Strict (Reader, ask, runReader)
import Control.Eff.State.Strict (State, get, modify, evalState, execState)
import qualified Data.IntMap.Strict as M
import qualified Data.IntSet as IS
import qualified Data.MultiSet as MS

import QSet

type Vertex = Int
type Pat = MS.MultiSet Var
type Target = (Pat, Vertex)

lblToVertex :: Lbl -> Vertex
lblToVertex ('l':n) = read n
lblToVertex _ = undefined

vertexToLbl :: Vertex -> Lbl
vertexToLbl = ('l':) . show


data Node =
      Go Target
    | Branch Pat Target Target

data GNode = GNode {
      gvertex :: Vertex
    , gnode :: Node
}

type Graph = M.IntMap GNode


insertNode :: Vertex -> Node -> Graph -> Graph
insertNode v node graph =
    if isJust $ M.lookup v graph
        then error $ "Duplicate label: " ++ show v
        else M.insert v (GNode v node) graph

constructInstrGraph :: [Instr] -> Graph
constructInstrGraph = flip foldr M.empty $ \i g ->
    let insert v n = insertNode v n g in
    case i of
        Comment _ -> g
        GotoInstr (lblToVertex -> v1) (lblToVertex -> v2) y ->
            insert v1 $ Go (MS.fromList y, v2)
        ForkInstr (lblToVertex -> v1) x (lblToVertex -> v2) y (lblToVertex -> v3) ->
            insert v1 $ Branch (MS.fromList x) (MS.fromList y, v2) (MS.empty, v3)

deconstructGraph :: Graph -> [SimpInstr]
deconstructGraph g = uncurry nodeToInstr =<< M.toList g
    where nodeToInstr v1 (gnode -> n) = case n of
            Go (y, v2) ->
                [ LbldInstr (vertexToLbl v1) [] (vertexToLbl v2) (MS.elems y) ]
            Branch x (y, v2) (z, v3) ->
                [ LbldInstr (vertexToLbl v1) (MS.elems x) (vertexToLbl v2) (MS.elems y)
                , LbldInstr (vertexToLbl v1) [] (vertexToLbl v3) (MS.elems z) ]


type G r e =
    ( Member (State Graph) r
    , Member (Reader (Vertex, Vertex)) r
    ) => Eff r e

getNode :: Vertex -> G r (Maybe GNode)
getNode v = do
    graph <- get
    return $ v `M.lookup` graph


optimize :: Lbl -> Lbl -> [Instr] -> [SimpInstr]
optimize lstart lend instrs =
    deconstructGraph $ run $
    flip runReader (lblToVertex lstart, lblToVertex lend) $
    execState (constructInstrGraph instrs)
        pathCompress

compileOptimized :: Int -> ([Instr], [Var], Lbl, Lbl) -> [SimpInstr]
compileOptimized ninputs (instrs, vars, lstart, lend) =
    compile ninputs (optimize lstart lend instrs, vars, lstart, lend)




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
