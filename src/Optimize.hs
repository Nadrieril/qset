{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables, LambdaCase, ViewPatterns, TypeOperators, DeriveFunctor, DeriveFoldable, DeriveTraversable, TupleSections #-}
module Optimize where

import Data.Maybe
import Control.Monad
import Control.Eff (Member, Eff, run, (:>))
import Control.Eff.Reader.Strict (Reader, ask, runReader)
import Control.Eff.State.Strict (State, get, modify, evalState)
import Control.Eff.Writer.Strict (tell, runMonoidWriter)
import qualified Data.IntMap.Strict as M
import qualified Data.IntSet as IS
import qualified Data.MultiSet as MS

import QSet

type Vertex = Int
type Pat = MS.MultiSet Var
type Target a = (Pat, a)

lblToVertex :: Lbl -> Vertex
lblToVertex ('l':n) = read n
lblToVertex _ = undefined

vertexToLbl :: Vertex -> Lbl
vertexToLbl = ('l':) . show


data Node a =
      Go a
    | Branch Pat a a
    deriving (Functor, Foldable, Traversable)

data GNode a = GNode {
      gvertex :: Vertex
    , gnode :: Node (Target a)
} deriving (Functor, Foldable, Traversable)

type Graph = M.IntMap (GNode Vertex)


insertNode :: Vertex -> Node (Target Vertex) -> Graph -> Graph
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

nodeToInstrs :: GNode Vertex -> [SimpInstr]
nodeToInstrs (GNode v1 n) = case n of
        Go (y, v2) ->
            [ LbldInstr (vertexToLbl v1) [] (vertexToLbl v2) (MS.elems y) ]
        Branch x (y, v2) (z, v3) ->
            [ LbldInstr (vertexToLbl v1) (MS.elems x) (vertexToLbl v2) (MS.elems y)
            , LbldInstr (vertexToLbl v1) [] (vertexToLbl v3) (MS.elems z) ]


type G r e =
    ( Member (State Graph) r
    , Member (Reader (Vertex, Vertex)) r
    ) => Eff r e

getNode :: Vertex -> G r (Maybe (GNode Vertex))
getNode v = do
    graph <- get
    return $ v `M.lookup` graph


optimize :: Lbl -> Lbl -> [Instr] -> [SimpInstr]
optimize lstart lend instrs = run $
    flip runReader (lblToVertex lstart, lblToVertex lend) $
    evalState (constructInstrGraph instrs) $ do
        pathCompress
        nodes <- reverse <$> reachable
        return $ nodeToInstrs =<< nodes

compileOptimized :: Int -> ([Instr], [Var], Lbl, Lbl) -> [SimpInstr]
compileOptimized ninputs (instrs, vars, lstart, lend) =
    compile ninputs (optimize lstart lend instrs, vars, lstart, lend)



dfsFold :: a -> (GNode (Vertex, a) -> G (State IS.IntSet :> r) a) -> G r a
dfsFold dft action = do
    (vstart, _::Vertex) <- ask
    dfsFoldAt vstart dft action

dfsFoldAt :: forall r a. Vertex -> a -> (GNode (Vertex, a) -> G (State IS.IntSet :> r) a) -> G r a
dfsFoldAt v dft action = snd <$> evalState IS.empty (dfsFoldAux v)
    where
        dfsFoldAux :: Vertex -> G (State IS.IntSet :> r) (Vertex, a)
        dfsFoldAux v = (v,) <$> do
            visited <- get
            getNode v >>= \case
                Nothing -> return dft
                _ | v `IS.member` visited -> return dft
                Just n -> do
                    modify $ IS.insert v
                    action =<< traverse dfsFoldAux n

dfsDo :: (GNode Vertex -> G (State IS.IntSet :> r) ()) -> G r ()
dfsDo action = do
    (vstart, _::Vertex) <- ask
    dfsDoAt vstart action

dfsDoAt :: Vertex -> (GNode Vertex -> G (State IS.IntSet :> r) ()) -> G r ()
dfsDoAt v action = dfsFoldAt v () (action . fmap fst)




reachable :: G r [GNode Vertex]
reachable = fst <$> runMonoidWriter (dfsDo tellOne)
    where tellOne = tell . (:[])


pathCompress :: G r ()
pathCompress = void $ dfsFold Nothing $ \(GNode v node) -> do
    let gnode' = GNode v $ fmap f node
    modify $ M.insert v gnode'
    return $ Just gnode'

    where
        f :: Target (a, Maybe (GNode a)) -> Target a
        f (p, (v, n)) = fromMaybe (p, v) (compress p =<< n)

        compress :: Pat -> GNode a -> Maybe (Target a)
        compress pat (gnode -> n) = case n of
            Go (y, v1) -> Just (pat `MS.union` y, v1)
            Branch x (y, v1) _  | x `MS.isSubsetOf` pat -> Just ((pat `MS.difference` x) `MS.union` y, v1)
            _ -> Nothing
