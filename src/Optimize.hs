{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables, LambdaCase, ViewPatterns, TypeOperators, DeriveFunctor, DeriveFoldable, DeriveTraversable, TupleSections #-}
module Optimize where

import Data.List
import Data.Maybe
import Control.Monad
import Control.Eff (Member, Eff, run, (:>))
import Control.Eff.Reader.Strict (Reader, ask, runReader)
import Control.Eff.State.Strict (State, get, modify, evalState)
import Control.Eff.Writer.Strict (tell, runMonoidWriter)
import qualified Data.IntMap.Strict as IM
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

type Graph = IM.IntMap (GNode Vertex)


insertNode :: Vertex -> Node (Target Vertex) -> Graph -> Graph
insertNode v node graph =
    if isJust $ IM.lookup v graph
        then error $ "Duplicate label: " ++ show v
        else IM.insert v (GNode v node) graph

constructInstrGraph :: [Instr] -> Graph
constructInstrGraph = flip foldr IM.empty $ \i g ->
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
    , Member (State Vertex) r
    , Member (Reader (Vertex, Vertex)) r
    ) => Eff r e

getNode :: Vertex -> G r (Maybe (GNode Vertex))
getNode v = do
    graph <- get
    return $ v `IM.lookup` graph

newVertex :: G r Vertex
newVertex = do
    modify (+(1::Vertex))
    get

insertNodeM :: Vertex -> Node (Target Vertex) -> G r ()
insertNodeM v n = modify $ insertNode v n

optimize :: Lbl -> Lbl -> [Instr] -> [SimpInstr]
optimize lstart lend instrs =
    let graph = constructInstrGraph instrs in
    run $
    flip runReader (lblToVertex lstart, lblToVertex lend) $
    evalState (fst $ IM.findMax graph) $
    evalState graph $ do
        pathCompress
        loopFusion
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
    let gnode' = GNode v $ fmap compress node
    modify $ IM.insert v gnode'
    return $ Just gnode'

    where
        compress :: Target (a, Maybe (GNode a)) -> Target a
        compress (p, (v, n)) = fromMaybe (p, v) (compressAux p =<< n)

        compressAux :: Pat -> GNode a -> Maybe (Target a)
        compressAux pat (gnode -> n) = case n of
            Go (y, v1) -> Just (pat `MS.union` y, v1)
            Branch x (y, v1) _  | x `MS.isSubsetOf` pat -> Just ((pat `MS.difference` x) `MS.union` y, v1)
            _ -> Nothing

loopFusion :: G r ()
loopFusion = void $ dfsFold [] $ \(GNode v node) -> do
    node <- case node of
        Branch _ (_, (v1, _)) (_, (_, m2)) | v1 == v ->
            return $ fmap (\(p, (v, _)) -> (p, (v, m2))) node
        _ -> return node

    node <- case node of
        Go (x, (v1, m1)) -> do
            (_, x) <- return $ fusion False MS.empty x m1
            return $ Go (x, (v1, m1))
        Branch x (y, (v1, m1)) (z, (v2, m2)) -> do
            (_, y) <- return $ fusion False x y m1
            (_, z) <- return $ fusion False MS.empty z m2
            if v1 == v then do
                (x', y') <- return $ superFusion x y m1
                if x == x'
                    then return $ Branch x (y', (v1, m1)) (z, (v2, m2))
                    else do
                        v' <- newVertex
                        insertNodeM v' $ Branch x (y, v') (z, v2)
                        return $ Branch x' (y', (v1, m1)) (z, (v', m2))
            else return $ Branch x (y, (v1, m1)) (z, (v2, m2))


    modify $ IM.insert v $ GNode v $ fmap (fmap fst) node

    return $ case node of
        Go (_, (_, m1)) -> m1
        Branch x (y, (v1, _)) (_, (_, _)) | v1 == v && x `MS.isSubsetOf` y ->
            error $ "infinite loop at label l" ++ show v
        Branch x (y, (v1, _)) (_, (_, m2)) | v1 == v ->
            (x, y) : flip filter m2
                        (\(src, tgt) ->
                            null (MS.intersection x src)
                         && null (MS.intersection x tgt)
                         && null (MS.intersection y src)
                        )
        Branch _ (_, (_, m1)) (_, (_, m2)) ->
            m1 `intersect` m2

    where
        superFusion = fusion True
        fusion :: Bool -> Pat -> Pat -> [(Pat, Pat)] -> (Pat, Pat)
        fusion super sink pat m = loop (sink, pat)
            where
                loop :: (Pat, Pat) -> (Pat, Pat)
                loop (sink, pat) =
                    let nonConflicts = filter (not . conflicts (sink, pat)) m in
                    case find (canReplace (sink, pat)) nonConflicts of
                        Just (src, tgt) -> loop $ replace (sink, pat) (src, tgt)
                        Nothing | not super -> (sink, pat)
                        Nothing -> case find (canReplacePartial (sink, pat)) nonConflicts of
                            Nothing -> (sink, pat)
                            Just (src, tgt) -> loop $ replace (sink, pat) (src, tgt)

                conflicts (sink, _) (_, tgt) = not $ null $ sink `MS.intersection` tgt
                canReplace (_, pat) (src, _) = src `MS.isSubsetOf` pat
                canReplacePartial (_, pat) (src, _) = not (null (src `MS.intersection` pat))

                replace :: (Pat, Pat) -> (Pat, Pat) -> (Pat, Pat)
                replace (sink, pat) (src, tgt) =
                    ( sink `MS.union` (src `MS.difference` pat)
                    , tgt `MS.union` (pat `MS.difference` src) )
