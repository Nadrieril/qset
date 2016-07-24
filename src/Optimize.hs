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
    | Loop Pat Pat Target
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
    ForkInstr l1 x l2 y l3 | l1 == l2 -> newNode l1 $ Loop (MS.fromList x) (MS.fromList y) (MS.empty, l3)
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
            Loop x y (z, l3) ->
                [LbldInstr l1 (MS.elems x) l1 (MS.elems y), LbldInstr l1 [] l3 (MS.elems z)]
            Branch x (y, l2) (z, l3) ->
                [LbldInstr l1 (MS.elems x) l2 (MS.elems y), LbldInstr l1 [] l3 (MS.elems z)]



optimize :: Lbl -> Lbl -> [Instr] -> [SimpInstr]
optimize lstart lend instrs = run $
    flip runReader (lstart, lend) $
    evalState (M.empty :: Graph) $ do
        constructInstrGraph instrs
        deconstructGraph <$> get

compileOptimized :: Int -> ([Instr], [Var], Lbl, Lbl) -> [SimpInstr]
compileOptimized ninputs (instrs, vars, lstart, lend) =
    compile ninputs (optimize lstart lend instrs, vars, lstart, lend)
