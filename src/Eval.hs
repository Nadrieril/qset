{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables, TypeOperators, DataKinds #-}
module Eval where

import Data.List
import Data.Maybe
import Control.Monad
import Control.Eff (Member, Eff, run)
import Control.Eff.State.Strict (State, get, put, modify, execState, runState)
import qualified Data.MultiSet as MS
import qualified Data.IntMap.Strict as IM

import QSet


type Eval r e =
    ( Member (State (MS.MultiSet Var)) r
    , Member (State Int) r
    , Member (State (IM.IntMap Int)) r
    ) => Eff r e

data Rule = Rule Int [Var] [Var]

instrsToRules :: [Instr] -> [Rule]
instrsToRules instrs = mapMaybe aux $ zip [(0::Int)..] instrs
    where
        aux (li, l :-> r) = Just $ Rule li l r
        aux _ = Nothing


evalRule :: Rule -> Eval r Bool
evalRule (Rule _ l r) = do
    let ls = MS.fromList l
    let rs = MS.fromList r
    ms <- get
    if ls `MS.isSubsetOf` ms
        then do
            put ((ms `MS.difference` ls) `MS.union` rs)
            return True
        else return False

stepProg :: [Rule] -> Eval r Bool
stepProg = loop
    where
        loop :: [Rule] -> Eval r Bool
        loop [] = return False
        loop ((r@(Rule l _ _)):q) = do
            b <- evalRule r
            if b then do
                    modify (IM.alter (Just . (+1) . fromMaybe (0::Int)) l)
                    return True
                 else loop q

eval :: [Rule] -> Eval r ()
eval prog = loop True
    where
        loop :: Bool -> Eval r ()
        loop continue = when continue $ do
            modify (+ (1::Int))
            stepProg prog >>= loop

evalProg :: [Instr] -> [Int] -> (IM.IntMap Int, Int, [Int])
evalProg prog initialState =
    let initialMS = (MS.fromOccurList $ zip ["i"++show i | i <- [(0::Int)..]] initialState) in
    let (prof, (steps, finalMS)) = run $
            runState IM.empty $
            runState (0::Int) $
            execState initialMS $
            eval (instrsToRules prog) in
    let finalState = [ i | (v, i) <- sort $ MS.toOccurList finalMS, head v == 'o' ] in
    (prof, steps, finalState)
