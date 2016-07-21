{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables, TypeOperators, DataKinds #-}
module Eval where

import Data.List
import Control.Monad
import Control.Eff (Member, Eff, run)
import Control.Eff.State.Strict (State, get, put, modify, execState, runState)
import qualified Data.MultiSet as MS

import QSet


type Eval r e =
    ( Member (State (MS.MultiSet Var)) r
    , Member (State Int) r
    ) => Eff r e

evalInstr :: Instr -> Eval r Bool
evalInstr (Comment _) = return False
evalInstr (l :-> r) = do
    let ls = MS.fromList l
    let rs = MS.fromList r
    ms <- get
    if ls `MS.isSubsetOf` ms
        then do
            put ((ms `MS.difference` ls) `MS.union` rs)
            return True
        else return False

stepProg :: [Instr] -> Eval r Bool
stepProg = loop
    where
        loop :: [Instr] -> Eval r Bool
        loop [] = return False
        loop (i:q) = do
            b <- evalInstr i
            if b then return True
                 else loop q

eval :: [Instr] -> Eval r ()
eval prog = loop True
    where
        loop :: Bool -> Eval r ()
        loop continue = when continue $ do
            modify (+ (1::Int))
            stepProg prog >>= loop

evalProg :: [Instr] -> [Int] -> (Int, [Int])
evalProg prog initialState =
    let initialMS = (MS.fromOccurList $ zip ["i"++show i | i <- [(0::Int)..]] initialState) in
    let (steps, finalMS) = run $
            runState (0::Int) $
            execState initialMS $
            eval prog in
    let finalState = [ i | (v, i) <- sort $ MS.toOccurList finalMS, head v == 'o' ] in
    (steps, finalState)
