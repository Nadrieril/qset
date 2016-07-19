{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables, TypeOperators, DataKinds #-}
module Main where

import Data.List
import Data.Maybe
import Data.Void (Void)
import qualified Data.Map.Strict as M
import Control.Monad
import Control.Eff (Member, Eff, run, (:>))
import Control.Eff.State.Strict (State, get, put, evalState)
import Control.Eff.Writer.Strict (Writer, tell, runWriter, censor)

import QSet


main :: IO ()
main = do
    let instrs = runBlk 2 prog
    forM_ instrs print
    -- putStrLn $ compile instrs



goto :: Var -> Blk r ()
goto lend = do
    lstart <- crntLabel
    [lstart] >>> [lend]
    endLabel lend

atCrntLabel :: Blk r a -> Blk r a
atCrntLabel b = do
    lstart <- crntLabel
    ifLabel lstart b


ifz :: Var -> Blk r () -> Blk r () -> Blk r ()
ifz x b1 b2 = do
    lbl1 <- newLabel
    lbl2 <- newLabel
    lstart <- crntLabel
    [lstart, x] >>> [x, lbl2]
    [lstart] >>> [lbl1]
    (lend::Var, ()) <- lift $ runBlkAtLabel lbl1 b1
    (_   ::Var, ()) <- lift $ runBlkAtLabel lbl2 (b2 >> goto lend)
    endLabel lend

whennz :: Var -> Blk r () -> Blk r ()
whennz x = ifz x (return ())

whenz :: Var -> Blk r () -> Blk r ()
whenz x = flip (ifz x) (return ())


fork :: Var -> [Var] -> Blk r ()
fork x ys = do
    atCrntLabel $ [x] >>> ys
    newLabel >>= goto

clear :: Var -> Blk r ()
clear x = fork x []

move :: Var -> Var -> Blk r ()
move x y = fork x [y]

copy :: Var -> [Var] -> Blk r ()
copy x ys = do
    tmp <- newVar "copy"
    fork x (tmp:ys)
    move tmp x

incr :: Var -> Blk r ()
incr x = do
    lstart <- crntLabel
    lend <- newLabel
    [lstart] >>> [lend, x]
    endLabel lend

incr2 :: Var -> Blk r ()
incr2 x = do
    lstart <- crntLabel
    lend <- newLabel
    [lstart] >>> [lend, x, x]
    endLabel lend

decr :: Var -> Blk r ()
decr x = do
    lstart <- crntLabel
    lend <- newLabel
    [lstart, x] >>> [lend]
    goto lend

add :: Var -> Var -> Var -> Blk r ()
add x y z = do
    move x z
    move y z

sub :: Var -> Var -> [Var] -> Blk r ()
sub x y res = do
    atCrntLabel $ [x, y] >>> res
    newLabel >>= goto

prod :: Var -> Var -> Var -> Blk r ()
prod x y z = do
    lstart <- crntLabel
    whennz y $ do
        copy x [z]
        decr y
        goto lstart

euclDiv :: Var -> Var -> Var -> Var -> Blk r ()
euclDiv a b q r = whennz b $ do
    lstart <- crntLabel
    sub a b [r]
    ifz a
        (whenz b $ do
            incr q
            clear r)
        (do incr q
            move r b
            goto lstart)

sqrt_ :: Var -> Var -> Blk r ()
sqrt_ x r = do
    t <- newVar "t"
    y <- newVar "y"
    tmp <- newVar "tmp"
    tmp2 <- newVar "tmp"
    incr t
    incr x
    lstart <- crntLabel
    whennz x $ do
        decr x
        copy t [tmp]
        sub y tmp [tmp2]
        incr y
        ifz tmp
            (do clear tmp2
                incr r
                incr2 t)
            (do clear tmp
                move tmp2 y)
        goto lstart


prog :: Blk r ()
-- prog = prod "i0" "i1" "o0"
-- prog = copy "x" ["y", "z"]
-- prog = euclDiv "i0" "i1" "o0" "o1"
prog = sqrt_ "i0" "o0"
