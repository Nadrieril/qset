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
import Text.Printf (printf)

import QSet


main :: IO ()
main = do
    let instrs = runBlk 2 prog
    forM_ instrs print
    -- putStrLn ""
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
clear x = do
    comment $ printf "clear %s" x
    fork x []

move :: Var -> Var -> Blk r ()
move x y = do
    comment $ printf "move %s %s" x y
    fork x [y]

copy :: Var -> [Var] -> Blk r ()
copy x ys = do
    comment $ printf "copy %s %s" x (show ys)
    tmp <- newVar "cp"
    fork x (tmp:ys)
    move tmp x

incr :: Var -> Blk r ()
incr x = do
    comment $ printf "incr %s" x
    lstart <- crntLabel
    lend <- newLabel
    [lstart] >>> [lend, x]
    endLabel lend

decr :: Var -> Blk r ()
decr x = do
    comment $ printf "decr %s" x
    lstart <- crntLabel
    lend <- newLabel
    [lstart, x] >>> [lend]
    goto lend

add :: Var -> Var -> Var -> Blk r ()
add x y z = do
    comment $ printf "add %s %s %s" x y z
    move x z
    move y z

min_ :: Var -> Var -> [Var] -> Blk r ()
min_ x y res = do
    comment $ printf "min_ %s %s %s" x y (show res)
    atCrntLabel $ [x, y] >>> res
    newLabel >>= goto

sub :: Var -> Var -> Blk r ()
sub x y = do
    comment $ printf "sub %s %s" x y
    atCrntLabel $ [x, y] >>> []
    newLabel >>= goto

prod :: Var -> Var -> Var -> Blk r ()
prod x y z = do
    comment $ printf "prod %s %s %s" x y z
    lstart <- crntLabel
    whennz y $ do
        copy x [z]
        decr y
        goto lstart

euclDiv :: Var -> Var -> Var -> Var -> Blk r ()
euclDiv a b q r = whennz b $ do
    lstart <- crntLabel
    min_ a b [r]
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
    z <- newVar "z"
    incr t
    incr x
    lstart <- crntLabel
    sub x z
    whennz x $ do
        incr t
        incr r
        copy t [z]
        incr t
        decr x
        goto lstart


prog :: Blk r ()
-- prog = prod "i0" "i1" "o0"
-- prog = copy "x" ["y", "z"]
-- prog = euclDiv "i0" "i1" "o0" "o1"
prog = sqrt_ "i0" "o0"
