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


submod :: Var -> Var -> Var -> Blk r ()
submod x y n = do
    comment $ printf "submod %s %s %s" x y n
    sub x y
    lbl1 <- crntLabel
    tmp <- newVar "cp"
    whennz y $ do
        clear x
        atCrntLabel $ [n, y] >>> [tmp]
        atCrntLabel $ [n] >>> [tmp, x]
        newLabel >>= goto
        move tmp n
        goto lbl1
    newLabel >>= goto

bezout :: Var -> Var -> Var -> Blk r ()
bezout a b s0 = do
    [q, r0, r1, r, _, s1, tmp0] <- mapM newVar
        ["q", "r", "r", "r", "s", "s", "tmp"]
    move a r0
    copy b [r1]
    incr s0
    lstart <- crntLabel
    comment "main loop"
    whennz r1 $ do
        copy r1 [tmp0]
        comment "euclDiv r0 r1 q r"
        euclDiv r0 r1 q r
        clear r0
        move tmp0 r0
        clear r1
        move r r1

        prod s1 q tmp0

        submod s0 tmp0 b

        move s1 tmp0
        move s0 s1
        move tmp0 s0

        goto lstart
    comment "cleanup"



prog :: Blk r ()
-- prog = prod "i0" "i1" "o0"
-- prog = copy "x" ["y", "z"]
-- prog = euclDiv "i0" "i1" "o0" "o1"
-- prog = sqrt_ "i0" "o0"
prog = bezout "i0" "i1" "o0"

-- [397, 397, 5] -> 125453
-- [3, 7, 5] -> 5

-- [5, 156816] -> 125453
-- [5, 12] -> 5
-- [11, 32] -> 3
-- [13, 40] -> 37
