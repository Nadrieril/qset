{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables, TypeOperators, DataKinds #-}
module Main where

import Data.Maybe
import Control.Monad(forM_, when)
import Text.Printf (printf)
import qualified Data.IntMap.Strict as IM

import QSet
import Eval


main :: IO ()
main = do
    -- let testcases = [[3, 4], [100, 20], [20, 100], [150, 150], [397, 397]]
    -- let prog = prod "i0" "i1" "o0"
    -- let testcases = [[2*2], [12*12], [10*10], [15*15]]
    -- let prog = sqrt_ "i0" "o0"
    -- let testcases = [[397, 397, 5]]
    let testcases = [[3, 7, 5], [29, 47, 5], [37, 43, 11], [5, 13, 17], [37, 5, 11], [37, 37, 11], [7, 17, 7], [3, 3, 3]]
    -- let prog = faster 6 $ rsa "i0" "i1" "i2" "o0"
    let prog = rsa "i0" "i1" "i2" "o0"

    let doProfile = False
    let doTest = Just 1
    let doCompile = False



    let instrs = runBlk 5 prog >>= toSimpleInstr

    if doProfile
        then do
            let prof = profile instrs testcases
            forM_ (zip [0..] instrs) $ \(linei, line) -> do
                let percentSteps = fromMaybe 0 $ IM.lookup linei prof
                putStrLn $ printf "% 3d. %s   # %.2f%%" linei (show line) (100 * percentSteps)
        else forM_ instrs print
    putStrLn ""

    when doCompile $ do
        putStrLn $ compile instrs
        putStrLn ""

    when (isJust doTest) $ do
        let (_, steps, finalState) = evalProg instrs $ testcases !! fromJust doTest
        print (finalState, steps)




profile :: [Instr] -> [[Int]] -> IM.IntMap Float
profile prog testcases =
    let profFracs = flip map testcases $ \tc ->
            let (prof, steps, _) = evalProg prog tc in
            fmap (\x -> fromIntegral x / fromIntegral steps) prof
        profFrac = (/ fromIntegral (length testcases)) <$> IM.unionsWith (+) profFracs
    in profFrac



(>>>) = transition

(>=>) = loop

whennz :: Var -> Blk r () -> Blk r ()
whennz x = ifz x (return ())

whenz :: Var -> Blk r () -> Blk r ()
whenz x = flip (ifz x) (return ())

whilenz :: Var -> Blk r a -> Blk r ()
whilenz x b = do
    comment $ printf "whilenz %s" x
    lstart <- getLabel
    whennz x $ b >> goto lstart


clear :: Var -> Blk r ()
clear x = do
    comment $ printf "clear %s" x
    [x] >=> []

move :: Var -> Var -> Blk r ()
move x y = do
    comment $ printf "move %s %s" x y
    [x] >=> [y]

swap :: Var -> Var -> Blk r ()
swap x y = do
    comment $ printf "swap %s %s" x y
    tmp <- newVar "swp"
    move x tmp
    move y x
    move tmp y

copy :: Var -> [Var] -> Blk r ()
copy x ys = do
    comment $ printf "copy %s %s" x (show ys)
    tmp <- newVar "cp"
    [x] >=> (tmp:ys)
    move tmp x

incr :: Var -> Blk r ()
incr x = do
    comment $ printf "incr %s" x
    [] >>> [x]

decr :: Var -> Blk r ()
decr x = do
    comment $ printf "decr %s" x
    [x] >>> []

add :: Var -> Var -> Var -> Blk r ()
add x y z = do
    comment $ printf "add %s %s %s" x y z
    move x z
    move y z

sub :: Var -> Var -> Blk r ()
sub x y = do
    comment $ printf "sub %s %s" x y
    [x, y] >=> []

prod :: Var -> Var -> Var -> Blk r ()
prod x y z = do
    comment $ printf "prod %s %s %s" x y z
    whilenz y $ do
        copy x [z]
        decr y

euclDiv :: Var -> Var -> Var -> Var -> Blk r ()
euclDiv a b q r = whennz b $ do
    lstart <- getLabel
    [a, b] >=> [r]
    whennz a $ do
        incr q
        move r b
        goto lstart
    whenz b $ do
        incr q
        clear r

sqrt_ :: Var -> Var -> Blk r ()
sqrt_ x r = do
    t <- newVar "t"
    z <- newVar "z"
    incr t
    incr x
    lstart <- getLabel
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
    tmp <- newVar "cp"
    sub x y
    whilenz y $ do
        clear x
        [n, y] >=> [tmp]
        [n] >=> [tmp, x]
        move tmp n


bezout :: Var -> Var -> Var -> Blk r ()
bezout r0 b s0 = do
    [q, _, r1, r, _, s1, tmp0] <- mapM newVar
        ["q", "r", "r", "r", "s", "s", "tmp"]
    copy b [r1]
    incr s0

    comment "main loop"
    whilenz r1 $ do
        copy r1 [tmp0]
        comment "euclDiv r0 r1 q r"
        euclDiv r0 r1 q r
        clear r0
        move tmp0 r0
        clear r1
        move r r1

        prod s1 q tmp0
        submod s0 tmp0 b

        swap s0 s1

    comment "cleanup"

rsa :: Var -> Var -> Var -> Var -> Blk r ()
rsa a b e ret = do
    n <- newVar "n"
    decr a
    decr b
    prod a b n
    bezout e n ret
