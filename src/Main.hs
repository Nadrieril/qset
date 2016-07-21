{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables, TypeOperators, DataKinds #-}
module Main where

import Data.Maybe
import Control.Monad
import Text.Printf (printf)
import qualified Data.IntMap.Strict as IM

import QSet
import Eval


main :: IO ()
main = do
    let instrs = runBlk 5 prog

    let testcases = [[3, 4], [100, 20], [20, 100], [150, 150], [397, 397]]
    let prof = profile instrs testcases
    forM_ (zip [0..] instrs) $ \(linei, line) -> do
        let percentSteps = fromMaybe 0 $ IM.lookup linei prof
        putStrLn $ printf "% 3d. %s   # %.2f%%" linei (show line) (100 * percentSteps)
    -- putStrLn ""

    -- putStrLn $ compile instrs
    -- putStrLn ""

    -- let (_, steps, finalState) = evalProg instrs [397, 397]
    -- print (finalState, steps)
    -- print $ evalProg instrs [3, 7, 5]
    -- print $ evalProg instrs [397, 397, 5]


prog :: Blk r ()
prog = prod "i0" "i1" "o0"
-- prog = sqrt_ "i0" "o0"
-- prog = rsa "i0" "i1" "i2" "o0"


profile :: [Instr] -> [[Int]] -> IM.IntMap Float
profile prog testcases =
    let profFracs = flip map testcases $ \tc ->
            let (prof, steps, _) = evalProg prog tc in
            fmap (\x -> fromIntegral x / fromIntegral steps) prof
        profFrac = (/ fromIntegral (length testcases)) <$> IM.unionsWith (+) profFracs
    in profFrac


reproduce :: Int -> [a] -> [a]
reproduce n l = concat $ replicate n l

goto :: Var -> Blk r ()
goto lend = do
    lstart <- getLabel
    [lstart] >>> [lend]
    newLabel >>= setLabel

changeLabel :: Var -> Blk r ()
changeLabel lend = do
    lstart <- getLabel
    [lstart] >>> [lend]
    setLabel lend

atCrntLabel :: Blk r a -> Blk r a
atCrntLabel b = do
    lstart <- getLabel
    ifLabel lstart b


ifz :: Var -> Blk r () -> Blk r () -> Blk r ()
ifz x b1 b2 = do
    lbl1 <- newLabel
    lbl2 <- newLabel
    lstart <- getLabel
    [lstart, x] >>> [x, lbl2]
    [lstart] >>> [lbl1]
    (lend::Var, ()) <- lift $ runBlkAtLabel lbl1 b1
    (_   ::Var, ()) <- lift $ runBlkAtLabel lbl2 (b2 >> goto lend)
    setLabel lend

whennz :: Var -> Blk r () -> Blk r ()
whennz x = ifz x (return ())

whenz :: Var -> Blk r () -> Blk r ()
whenz x = flip (ifz x) (return ())


fork :: Var -> [Var] -> Blk r ()
fork x ys = do
    atCrntLabel $ [x] >>> ys
    newLabel >>= changeLabel

clear :: Var -> Blk r ()
clear x = do
    comment $ printf "clear %s" x
    fork x []

move :: Var -> Var -> Blk r ()
move x y = do
    comment $ printf "move %s %s" x y
    fork x [y]

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
    fork x (tmp:ys)
    move tmp x

incr :: Var -> Blk r ()
incr x = do
    comment $ printf "incr %s" x
    lstart <- getLabel
    lend <- newLabel
    [lstart] >>> [lend, x]
    setLabel lend

decr :: Var -> Blk r ()
decr x = do
    comment $ printf "decr %s" x
    lstart <- getLabel
    lend <- newLabel
    [lstart, x] >>> [lend]
    changeLabel lend

add :: Var -> Var -> Var -> Blk r ()
add x y z = do
    comment $ printf "add %s %s %s" x y z
    move x z
    move y z

min_ :: Var -> Var -> [Var] -> Blk r ()
min_ x y res = do
    comment $ printf "min_ %s %s %s" x y (show res)
    atCrntLabel $ [x, y] >>> res
    newLabel >>= changeLabel

sub :: Var -> Var -> Blk r ()
sub x y = do
    comment $ printf "sub %s %s" x y
    atCrntLabel $ [x, y] >>> []
    newLabel >>= changeLabel

prod :: Var -> Var -> Var -> Blk r ()
prod x y z = do
    comment $ printf "prod %s %s %s" x y z
    whilenz y $ do
        fcopy x [z]
        decr y

euclDiv :: Var -> Var -> Var -> Var -> Blk r ()
euclDiv a b q r = whennz b $ do
    lstart <- getLabel
    fmin_ a b [r]
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
    sub x z
    whilenz x $ do
        incr t
        incr r
        copy t [z]
        incr t
        decr x


submod :: Var -> Var -> Var -> Blk r ()
submod x y n = do
    comment $ printf "submod %s %s %s" x y n
    tmp <- newVar "cp"
    fsub x y
    whilenz y $ do
        clear x
        atCrntLabel $ reproduce 5 [n, y] >>> reproduce 5 [tmp]
        atCrntLabel $ [n, y] >>> [tmp]
        atCrntLabel $ reproduce 5 [n] >>> reproduce 5 [tmp, x]
        atCrntLabel $ [n] >>> [tmp, x]
        changeToNewLabel
        fmove tmp n

whilenz :: Var -> Blk r a -> Blk r ()
whilenz x b = do
    lstart <- getLabel
    whennz x $ b >> goto lstart



ffork :: Var -> [Var] -> Blk r ()
ffork x ys = do
    let n = 5
    atCrntLabel $ reproduce n [x] >>> reproduce n ys
    atCrntLabel $ [x] >>> ys
    changeToNewLabel

fclear :: Var -> Blk r ()
fclear x = do
    comment $ printf "clear %s" x
    ffork x []

fmove :: Var -> Var -> Blk r ()
fmove x y = do
    comment $ printf "move %s %s" x y
    ffork x [y]

fswap :: Var -> Var -> Blk r ()
fswap x y = do
    comment $ printf "swap %s %s" x y
    tmp <- newVar "swp"
    fmove x tmp
    fmove y x
    fmove tmp y

fcopy :: Var -> [Var] -> Blk r ()
fcopy x ys = do
    comment $ printf "copy %s %s" x (show ys)
    tmp <- newVar "cp"
    ffork x (tmp:ys)
    fmove tmp x

fmin_ :: Var -> Var -> [Var] -> Blk r ()
fmin_ x y res = do
    comment $ printf "min_ %s %s %s" x y (show res)
    let n = 5
    atCrntLabel $ reproduce n [x, y] >>> reproduce n res
    atCrntLabel $ [x, y] >>> res
    changeToNewLabel

fsub :: Var -> Var -> Blk r ()
fsub x y = do
    comment $ printf "sub %s %s" x y
    atCrntLabel $ reproduce 5 [x, y] >>> []
    atCrntLabel $ [x, y] >>> []
    changeToNewLabel

bezout :: Var -> Var -> Var -> Blk r ()
bezout r0 b s0 = do
    [q, _, r1, r, _, s1, tmp0] <- mapM newVar
        ["q", "r", "r", "r", "s", "s", "tmp"]
    copy b [r1]
    incr s0

    comment "main loop"
    whilenz r1 $ do
        fcopy r1 [tmp0]
        comment "euclDiv r0 r1 q r"
        euclDiv r0 r1 q r
        clear r0
        fmove tmp0 r0
        clear r1
        fmove r r1

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
