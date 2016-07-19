{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables, TypeOperators, DataKinds, DeriveFunctor #-}
module Main where

import Data.List
import Control.Monad
import Control.Monad.Effect (Effect, runEffect, Row(..))
import Control.Effect.Writer (EffectWriter, Writer, runWriter, tell, censor)
import Control.Effect.State (EffectState, State, runState, put, get)

main :: IO ()
main = do
    let instrs = runBlk 2 prog
    forM_ instrs print
    -- putStrLn $ compile instrs


type Var = String
data Instr = (:->) [Var] [Var]

instance Show Instr where
    show (l :-> r) = unwords l ++ " > " ++ unwords r

compile :: [Instr] -> String
compile = intercalate ", " . map aux
    where aux (l :-> r) = unwords r ++ "/" ++ unwords l



type M r e =
    ( EffectWriter [Instr] r
    , EffectState (Int, Int) r
    ) => Effect r e

data Blk r a = Blk { unBlk :: Var -> M r (Var, a) }
    deriving (Functor)

lift :: M r a -> Blk r a
lift m = Blk $ \l -> (,) l <$> m


instance Applicative (Blk r) where
    pure x = lift $ pure x
    bf <*> bx = Blk $ \lstart -> do
        (lbl1, f) <- unBlk bf lstart
        (lbl2, x) <- unBlk bx lbl1
        return (lbl2, f x)

instance Monad (Blk r) where
    return = pure
    bx >>= bf = Blk $ \lstart -> do
        (lbl1, x) <- unBlk bx lstart
        unBlk (bf x) lbl1


runBlk :: Int -> Blk (State (Int, Int) :+ Writer [Instr] :+ Nil) () -> [Instr]
runBlk ninputs b = runEffect $
    fmap snd $ runWriter $ do
        ((lstart, lend), (lastvar, _)) <- runState (0::Int, 0::Int) $ do
            lstart <- newLabelM
            (lend, ()) <- unBlk b lstart
            return (lstart, lend)

        -- clear variables and inputs
        tell =<< forM [0..lastvar]   (\i -> return $ [lend, "x"++show i] :-> [lend])
        tell =<< forM [0..ninputs-1] (\i -> return $ [lend, "i"++show i] :-> [lend])
        tell [[lend] :-> []]
        -- Starting point
        tell [["i0"] :-> ["i0", lstart]]
        return ()



(>>>) :: [Var] -> [Var] -> Blk r ()
(>>>) l r = lift $ tell [l :-> r]

newLabelM :: M r Var
newLabelM = do
    (i::Int, j::Int) <- get
    put (i, j+1)
    return $ "l" ++ show j

newLabel :: Blk r Var
newLabel = lift newLabelM

newVar :: Blk r Var
newVar = lift $ do
    (i::Int, j::Int) <- get
    put (i+1, j)
    return $ "x" ++ show i

crntLabel :: Blk r Var
crntLabel = Blk $ \lstart -> return (lstart, lstart)

endLabel :: Var -> Blk r ()
endLabel lend = Blk $ \_ -> return (lend, ())

runAtLabel :: Var -> Blk r a -> M r (Var, a)
runAtLabel = flip unBlk


goto :: Var -> Blk r ()
goto lend = do
    lstart <- crntLabel
    [lstart] >>> [lend]
    endLabel lend

tellAtLabel :: Instr -> Blk r ()
tellAtLabel (l :-> r) = do
    lstart <- crntLabel
    (lstart:l) >>> (lstart:r)


ifz :: Var -> Blk r () -> Blk r () -> Blk r ()
ifz x b1 b2 = do
    lbl1 <- newLabel
    lbl2 <- newLabel
    lstart <- crntLabel
    [lstart, x] >>> [x, lbl2]
    [lstart] >>> [lbl1]
    (lend::Var, ()) <- lift $ runAtLabel lbl1 b1
    (_   ::Var, ()) <- lift $ runAtLabel lbl2 (b2 >> goto lend)
    endLabel lend

whennz :: Var -> Blk r () -> Blk r ()
whennz x = ifz x (return ())

whenz :: Var -> Blk r () -> Blk r ()
whenz x = flip (ifz x) (return ())


clear :: Var -> Blk r ()
clear x = do
    tellAtLabel $ [x] :-> []
    newLabel >>= goto

fork :: Var -> [Var] -> Blk r ()
fork x ys = do
    tellAtLabel $ [x] :-> ys
    newLabel >>= goto

move :: Var -> Var -> Blk r ()
move x y = do
    tellAtLabel $ [x] :-> [y]
    newLabel >>= goto

copy :: Var -> [Var] -> Blk r ()
copy x ys = do
    tmp <- newVar
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
    tellAtLabel $ [x, y] :-> res
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
    -- t <- newVar
    -- y <- newVar
    -- tmp <- newVar
    let (t, y, tmp, tmp2) = ("t", "y", "tmp", "tmp2")
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
