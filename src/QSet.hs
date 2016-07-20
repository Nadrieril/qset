{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables, TypeOperators, DataKinds, DeriveFunctor #-}
module QSet where

import Data.List
import Data.Maybe
import Data.Void (Void)
import qualified Data.Map.Strict as M
import Control.Monad
import Control.Eff (Member, Eff, run, (:>))
import Control.Eff.State.Strict (State, get, put, evalState)
import Control.Eff.Writer.Strict (Writer, tell, runWriter, censor)


type Var = String
data Instr = (:->) [Var] [Var] | Comment String

instance Show Instr where
    show (l :-> r) = unwords l ++ " > " ++ unwords r
    show (Comment s) = "# "++s

compile :: [Instr] -> String
compile instrs = intercalate "," $ instrs >>= aux
    where
        instrvars (l :-> r) = l ++ r
        instrvars _ = []
        varcount :: M.Map Var Int
        varcount = foldr (\i m -> foldr (M.alter $ Just . maybe 0 (+1)) m (instrvars i)) M.empty instrs
        vars = map snd $ sort $ map (\(a,b)->(b,a)) $ M.toList varcount
        filteredvars = filter (\x -> head x /= 'o' && head x /= 'i') vars
        varmap = M.fromList $ zip filteredvars (map (:[]) $ ['a'..'z']++['A'..'Z']++['0'..'9'])
        lookupvar v = fromMaybe v $ M.lookup v varmap
        aux (l :-> r) = return $ unwords (map lookupvar r) ++ "/" ++ unwords (map lookupvar l)
        aux _ = []



type M r e =
    ( Member (Writer Instr) r
    , Member (Writer Var) r
    , Member (State (M.Map String Int)) r
    ) => Eff r e

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


runBlk :: Int -> Blk (State (M.Map String Int) :> Writer Var :> Writer Instr :> Void) () -> [Instr]
runBlk ninputs b = run $
    fmap fst $ runWriter (:) ([] :: [Instr]) $ do
        (vars, (lstart, lend)) <-
            runWriter (:) ([] :: [Var]) $
            evalState M.empty $ do
                lstart <- newLabelM
                (lend, ()) <- unBlk b lstart
                return (lstart, lend)

        -- clear variables and inputs
        forM_ vars (\v -> tell $ [lend, v] :-> [lend])
        forM_ [0..ninputs-1] (\i -> tell $ [lend, "i"++show i] :-> [lend])
        tell $ [lend] :-> []
        -- Starting point
        tell $ ["i0"] :-> ["i0", lstart]
        return ()



(>>>) :: [Var] -> [Var] -> Blk r ()
(>>>) l r = lift $ tell $ l :-> r

comment :: String -> Blk r ()
comment s = lift $ tell $ Comment s

newLabelM :: M r Var
newLabelM = do
    m :: M.Map String Int <- get
    let i = fromMaybe 0 $ M.lookup "l" m
    put $ M.insert "l" (i+1) m
    return $ "l" ++ show i

newLabel :: Blk r Var
newLabel = lift newLabelM

newVar :: String -> Blk r Var
newVar n = lift $ do
    m :: M.Map String Int <- get
    let i = fromMaybe 0 $ M.lookup n m
    put $ M.insert n (i+1) m
    let v = n ++ show i
    tell v
    return v

crntLabel :: Blk r Var
crntLabel = Blk $ \lstart -> return (lstart, lstart)

endLabel :: Var -> Blk r ()
endLabel lend = Blk $ \_ -> return (lend, ())

runBlkAtLabel :: Var -> Blk r a -> M r (Var, a)
runBlkAtLabel = flip unBlk

ifLabel :: Var -> Blk r a -> Blk r a
ifLabel lbl b =
    let prepend lbl (l :-> r) = (lbl:l) :-> (lbl:r) in
    Blk $ censor (prepend lbl) . unBlk b
