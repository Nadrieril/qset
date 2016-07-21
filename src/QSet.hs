{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables, TypeOperators, DataKinds, DeriveFunctor, LambdaCase, PatternSynonyms, ViewPatterns #-}
module QSet (
              Var
            , Lbl
            , Instr(..)
            , Blk
            , (>>>)
            , (|->)
            , pattern (:->)
            , comment
            , newLabel
            , newVar
            , getLabel
            , setLabel
            , faster
            , runBlk
            , compile
            ) where

import Data.List
import Data.Maybe
import Data.Typeable
import Data.Void (Void)
import qualified Data.Map.Strict as M
import Control.Monad
import Control.Eff (Member, Eff, run, (:>))
import Control.Eff.State.Strict (State, get, put, evalState)
import Control.Eff.Writer.Strict (Writer, tell, runWriter, runMonoidWriter, censor)


type Var = String
type Lbl = String
data Instr = Comment String
    | SimpInstr [Var] [Var]
    | LbldInstr Lbl Lbl [Var] [Var]

pattern (:->) x y <- (\case
                SimpInstr x y -> Just (x, y)
                LbldInstr l1 l2 x y -> Just (l1:x, l2:y)
                _ -> Nothing
            -> Just (x, y)) where
        (:->) x y = SimpInstr x y

instance Show Instr where
    show (l :-> r) = unwords l ++ " > " ++ unwords r
    show (Comment s) = "# "++s
    show _ = undefined

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
    ( Member (Writer [Instr]) r
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


runBlk :: Int -> Blk (State (M.Map String Int) :> Writer Var :> Writer [Instr] :> Void) () -> [Instr]
runBlk ninputs b = run $
    fmap fst $ runMonoidWriter $ do
        (vars, (lstart, lend)) <-
            runWriter (:) ([] :: [Var]) $
            evalState M.empty $ do
                lstart <- newLabelM
                (lend, ()) <- unBlk b lstart
                return (lstart, lend)

        -- clear variables and inputs
        let inputs = map (\i -> "i"++show i) [0..ninputs-1]
        forM_ (vars ++ inputs) (\v -> tellOne $ LbldInstr lend lend [v] [])
        -- Ending point
        tellOne $ [lend] :-> []
        -- Starting point
        tellOne $ ["i0"] :-> ["i0", lstart]
        return ()


tellOne :: (Typeable w, Member (Writer [w]) r) => w -> Eff r ()
tellOne = tell . (:[])

censorB :: ([Instr] -> [Instr]) -> Blk r a -> Blk r a
censorB f b = Blk $ censor f . unBlk b


(>>>) :: [Var] -> [Var] -> Blk r ()
(>>>) l r = do
    lbl <- getLabel
    lift $ tellOne $ LbldInstr lbl lbl l r

(|->) :: Blk r () -> Var -> Blk r ()
(|->) b lbl = do
    clbl <- getLabel
    censorB (map $ \case
            SimpInstr l r -> LbldInstr clbl lbl l r
            LbldInstr l1 _ l r -> LbldInstr l1 lbl l r
            i -> i
        ) b


comment :: String -> Blk r ()
comment s = lift $ tellOne $ Comment s

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

getLabel :: Blk r Var
getLabel = Blk $ \lstart -> return (lstart, lstart)

setLabel :: Var -> Blk r ()
setLabel lend = Blk $ \_ -> return (lend, ())


faster :: Int -> Blk r a -> Blk r a
faster n =
    censorB (>>= \case
        SimpInstr l r -> [SimpInstr (reproduce n l) (reproduce n r), SimpInstr l r]
        i@(LbldInstr _ _ [] []) -> [i]
        LbldInstr l1 l2 l r | l1 == l2 -> [LbldInstr l1 l2 (reproduce n l) (reproduce n r), LbldInstr l1 l2 l r]
        i -> [i]
    )
    where reproduce n l = concat $ replicate n l
