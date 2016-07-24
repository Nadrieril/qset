{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables, TypeOperators, DeriveFunctor, LambdaCase, PatternSynonyms #-}
module QSet (
              Var
            , Lbl
            , Instr(..)
            , Blk
            , loop
            , ifz
            , goto
            , transition
            , pattern (:->)
            , toSimpleInstr
            , comment
            , newVar
            , getLabel
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
    | LbldInstr Lbl [Var] Lbl [Var]
    | ForkInstr Lbl [Var] Lbl [Var] Lbl


toSimpleInstr :: Instr -> [Instr]
toSimpleInstr (LbldInstr l1 x l2 y) = [SimpInstr (l1:x) (l2:y)]
toSimpleInstr (ForkInstr l1 x l2 y l3) = [LbldInstr l1 x l2 y, LbldInstr l1 [] l3 []] >>= toSimpleInstr
toSimpleInstr i = [i]


pattern (:->) x y <- SimpInstr x y where
        (:->) x y = SimpInstr x y

instance Show Instr where
    show (Comment s) = "# "++s
    show i = intercalate ", " $ map aux $ toSimpleInstr i
        where aux (l :-> r) = unwords l ++ " > " ++ unwords r
              aux _ = undefined

compile :: [Instr] -> String
compile instrs = intercalate "," $ instrs >>= toSimpleInstr >>= aux
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
        forM_ (vars ++ inputs) (\v -> tellOne $ LbldInstr lend [v] lend [])
        -- Ending point
        tellOne $ [lend] :-> []
        -- Starting point
        tellOne $ ["i0"] :-> ["i0", lstart]
        return ()


tellOne :: (Typeable w, Member (Writer [w]) r) => w -> Eff r ()
tellOne = tell . (:[])

tellOneB :: Instr -> Blk r ()
tellOneB i = lift $ tellOne i

censorB :: ([Instr] -> [Instr]) -> Blk r a -> Blk r a
censorB f b = Blk $ censor f . unBlk b


comment :: String -> Blk r ()
comment s = tellOneB $ Comment s

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



transition :: [Var] -> [Var] -> Blk r ()
transition l r = do
    lstart <- getLabel
    lend <- newLabel
    tellOneB $ if null l
        then LbldInstr lstart [] lend r
        else ForkInstr lstart l lend r lend
    setLabel lend

loop :: [Var] -> [Var] -> Blk r ()
loop l r = do
    lstart <- getLabel
    lend <- newLabel
    tellOneB $ if null l
        then LbldInstr lstart [] lstart r
        else ForkInstr lstart l lstart r lend
    setLabel lend

goto :: Lbl -> Blk r ()
goto lend = do
    lstart <- getLabel
    tellOneB $ LbldInstr lstart [] lend []
    setLabel lend

ifz :: Var -> Blk r () -> Blk r () -> Blk r ()
ifz x b1 b2 = do
    lstart <- getLabel
    lbl1 <- newLabel
    lbl2 <- newLabel
    lend <- newLabel
    tellOneB $ ForkInstr lstart [x] lbl2 [x] lbl1

    setLabel lbl1
    b1 >> goto lend

    setLabel lbl2
    b2 >> goto lend

    setLabel lend


faster :: Int -> Blk r a -> Blk r a
faster n =
    censorB (>>= \case
        SimpInstr l r -> [SimpInstr (reproduce n l) (reproduce n r), SimpInstr l r]
        i@(LbldInstr _ _ [] []) -> [i]
        LbldInstr l1 l l2 r | l1 == l2 -> [LbldInstr l1 (reproduce n l) l2 (reproduce n r), LbldInstr l1 l l2 r]
        i@LbldInstr{} -> [i]
        ForkInstr l1 l l2 r l3 | l1 == l2 -> [LbldInstr l1 (reproduce n l) l2 (reproduce n r), ForkInstr l1 l l2 r l3]
        i@ForkInstr{} -> [i]
        Comment s -> [Comment s]
    )
    where reproduce n l = concat $ replicate n l
