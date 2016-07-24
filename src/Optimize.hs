{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables, LambdaCase, ViewPatterns #-}
module Optimize where

import Data.Maybe
import qualified Data.Map.Strict as M
import Control.Monad
import Control.Eff (Member, Eff, run, (:>))
import Control.Eff.Reader.Strict (Reader, ask, runReader)
import Control.Eff.State.Strict (State, get, put, modify, evalState)
import Control.Eff.Writer.Strict (Writer, tell, runWriter, runMonoidWriter)
import qualified Data.MultiSet as MS

import QSet

optimize :: Lbl -> Lbl -> [Instr] -> [SimpInstr]
optimize _ _ instrs = toSimpleInstr =<< instrs
