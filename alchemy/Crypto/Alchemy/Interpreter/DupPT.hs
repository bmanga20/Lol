{-# LANGUAGE TypeFamilies #-}

module Crypto.Alchemy.Interpreter.DupPT where

import Crypto.Alchemy.Language.CT
import Crypto.Alchemy.Language.Lam

dupPT :: Dup expr1 expr2 i (d :: Depth) a -> (expr1 d a, expr2 d a)
dupPT (Dup a b) = (a,b)

data Dup expr1 expr2 i a = Dup {unDupA :: expr1 a, unDupB :: expr2 a}
