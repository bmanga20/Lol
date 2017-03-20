{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTSyntax          #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE TypeOperators       #-}

module Crypto.Alchemy.Interpreter.PTEval where

import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.PT
import Crypto.Lol
import Crypto.Lol.Types.ZPP
import Crypto.Lol.Cyclotomic.Tensor

-- EAC: Another data type that requirs a CUSK (i.e., kind sigs for all vars)
-- | Metacircular evaluator with depth.
newtype ID (d :: k) (a :: *) = ID {unID :: a} deriving (Show, Eq)

-- | Metacircular lambda with depth.
instance LambdaD ID where
  lamD f   = ID $ unID . f . ID
  appD f a = ID $ unID f $ unID a

-- | Metacircular plaintext symantics.
instance SymPT ID where
  a +# b = ID $ unID a + unID b
  neg a = ID $ negate $ unID a
  a *# b = ID $ unID a * unID b
  addPublicPT a b = ID $ a + unID b
  mulPublicPT a b = ID $ a * unID b

  tunnelPT linf = ID . evalLin linf . unID
