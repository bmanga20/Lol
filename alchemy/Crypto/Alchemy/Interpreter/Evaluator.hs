{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Crypto.Alchemy.Interpreter.Evaluator where

import Algebra.Additive as Additive (C)
import Algebra.Ring as Ring (C)

import Crypto.Alchemy.Lam
import Crypto.Alchemy.CTLang
import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE

import Data.Constraint

-- | Metacircular evaluator.
newtype I a = I { unI :: a }
  deriving (Eq, Show, Additive.C, Ring.C)

-- | Metacircular lambda.
instance Lambda I where
  lam f   = I $ unI . f . I
  app f a = I $ unI f $ unI a

-- | Metacircular ciphertext symantics.
instance SymCT I where
  entailRingSymCT = tag $ Sub Dict
  rescaleCT = I . rescaleLinearCT . unI
  addPublicCT a = I . addPublic a . unI