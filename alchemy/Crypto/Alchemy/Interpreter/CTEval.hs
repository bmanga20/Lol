{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Crypto.Alchemy.Interpreter.CTEval where

import Algebra.Additive as Additive (C)
import Algebra.Ring as Ring (C)

import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.CT
import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE as SHE

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
  mulPublicCT a = I . mulPublic a . unI
  keySwitchQuadCT hint = I . keySwitchQuadCirc hint . unI
  tunnelCT info = I . SHE.tunnelCT info . unI