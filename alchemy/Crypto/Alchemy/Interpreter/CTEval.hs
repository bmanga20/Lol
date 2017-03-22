{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}

module Crypto.Alchemy.Interpreter.CTEval where

import Algebra.Additive as Additive (C)
import Algebra.Ring as Ring (C)

import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.CT
import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE as SHE

-- | Metacircular evaluator.
newtype I a = I { unI :: a }
  deriving (Eq, Show, Additive.C, Ring.C)

-- | Metacircular lambda.
instance Lambda I where
  lam f   = I $ unI . f . I
  app f a = I $ unI f $ unI a

-- | Metacircular ciphertext symantics.
instance SymCT I where

  type RescaleCtxCT   I     t m m' zp zq' zq = (RescaleCyc (Cyc t) zq' zq, ToSDCtx t m' zp zq')
  type AddPubCtxCT    I     t m m' zp     zq = (AddPublicCtx t m m' zp zq)
  type MulPubCtxCT    I     t m m' zp     zq = (MulPublicCtx t m m' zp zq)
  type KeySwitchCtxCT I gad t m m' zp zq' zq = (KeySwitchCtx gad t m' zp zq zq')
  type TunnelCtxCT    I gad t e r s e' r' s' zp zq = (TunnelCtx t r s e' r' s' zp zq gad)

  rescaleCT = I . rescaleLinearCT . unI
  addPublicCT a = I . addPublic a . unI
  mulPublicCT a = I . mulPublic a . unI
  keySwitchQuadCT hint = I . keySwitchQuadCirc hint . unI
  tunnelCT info = I . SHE.tunnelCT info . unI

instance Lit I where
  type LitCtx I a = ()
  lit = I

