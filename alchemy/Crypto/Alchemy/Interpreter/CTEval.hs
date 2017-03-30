{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE RebindableSyntax     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Crypto.Alchemy.Interpreter.CTEval where

import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.CT
import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE as SHE

-- | Metacircular evaluator.
newtype I a = I { unI :: a }
  deriving (Eq, Show, Functor)

-- | Metacircular ciphertext symantics.
instance SymCT I where

  type AdditiveCtxCT  I a = (Additive a)
  type RingCtxCT      I a = (Ring a)
  type ModSwitchCtxCT I (CT m zp (Cyc t m' zq)) zp'     = (ModSwitchPTCtx t m' zp zp' zq)
  type RescaleCtxCT   I t m m' zp zq zq'                = (RescaleCyc (Cyc t) zq' zq, ToSDCtx t m' zp zq')
  type AddPubCtxCT    I (CT m zp (Cyc t m' zq))         = (AddPublicCtx t m m' zp zq)
  type MulPubCtxCT    I (CT m zp (Cyc t m' zq))         = (MulPublicCtx t m m' zp zq)
  type KeySwitchCtxCT I (CT m zp (Cyc t m' zq)) zq' gad = (KeySwitchCtx gad t m' zp zq zq')
  type TunnelCtxCT    I t e r s e' r' s' zp zq gad      = (TunnelCtx t r s e' r' s' zp zq gad)

  (I a) +^ (I b) = I $ a + b
  (I a) *^ (I b) = I $ a * b
  negCT           = fmap negate
  modSwitchPT     = fmap SHE.modSwitchPT
  rescaleCT       = fmap rescaleLinearCT
  addPublicCT     = fmap . addPublic
  mulPublicCT     = fmap . mulPublic
  keySwitchQuadCT = fmap . keySwitchQuadCirc
  tunnelCT        = fmap . SHE.tunnelCT

-- | Metacircular lambda.
instance Lambda I where
  lam f = I $ unI . f . I
  app f = fmap (unI f)

instance Lit I where
  type LitCtx I a = ()
  lit = I
