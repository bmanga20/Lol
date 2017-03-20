{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

module Crypto.Alchemy.Language.CT where

import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE

import Data.Constraint

-- | Symantics for ciphertext operations.

class SymCT expr where

  -- EAC: Constraints on these functions are precisely those neede for the
  -- SymCT metacircular evaluator in CTEval.hs

  -- | Entailment of ring structure.
  entailRingSymCT :: Tagged (expr ct)
                     (Ring ct :- Ring (expr ct))

  rescaleCT :: (RescaleCyc (Cyc t) zq' zq, ToSDCtx t m' zp zq') =>
               -- above constraints copied from rescaleLinearCT
               expr (CT m zp (Cyc t m' zq')) -> expr (CT m zp (Cyc t m' zq))

  addPublicCT :: (AddPublicCtx t m m' zp zq, ct ~ CT m zp (Cyc t m' zq))
              => Cyc t m zp -> expr ct -> expr ct

  mulPublicCT :: (MulPublicCtx t m m' zp zq, ct ~ CT m zp (Cyc t m' zq))
              => Cyc t m zp -> expr ct -> expr ct

  keySwitchQuadCT :: (KeySwitchCtx gad t m' zp zq zq', ct ~ CT m zp (Cyc t m' zq))
                  => KSQuadCircHint gad (Cyc t m' zq') -> expr ct -> expr ct

  tunnelCT :: (TunnelCtx t r s e' r' s' zp zq gad, e ~ FGCD r s)
           => TunnelInfo gad t e r s e' r' s' zp zq
              -> expr (CT r zp (Cyc t r' zq))
              -> expr (CT s zp (Cyc t s' zq))