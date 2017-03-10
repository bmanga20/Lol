{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

module Crypto.Alchemy.CTLang where

import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE

import Data.Constraint

-- | Symantics for ciphertext operations.

class SymCT expr where

  -- | Entailment of ring structure.
  entailRingSymCT :: Tagged (expr ct)
                     (Ring ct :- Ring (expr ct))

  rescaleCT :: (RescaleCyc (Cyc t) zq' zq, ToSDCtx t m' zp zq') =>
               -- above constraints copied from rescaleLinearCT
               expr (CT m zp (Cyc t m' zq')) -> expr (CT m zp (Cyc t m' zq))

  addPublicCT :: (AddPublicCtx t m m' zp zq)
              => Cyc t m zp -> expr (CT m zp (Cyc t m' zq)) -> expr (CT m zp (Cyc t m' zq))

  mulPublicCT :: (MulPublicCtx t m m' zp zq)
              => Cyc t m zp -> expr (CT m zp (Cyc t m' zq)) -> expr (CT m zp (Cyc t m' zq))
