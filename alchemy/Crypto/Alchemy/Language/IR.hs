{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

module Crypto.Alchemy.Language.IR where

import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE

import Data.Constraint

-- | Symantics for ciphertext operations.

class SymIR expr where

  -- | Entailment of ring structure.
  entailRingSymIR :: Tagged (expr ct)
                     (Ring ct :- Ring (expr ct))

  rescaleIR :: (RescaleCyc (Cyc t) zq' zq, ToSDCtx t m' zp zq') =>
               -- above constraints copied from rescaleLinearCT
               expr (CT m zp (Cyc t m' zq')) -> expr (CT m zp (Cyc t m' zq))

  addPublicIR :: (AddPublicCtx t m m' zp zq)
              => Cyc t m zp -> expr (CT m zp (Cyc t m' zq)) -> expr (CT m zp (Cyc t m' zq))

  mulPublicIR :: (MulPublicCtx t m m' zp zq)
              => Cyc t m zp -> expr (CT m zp (Cyc t m' zq)) -> expr (CT m zp (Cyc t m' zq))
