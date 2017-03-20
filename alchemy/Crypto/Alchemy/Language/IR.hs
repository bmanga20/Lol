{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

module Crypto.Alchemy.Language.IR where

import Control.Monad.Random

import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE
import Crypto.Lol.Cyclotomic.Tensor
import Crypto.Lol.Types.ZPP

import Data.Constraint
import Data.Typeable

-- | Symantics for ciphertext operations.

class SymIR expr where

  -- EAC: What constraints should go on these functions, if any? There's no
  -- corresponding evaluator.

  -- | Entailment of ring structure.
  entailRingSymIR :: Tagged (expr ct)
                     (Ring ct :- Ring (expr ct))

  rescaleIR :: (RescaleCyc (Cyc t) zq' zq, ToSDCtx t m' zp zq') =>
               -- above constraints copied from rescaleLinearCT
               expr (CT m zp (Cyc t m' zq')) -> expr (CT m zp (Cyc t m' zq))

  addPublicIR :: (AddPublicCtx t m m' zp zq, ct ~ CT m zp (Cyc t m' zq))
              => Cyc t m zp -> expr ct -> expr ct

  mulPublicIR :: (MulPublicCtx t m m' zp zq, ct ~ CT m zp (Cyc t m' zq))
              => Cyc t m zp -> expr ct -> expr ct

  keySwitchQuadIR :: (ct ~ CT m zp (Cyc t m' zq)) => expr ct -> expr ct

  -- has constraints from SymmSHE.tunnelCT and SymmSHE.tunnelInfo, plus a
  -- a couple of other functions, for all in-scope variables
  tunnelIR :: (CElt t zp, CElt t zq, CElt t (DecompOf zq),
               Fact s, Fact s', ExtendLinIdx e r s e' r' s',
               e' `Divides` r', e' ~ (e * (r' / r)), e ~ FGCD r s,
               Ring zq, Random zq, NFElt zq, Reduce (DecompOf zq) zq,
               ToSDCtx t r' zp zq, AbsorbGCtx t r' zp zq,
               -- to call crtSet
               --e `Divides` s, ZPP zp, TElt t (ZpOf zp),
               -- to call linearDec
               --e `Divides` r,
               -- recursive GADT constraint
               Typeable s')
           => Linear t zp e r s
              -> expr (CT r zp (Cyc t r' zq))
              -> expr (CT s zp (Cyc t s' zq))
