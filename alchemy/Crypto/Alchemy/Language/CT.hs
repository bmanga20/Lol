{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE TypeFamilies #-}

module Crypto.Alchemy.Language.CT where

import Crypto.Lol (Cyc, Factored)
import Crypto.Lol.Applications.SymmSHE
import GHC.Exts

infixl 7 *^
infixl 6  +^

-- | Symantics for ciphertext operations.

class SymCT expr where

  type AdditiveCtxCT  expr ct     :: Constraint
  type RingCtxCT      expr ct     :: Constraint
  type ModSwitchCtxCT expr ct zp' :: Constraint
  type RescaleCtxCT   expr ct zq' :: Constraint
  type AddPubCtxCT    expr ct     :: Constraint
  type MulPubCtxCT    expr ct     :: Constraint
  type KeySwitchCtxCT expr ct zq' gad :: Constraint
  type TunnelCtxCT    expr (t :: Factored -> * -> *) (e :: Factored) (r :: Factored) (s :: Factored) (e' :: Factored) (r' :: Factored) (s' :: Factored) zp zq gad :: Constraint

  (+^) :: (AdditiveCtxCT expr ct, ct ~ CT m zp (Cyc t m' zq))
       => expr ct -> expr ct -> expr ct

  negCT :: (AdditiveCtxCT expr ct, ct ~ CT m zp (Cyc t m' zq))
        => expr ct -> expr ct

  (*^) :: (RingCtxCT expr ct, ct ~ CT m zp (Cyc t m' zq))
       => expr ct -> expr ct -> expr ct

  modSwitchPT :: (ModSwitchCtxCT expr ct zp', ct ~ CT m zp (Cyc t m' zq))
              => expr ct -> expr (CT m zp' (Cyc t m' zq))

  rescaleCT :: (RescaleCtxCT expr ct zq', ct ~ CT m zp (Cyc t m' zq))
            => expr (CT m zp (Cyc t m' zq')) -> expr ct

  addPublicCT :: (AddPubCtxCT expr ct, ct ~ CT m zp (Cyc t m' zq))
              => Cyc t m zp -> expr ct -> expr ct

  mulPublicCT :: (MulPubCtxCT expr ct, ct ~ CT m zp (Cyc t m' zq))
              => Cyc t m zp -> expr ct -> expr ct

  keySwitchQuadCT :: (KeySwitchCtxCT expr ct zq' gad, ct ~ CT m zp (Cyc t m' zq))
                  => KSQuadCircHint gad (Cyc t m' zq') -> expr ct -> expr ct

  tunnelCT :: (TunnelCtxCT expr t e r s e' r' s' zp zq gad)
           => TunnelInfo gad t e r s e' r' s' zp zq
              -> expr (CT r zp (Cyc t r' zq))
              -> expr (CT s zp (Cyc t s' zq))
