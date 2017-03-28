{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

module Crypto.Alchemy.Language.CT where

import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE

import Data.Constraint

-- | Symantics for ciphertext operations.

class SymCT expr where

  type AdditiveCtxCT expr (t :: Factored -> * -> *) (m :: Factored) (m' :: Factored) zp zq :: Constraint
  type RingCtxCT expr (t :: Factored -> * -> *) (m :: Factored) (m' :: Factored) zp zq :: Constraint
  type RescaleCtxCT expr (t :: Factored -> * -> *) (m :: Factored) (m' :: Factored) zp zq' zq :: Constraint
  type AddPubCtxCT expr (t :: Factored -> * -> *) (m :: Factored) (m' :: Factored) zp zq :: Constraint
  type MulPubCtxCT expr (t :: Factored -> * -> *) (m :: Factored) (m' :: Factored) zp zq :: Constraint
  type KeySwitchCtxCT expr gad (t :: Factored -> * -> *) (m :: Factored) (m' :: Factored) zp zq' zq :: Constraint
  type TunnelCtxCT expr gad (t :: Factored -> * -> *) (e :: Factored) (r :: Factored) (s :: Factored) (e' :: Factored) (r' :: Factored) (s' :: Factored) zp zq :: Constraint

  (+^) :: (AdditiveCtxCT expr t m m' zp zq)
    => expr (CT m zp (Cyc t m' zq)) -> expr (CT m zp (Cyc t m' zq)) -> expr (CT m zp (Cyc t m' zq))

  negCT :: (AdditiveCtxCT expr t m m' zp zq) => expr (CT m zp (Cyc t m' zq)) -> expr (CT m zp (Cyc t m' zq))

  (*^) :: (RingCtxCT expr t m m' zp zq)
    => expr (CT m zp (Cyc t m' zq)) -> expr (CT m zp (Cyc t m' zq)) -> expr (CT m zp (Cyc t m' zq))


  rescaleCT :: (RescaleCtxCT expr t m m' zp zq' zq)
            => expr (CT m zp (Cyc t m' zq')) -> expr (CT m zp (Cyc t m' zq))

  addPublicCT :: (AddPubCtxCT expr t m m' zp zq, ct ~ CT m zp (Cyc t m' zq))
              => Cyc t m zp -> expr ct -> expr ct

  mulPublicCT :: (MulPubCtxCT expr t m m' zp zq, ct ~ CT m zp (Cyc t m' zq))
              => Cyc t m zp -> expr ct -> expr ct

  keySwitchQuadCT :: (KeySwitchCtxCT expr gad t m m' zp zq' zq, ct ~ CT m zp (Cyc t m' zq))
                  => KSQuadCircHint gad (Cyc t m' zq') -> expr ct -> expr ct

  tunnelCT :: (TunnelCtxCT expr gad t e r s e' r' s' zp zq)
           => TunnelInfo gad t e r s e' r' s' zp zq
              -> expr (CT r zp (Cyc t r' zq))
              -> expr (CT s zp (Cyc t s' zq))