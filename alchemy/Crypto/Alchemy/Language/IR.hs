{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

module Crypto.Alchemy.Language.IR where

import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE

import Data.Constraint

-- | Symantics for ciphertext operations.

class SymIR mon expr where

  type RescaleCtxIR expr (t :: Factored -> * -> *) (m :: Factored) (m' :: Factored) zp zq' zq :: Constraint
  type AddPubCtxIR expr (t :: Factored -> * -> *) (m :: Factored) (m' :: Factored) zp zq :: Constraint
  type MulPubCtxIR expr (t :: Factored -> * -> *) (m :: Factored) (m' :: Factored) zp zq :: Constraint
  type KeySwitchCtxIR expr (t :: Factored -> * -> *) (m :: Factored) (m' :: Factored) zp zq :: Constraint
  type TunnelCtxIR expr (t :: Factored -> * -> *) (e :: Factored) (r :: Factored) (s :: Factored) (r' :: Factored) (s' :: Factored) zp zq :: Constraint

  rescaleIR :: (RescaleCtxIR expr t m m' zp zq' zq)
            => mon (expr (CT m zp (Cyc t m' zq')) -> expr (CT m zp (Cyc t m' zq)))

  addPublicIR :: (AddPubCtxIR expr t m m' zp zq, ct ~ CT m zp (Cyc t m' zq))
              => mon (Cyc t m zp -> expr ct -> expr ct)

  mulPublicIR :: (MulPubCtxIR expr t m m' zp zq, ct ~ CT m zp (Cyc t m' zq))
              => mon (Cyc t m zp -> expr ct -> expr ct)

  keySwitchQuadIR :: (KeySwitchCtxIR expr t m m' zp zq, ct ~ CT m zp (Cyc t m' zq))
                  => mon (expr ct -> expr ct)

  tunnelIR :: (TunnelCtxIR expr t e r s r' s' zp zq)
           => Linear t zp e r s -> mon (expr (CT r zp (Cyc t r' zq)) -> expr (CT s zp (Cyc t s' zq)))
