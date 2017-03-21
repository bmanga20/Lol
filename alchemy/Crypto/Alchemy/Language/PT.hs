{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeInType       #-}
{-# LANGUAGE TypeOperators    #-}

module Crypto.Alchemy.Language.PT where

import Crypto.Lol hiding (Pos(..), type (*))
import Data.Type.Natural
import Data.Constraint
import Data.Kind

-- | Symantics for leveled plaintext operations of some depth @d@.

class SymPT (expr :: forall k . k -> * -> *) where

  type LitCtxPT      expr (d :: k) (t :: Factored -> * -> *) (m :: Factored) zp :: Constraint
  type AddPubCtxPT   expr (d :: k) (t :: Factored -> * -> *) (m :: Factored) zp :: Constraint
  type MulPubCtxPT   expr (d :: k) (t :: Factored -> * -> *) (m :: Factored) zp :: Constraint
  type AdditiveCtxPT expr (d :: k) (t :: Factored -> * -> *) (m :: Factored) zp :: Constraint
  type RingCtxPT     expr (d :: k) (t :: Factored -> * -> *) (m :: Factored) zp :: Constraint
  type TunnelCtxPT   expr (d :: k) (t :: Factored -> * -> *) (e :: Factored) (r :: Factored) (s :: Factored) zp :: Constraint

  litPT :: (rp ~ Cyc t m zp, LitCtxPT expr d t m zp) => rp -> expr d rp

  addPublicPT :: (rp ~ Cyc t m zp, AddPubCtxPT expr d t m zp) => rp -> expr d rp -> expr d rp
  mulPublicPT :: (rp ~ Cyc t m zp, MulPubCtxPT expr d t m zp) => rp -> expr d rp -> expr d rp

  (+#) :: (rp ~ Cyc t m zp, AdditiveCtxPT expr d t m zp) =>
          -- CJP: generalize input depths?
          expr d rp -> expr d rp -> expr d rp

  neg :: (rp ~ Cyc t m zp, AdditiveCtxPT expr d t m zp) => expr d rp -> expr d rp

  -- | Plaintext multiplication.  Inputs must be one depth less than
  -- output (so we can't use 'Ring').

  (*#) :: (rp ~ Cyc t m zp, RingCtxPT expr d t m zp) =>
          -- CJP: generalize input depths?
          expr ('S d) rp -> expr ('S d) rp -> expr d rp

  tunnelPT :: (TunnelCtxPT expr d t e r s zp)
           => Linear t zp e r s -> expr d (Cyc t r zp) -> expr d (Cyc t s zp)

(-#) :: forall (expr :: forall k . k -> * -> *) rp t m zp d . (SymPT expr, rp ~ Cyc t m zp, AdditiveCtxPT expr d t m zp)
     => expr d rp -> expr d rp -> expr d rp
a -# b = a +# (neg b)