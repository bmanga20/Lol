{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

module Crypto.Alchemy.Language.PT where

import Crypto.Lol hiding (Pos(..))
import Data.Type.Natural
import Data.Constraint

-- | Symantics for leveled plaintext operations of some depth @d@.

class SymPT expr where

  type AddPubCtxPT   expr (d :: Nat) (t :: Factored -> * -> *) (m :: Factored) zp :: Constraint
  type MulPubCtxPT   expr (d :: Nat) (t :: Factored -> * -> *) (m :: Factored) zp :: Constraint
  type AdditiveCtxPT expr (d :: Nat) (t :: Factored -> * -> *) (m :: Factored) zp :: Constraint
  type RingCtxPT     expr (d :: Nat) (t :: Factored -> * -> *) (m :: Factored) zp :: Constraint
  type TunnelCtxPT   expr (d :: Nat) (t :: Factored -> * -> *) (e :: Factored) (r :: Factored) (s :: Factored) zp :: Constraint

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

(-#) :: (SymPT expr, rp ~ Cyc t m zp, AdditiveCtxPT expr d t m zp)
     => expr d rp -> expr d rp -> expr d rp
a -# b = a +# (neg b)