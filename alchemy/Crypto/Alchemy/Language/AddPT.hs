{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE TypeFamilies #-}

module Crypto.Alchemy.Language.AddPT where

import Crypto.Lol (Cyc, Factored)
import GHC.Exts (Constraint)

-- | Symantics for leveled plaintext operations of some depth @d@.

class AddPT expr where
  type AddPubCtxPT   expr (t :: Factored -> * -> *) (m :: Factored) zp :: Constraint
  type MulPubCtxPT   expr (t :: Factored -> * -> *) (m :: Factored) zp :: Constraint
  type AdditiveCtxPT expr (t :: Factored -> * -> *) (m :: Factored) zp :: Constraint

  addPublicPT :: (AddPubCtxPT expr t m zp, a ~ Cyc t m zp) => a -> expr a -> expr a
  mulPublicPT :: (MulPubCtxPT expr t m zp, a ~ Cyc t m zp) => a -> expr a -> expr a

  (+#) :: (AdditiveCtxPT expr t m zp, a ~ Cyc t m zp) => expr a -> expr a -> expr a

  negPT :: (AdditiveCtxPT expr t m zp, a ~ Cyc t m zp) => expr a -> expr a

(-#) :: (AddPT expr, AdditiveCtxPT expr t m zp, a ~ Cyc t m zp)
     => expr a -> expr a -> expr a
a -# b = a +# (negPT b)