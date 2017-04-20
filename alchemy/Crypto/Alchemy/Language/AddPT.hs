{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE TypeFamilies #-}

module Crypto.Alchemy.Language.AddPT where

import Crypto.Alchemy.Depth
import Crypto.Lol (Cyc)
import GHC.Exts (Constraint)

infixl 6  +# --, -#

-- | Symantics for leveled plaintext operations of some depth @d@.

class AddPT expr where
  type AddPubCtxPT   expr (d :: Depth) a :: Constraint
  type MulPubCtxPT   expr (d :: Depth) a :: Constraint
  type AdditiveCtxPT expr (d :: Depth) a :: Constraint

  addPublicPT :: (AddPubCtxPT expr d a, a ~ Cyc t m zp, Applicative i) => a -> expr i d a -> expr i d a

  mulPublicPT :: (MulPubCtxPT expr d a, a ~ Cyc t m zp, Applicative i) => a -> expr i d a -> expr i d a

  (+#) :: (AdditiveCtxPT expr d a, a ~ Cyc t m zp, Applicative i) => expr i d a -> expr i d a -> expr i d a

  negPT :: (AdditiveCtxPT expr d a, a ~ Cyc t m zp, Applicative i) => expr i d a -> expr i d a

(-#) :: (AddPT expr, AdditiveCtxPT expr d a, a ~ Cyc t m zp, Applicative i)
     => expr i d a -> expr i d a -> expr i d a
a -# b = a +# negPT b
