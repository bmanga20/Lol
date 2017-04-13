{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Crypto.Alchemy.Language.AddPT where

import Crypto.Alchemy.Depth
import Crypto.Alchemy.Language.Lam
import Crypto.Lol (Cyc)
import GHC.Exts (Constraint)

infixl 6  +# --, -#

-- | Symantics for leveled plaintext operations of some depth @d@.

class AddPT expr where
  type AddPubCtxPT   (i :: * -> *) expr (d :: Depth) a :: Constraint
  --type MulPubCtxPT   expr (d :: Depth) a :: Constraint
  type AdditiveCtxPT (i :: * -> *) expr (d :: Depth) a :: Constraint

  addPublicPT :: (AddPubCtxPT i expr d a, a ~ Cyc t m zp, Applicative j) => a -> (i :. j) (expr d a) -> (i :. j) (expr d a)

  --mulPublicPT :: (MulPubCtxPT expr d a, a ~ Cyc t m zp) => a -> expr d a -> expr d a

  (+#) :: (AdditiveCtxPT i expr d a, a ~ Cyc t m zp, Applicative j) => (i :. j) (expr d a) -> (i :. j) (expr d a) -> (i :. j) (expr d a)
{-
  negPT :: (AdditiveCtxPT expr d a, a ~ Cyc t m zp) => expr d a -> expr d a


(-#) :: (AddPT expr, AdditiveCtxPT expr d a, a ~ Cyc t m zp)
     => expr d a -> expr d a -> expr d a
a -# b = a +# (negPT b)
-}