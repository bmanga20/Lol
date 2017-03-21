{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE RebindableSyntax     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Crypto.Alchemy.Interpreter.PT2IR where

import Crypto.Alchemy.Common
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.IR
import Crypto.Alchemy.Language.PT
import Crypto.Lol hiding (Pos(..), type (*))
import Crypto.Lol.Applications.SymmSHE

import Data.Kind
import Data.Type.Natural (Nat(..))

-- If you get compile errors about kinds, make sure that ALL arguments have
-- kind sigs! https://ghc.haskell.org/trac/ghc/ticket/13365
-- | Plaintext to ciphertext compiler.

-- The `forall` is right before the polymorphic argument in order to keep the
-- type polymorphic after partial application. (Otherwise the LamD instance won't compile)
-- This is likely a bug.
data PT2IR :: (* -> *)
           -> [(Factored,Factored)]
           -> [*]
           -> forall k . k
           -> *
           -> * where
  P2ITerm  :: (m' ~ Lookup m m'map, ct ~ CT m zp (Cyc t m' zq), zq ~ (zqs !! d))
           => irexpr ct -> PT2IR irexpr m'map zqs d (Cyc t m zp)

  P2ILam :: (PT2IR irexpr m'map zqs da a -> PT2IR irexpr m'map zqs db b)
         -> PT2IR irexpr m'map zqs '(da,db) (a -> b)

instance (SymIR irexpr) => SymPT (PT2IR irexpr m'map zqs) where

  type AddPubCtxPT   (PT2IR irexpr m'map zqs) d t m     zp = (AddPubCtxIR irexpr t m (Lookup m m'map) zp (zqs !! d))
  type MulPubCtxPT   (PT2IR irexpr m'map zqs) d t m     zp = (MulPubCtxIR irexpr t m (Lookup m m'map) zp (zqs !! d))
  type AdditiveCtxPT (PT2IR irexpr m'map zqs) d t m     zp = (Additive (irexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d)))))
  type RingCtxPT     (PT2IR irexpr m'map zqs) d t m     zp =
    (Ring (irexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! ('S d))))),
     RescaleCtxIR irexpr t m (Lookup m m'map) zp (zqs !! ('S d)) (zqs !! d),
     KeySwitchCtxIR irexpr t m (Lookup m m'map) zp (zqs !! ('S d)))
  type TunnelCtxPT   (PT2IR irexpr m'map zqs) d t e r s zp = (TunnelCtxIR irexpr t e r s (Lookup r m'map) (Lookup s m'map) zp (zqs !! d))

  (P2ITerm a) +# (P2ITerm b) = P2ITerm $ a + b

  neg (P2ITerm a) = P2ITerm $ -a

  -- EAC: should key switch before the mul, only if necessary. Current signature of *# doesn't allow this...
  (P2ITerm a) *# (P2ITerm b) = P2ITerm $
    rescaleIR $ keySwitchQuadIR $ a * b

  addPublicPT a (P2ITerm b) = P2ITerm $ addPublicIR a b
  mulPublicPT a (P2ITerm b) = P2ITerm $ mulPublicIR a b

  -- EAC: TODO Need to modSwitch up before a *sequence* of tunnels, and down after. How do we detect this?
  tunnelPT f (P2ITerm a) = P2ITerm $ tunnelIR f a

instance LambdaD (PT2IR irexpr m'map zqs) where
  lamD = P2ILam
  appD (P2ILam f) = f

-- CJP: want a conversion that works for both Term and Lam.  How to
-- write the type signature for it?
{-
-- | Convert from 'SymPT' to 'SymCT' (using 'PT2CT').
pt2CT :: (m `Divides` m', ct ~ CT m zp (Cyc t m' zq), Ring ct)
      => PT2CT irexpr d (Cyc t m zp)
      -> proxy m'
      -> Zqs t zp d zq
      -> irexpr (CT m zp (Cyc t m' zq))
pt2CT (P2ITerm f) = f
-}