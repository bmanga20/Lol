{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}

module Crypto.Alchemy.Interpreter.PT2IR where

import Control.Monad.Random

import Crypto.Alchemy.Common
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.IR
import Crypto.Alchemy.Language.PT
import Crypto.Lol hiding (Pos(..), type (*))
import qualified Crypto.Lol as Lol (Pos(..), type (*))
import Crypto.Lol.Applications.SymmSHE
import Crypto.Lol.Types


import Crypto.Lol.Types.ZPP
import Crypto.Lol.Cyclotomic.Tensor

import Data.Constraint
import Data.Dynamic
import Data.Kind
import Data.Type.Natural (Nat(..))

type ZpDict e = (Ring (Z2E e))

-- zq' is current modulus, zq is next modulus
type ZqDict t e zq' zq zqs =
   -- constraints to get constraints on P2CTerm for zq
  (Reduce Z zq, CElt t zq, Encode (Z2E e) zq,
   -- constraints for rescaleCT
   RescaleCyc (Cyc t) zq' zq, Reduce (DecompOf zq) zq, CElt t (DecompOf zq),
   NFElt zq, Random zq)

-- tensor, zp-exponent-of-two, zqs list, and depth of computation
data D t e zqs d where
  DZZ :: D t 'Lol.O zqs 'Z

  DZS :: (zq' ~ (zqs !! 'S d), zq ~ (zqs !! d),
          ZqDict t 'Lol.O zq' zq zqs)
      => D t 'Lol.O zqs d -> D t 'Lol.O zqs ('S d)

  DSZ :: (ZpDict ('Lol.S e))
      => D t e zqs 'Z -> D t ('Lol.S e) zqs 'Z

  DSS :: (zq' ~ (zqs !! 'S d), zq ~ (zqs !! d),
          ZpDict ('Lol.S e), ZqDict t ('Lol.S e) zq' zq zqs)
      => D t e zqs ('S d) -> D t ('Lol.S e) zqs d -> D t ('Lol.S e) zqs ('S d)

zpDict :: D t ('Lol.S e) zqs d
          -> (Dict (ZpDict ('Lol.S e)), D t e zqs d)
zpDict (DSZ d) = (Dict, d)
zpDict (DSS d _) = (Dict, d)

zqDict :: (zq' ~ (zqs !! ('S d)), zq ~ (zqs !! d))
  => D t e zqs ('S d) -> (Dict (ZqDict t e zq' zq zqs), D t e zqs d)
zqDict (DZS d) = (Dict, d)
zqDict (DSS _ d) = (Dict, d)

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
  P2ITerm  :: (m' ~ Lookup m m'map, ct ~ CT m zp (Cyc t m' zq),
               zp ~ Z2E k, zq ~ (zqs !! d), PosC k, -- p = 2^k
               m `Divides` m', Lift' zp, Reduce Z zq,
               CElt t zq, Eq zp, Encode zp zq,
               --additional constraints for AddPublicCtx t m m' zp zq
               CElt t zp, CElt t (LiftOf zp),
               --additional constraints for calling tunnelIR
               CElt t (DecompOf zq), Ring zq, Random zq, NFElt zq,
               Reduce (DecompOf zq) zq,
               ToSDCtx t m' zp zq, AbsorbGCtx t m' zp zq)
           => D t k zqs d -> MDiv m'map -> irexpr ct -> PT2IR irexpr m'map zqs d (Cyc t m zp)

  P2ILam :: (PT2IR irexpr m'map zqs da a -> PT2IR irexpr m'map zqs db b)
         -> PT2IR irexpr m'map zqs '(da,db) (a -> b)

instance (SymIR irexpr) => SymPT (PT2IR irexpr m'map zqs) where

  (P2ITerm d m a) +# (P2ITerm _ _ b) = P2ITerm d m $ a + b
                                   \\ witness entailRingSymIR a

  neg (P2ITerm d m a) = P2ITerm d m $ -a \\ witness entailRingSymIR a

  (P2ITerm (zqDict -> (Dict, d)) m a) *# (P2ITerm _ _ b) = P2ITerm d m $
    rescaleIR $ keySwitchQuadIR $ a * b \\ witness entailRingSymIR a

  addPublicPT a (P2ITerm d m b) = P2ITerm d m $ addPublicIR a b
  mulPublicPT a (P2ITerm d m b) = P2ITerm d m $ mulPublicIR a b

  tunnelPT :: forall e r s t zp d .
    (e ~ FGCD r s, e `Divides` r, e `Divides` s, CElt t zp, ZPP zp,
     TElt t (ZpOf zp), Typeable s)
    => Linear t zp e r s
       -> PT2IR irexpr m'map zqs d (Cyc t r zp)
       -> PT2IR irexpr m'map zqs d (Cyc t s zp)
  tunnelPT f (P2ITerm d m a) =
    -- EAC: TODO Need to modSwitch up before tunneling, and down after.
    case mdivLookup m (Proxy::Proxy s) of
      Dict -> P2ITerm d m $ tunnelIR f a

m' ~ (FLCM m (e*m'/m))
{-
-- EAC: copy-pasted from PTTunnel instance in Crypto.Lol.Applications.HomomPRF
    -- we should find a real home for this code...
    let crts = proxy crtSet (Proxy::Proxy e)
        r = proxy totientFact (Proxy::Proxy r)
        e = proxy totientFact (Proxy::Proxy e)
        dim = r `div` e
        -- only take as many crts as we need
        -- otherwise linearDec fails
        linf = linearDec (take dim crts) :: Linear t zp e r s
-}

instance LambdaD (PT2IR irexpr m'map zqs) where
  lamD = P2ILam
  appD (P2ILam f) = f

type MDiv map = MDiv' map (Length map)

data MDiv' m'map d where
  MNil :: MDiv' '[] 'Z
  MCons :: (m `Divides` m',
            e ~ FGCD m e', e' ~ (e Lol.* (m' / m)),
            m' ~ FLCM m e', e' `Divides` m',



            Typeable m, Typeable m',
            '(m,m') ~ (m'map !! d), m' ~ (Lookup m m'map))
        => Proxy m -> MDiv' m'map d -> MDiv' m'map ('S d)

mdivLookup :: forall m1 m'map d m' .
  (Typeable m1, Fact m1, m' ~ Lookup m1 m'map)
  => MDiv' m'map d -> Proxy m1
     -> Dict (m1 `Divides` m',
              Typeable m')
mdivLookup MNil _ = error "This can never happen"
mdivLookup (MCons (_::Proxy m2) mds) pm = case eqT @m1 @m2 of
  Nothing -> mdivLookup mds pm
  (Just Refl) -> Dict

{-
-- EAC: Alternate implementation of MDiv and mdivLookup.
-- This version has a nicer GADT (fewer constraints on MCons and no "index" parameter)
-- but it requries unsafeCoerce.
-- Note that *both* implementations have a hole.
data MDiv (map :: [(Factored,Factored)]) where
  MNil :: MDiv '[]
  MCons :: (m `Divides` m', Typeable m) => MDiv rest -> MDiv ( '(m,m') ': rest)

mdivLookup :: forall s map . (Typeable s) => MDiv map -> Proxy s -> Dict (s `Divides` (Lookup s map))
mdivLookup MNil _ = error "This can never happen"
mdivLookup a@(MCons rest) ps =
  -- https://ghc.haskell.org/trac/ghc/ticket/13365
  case a of
    (a :: MDiv ( '(m,m') ': rest)) ->
      case eqT @s @m of
        (Just Refl) -> Dict
        Nothing -> unsafeCoerceLookup @s @'(m,m') @rest $ mdivLookup rest ps

unsafeCoerceLookup :: forall s a rest .
  Dict (s `Divides` (Lookup s rest)) -> Dict (s `Divides` (Lookup s (a ': rest)))
unsafeCoerceLookup = unsafeCoerce
-}

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