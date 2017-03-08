{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

module Crypto.Alchemy.Interpreter.PT2CT where

import Crypto.Alchemy.Lam
import Crypto.Alchemy.CTLang
import Crypto.Alchemy.PTLang
import Crypto.Lol hiding (Pos(..))
import qualified Crypto.Lol as Lol (Pos(..))
import Crypto.Lol.Applications.SymmSHE
import Crypto.Lol.Types

import Data.Constraint
import Data.Singletons.Prelude.List
import Data.Singletons.Prelude.Maybe
import Data.Type.Natural (Nat(..))

-- injective type families are worthless: see
-- http://stackoverflow.com/questions/42602796/injective-type-families-with-gadts
-- https://ghc.haskell.org/trac/ghc/ticket/10833
--type family Mul2 (x :: k) :: k
--type instance Mul2 (ZqBasic q i) = ZqBasic (Mul2 q) i
--type instance Mul2 ('PP '(Prime2, e)) = 'PP '(Prime2, 'Lol.S e)

-- used to simulate injective type families
type family Div2 (x :: k) :: k

type family Two (x :: k)

type ZpDict e = (Ring (Z2E e))


-- concrete Z integer representation
type Z = Int64

-- a concrete Z_2^e data type
type Z2E e = ZqBasic ('PP '(Prime2, e)) Z

-- zq' is current modulus, zq is next modulus
type ZqDict t e zq' zq zqs =
   -- constraints to get constraints on P2CTerm for zq
  (Reduce Z zq, CElt t zq, Encode (Z2E e) zq,
   -- constraints for rescaleCT
   RescaleCyc (Cyc t) zq' zq)

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

-- singletons exports (:!!), which takes a TypeLit index; we need a TypeNatural index
type family (xs :: [k1]) !! (d :: Nat) :: k1 where
  (x ': xs) !! 'Z = x
  (x ': xs) !! 'S s = xs !! s

-- a type-lvel map from PT index to CT index
type M2M' m (m'map :: [(Factored,Factored)]) = FromJust (Lookup m m'map)

-- If you get compile errors about kinds, make sure that ALL arguments have
-- kind sigs! https://ghc.haskell.org/trac/ghc/ticket/13365
-- | Plaintext to ciphertext compiler.
data PT2CT
  (ctexpr :: * -> *)    -- ^ symantics of target ciphertext expression
  (m'map :: [(Factored,Factored)])
  (zqs :: [*])
  (d :: k)                      -- ^ depth of computation
  (a :: *)                      -- ^ type of the plaintext expression
  :: *
  where
    P2CTerm  :: (m' ~ M2M' m m'map,
                 ct ~ CT m zp (Cyc t m' zq),
                 zp ~ Z2E e,
                 zq ~ (zqs !! d),
                 m `Divides` m', Lift' zp, Reduce Z zq,
                 CElt t zq, Eq zp, Encode zp zq,
                 --additional constraints for AddPublicCtx t m m' zp zq
                 CElt t zp, CElt t (LiftOf zp))
             => D t e zqs d -> ctexpr ct -> PT2CT ctexpr m'map zqs d (Cyc t m zp)

    P2CLit :: (rp ~ Cyc t m zp) => rp -> PT2CT ctexpr m'map zqs d rp

    P2CLam :: (PT2CT ctexpr m'map zqs da a -> PT2CT ctexpr m'map zqs db b)
           -> PT2CT ctexpr m'map zqs '(da,db) (a -> b)

-- CJP: want a conversion that works for both Term and Lam.  How to
-- write the type signature for it?
{-
-- | Convert from 'SymPT' to 'SymCT' (using 'PT2CT').
pt2CT :: (m `Divides` m', ct ~ CT m zp (Cyc t m' zq), Ring ct)
      => PT2CT ctexpr d (Cyc t m zp)
      -> proxy m'
      -> Zqs t zp d zq
      -> ctexpr (CT m zp (Cyc t m' zq))
pt2CT (P2CTerm f) = f
-}

instance (SymCT ctexpr) => SymPT (PT2CT ctexpr m'map zqs) where

  (P2CTerm d a) +# (P2CTerm _ b) = P2CTerm d $ a + b
                                   \\ witness entailRingSymCT a
  (P2CTerm d a) +# (P2CLit    b) = P2CTerm d $ addPublicCT b a
  (P2CLit    a) +# (P2CTerm d b) = P2CTerm d $ addPublicCT a b
  (P2CLit    a) +# (P2CLit    b) = P2CLit    $ a+b

  neg (P2CTerm d a) = P2CTerm d $ -a \\ witness entailRingSymCT a
  neg (P2CLit a) = P2CLit $ -a

  -- still needs keyswitch
  (P2CTerm (zqDict -> (Dict, d)) a) *# (P2CTerm _ b) =
    P2CTerm d $ rescaleCT (a * b \\ witness entailRingSymCT a)

{-
instance LambdaD (PT2CT ctexpr) where
  lamD = P2CLam
  appD (P2CLam f) = f
-}
