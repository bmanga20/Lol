{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

module Crypto.Alchemy.Interpreter.PT2IR where

import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.IR
import Crypto.Alchemy.Language.PT
import Crypto.Lol hiding (Pos(..), type (*))
import qualified Crypto.Lol as Lol (Pos(..))
import Crypto.Lol.Applications.SymmSHE
import Crypto.Lol.Types

import Data.Constraint
import Data.Kind
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
type M2M' m m'map = FromJust (Lookup m m'map)

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
           -> *
  where
    P2ITerm  :: (m' ~ M2M' m m'map,
                 ct ~ CT m zp (Cyc t m' zq),
                 zp ~ Z2E e,
                 zq ~ (zqs !! d),
                 m `Divides` m', Lift' zp, Reduce Z zq,
                 CElt t zq, Eq zp, Encode zp zq,
                 --additional constraints for AddPublicCtx t m m' zp zq
                 CElt t zp, CElt t (LiftOf zp))
             => D t e zqs d -> ctexpr ct -> PT2IR ctexpr m'map zqs d (Cyc t m zp)

    P2ILam :: (PT2IR ctexpr m'map zqs da a -> PT2IR ctexpr m'map zqs db b)
           -> PT2IR ctexpr m'map zqs '(da,db) (a -> b)

-- CJP: want a conversion that works for both Term and Lam.  How to
-- write the type signature for it?
{-
-- | Convert from 'SymPT' to 'SymCT' (using 'PT2CT').
pt2CT :: (m `Divides` m', ct ~ CT m zp (Cyc t m' zq), Ring ct)
      => PT2CT ctexpr d (Cyc t m zp)
      -> proxy m'
      -> Zqs t zp d zq
      -> ctexpr (CT m zp (Cyc t m' zq))
pt2CT (P2ITerm f) = f
-}

instance (SymIR ctexpr) => SymPT (PT2IR ctexpr m'map zqs) where

  (P2ITerm d a) +# (P2ITerm _ b) = P2ITerm d $ a + b
                                   \\ witness entailRingSymIR a

  neg (P2ITerm d a) = P2ITerm d $ -a \\ witness entailRingSymIR a

  (P2ITerm (zqDict -> (Dict, d)) a) *# (P2ITerm _ b) =
    P2ITerm d $ rescaleIR (a * b \\ witness entailRingSymIR a)

  addPublicPT a (P2ITerm d b) = P2ITerm d $ addPublicIR a b
  mulPublicPT a (P2ITerm d b) = P2ITerm d $ mulPublicIR a b

instance LambdaD (PT2IR ctexpr m'map zqs) where
  lamD = P2ILam
  appD (P2ILam f) = f
