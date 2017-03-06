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

{-
-- | Encodes a sequence of @Z_q@ types, with needed constraints, for
-- depth-@d@ computations. (The exposed type @zq@ is the one used at
-- depth @d@.)
data Zqs t zp d zq where
  ZqZ :: (Encode zq zp) => Zqs t zp 'Z zq

  ZqS :: (RescaleCyc (Cyc t) zq' zq,
          Encode zp zq', CElt t zq') -- ToSDCtx minus Fact m'
      => Zqs t zp d zq' -> Zqs t zp ('S d) zq


-- CJP: make sure all the constraints in the GADT, functions, and
-- instances below make logical sense.  Some are weird and I don't
-- yet see whether there are better alternatives.
-}

{-
-- one dict for changing d/zq
data ZqDict t zp zqs d where
  ZqZ :: (Encode zp (zqs !! 'Z)) => G t m'map m zp zqs 'Z
  ZqS :: (...) => G t m'map m zp zqs d -> G t m m'map m zp zqs ('S d)

-- needs a mul2 type family
data ZpDict zp where
  ZpZ :: ZpDict zp
  ZpS :: ZpDict zp -> ZpDict (Mul2 zp)
-}


-- punt for now
--data IdxDict m'map m where

-- injective type families are worthless: see
-- http://stackoverflow.com/questions/42602796/injective-type-families-with-gadts
-- https://ghc.haskell.org/trac/ghc/ticket/10833
--type family Mul2 (x :: k) :: k
--type instance Mul2 (ZqBasic q i) = ZqBasic (Mul2 q) i
--type instance Mul2 ('PP '(Prime2, e)) = 'PP '(Prime2, 'Lol.S e)

-- used to simulate injective type families
type family Div2 (x :: k) :: k

type family Two (x :: k)

type ZpDict zp = (Ring zp)

-- zq' is current modulus, zq is next modulus
type ZqDict t zp zq' zq zqs =
   -- constraints to get constraints on P2CTerm for zq
  (Reduce (LiftOf zp) zq, CElt t zq, Encode zp zq,
   -- constraints for rescaleCT
   RescaleCyc (Cyc t) zq' zq)

data D t zp zqs d where
  DZZ :: D t (Two (Head zqs)) zqs 'Z
  DZS :: (zq' ~ (zqs !! ('S d)), zq ~ (zqs !! d), ZqDict t zp zq' zq zqs, zp ~ Two (Head zqs))
      => D t zp zqs d -> D t zp zqs ('S d)
  DSZ :: (ZpDict zp)
      => D t (Div2 zp) zqs 'Z -> D t zp zqs 'Z
  DSS :: (zq' ~ (zqs !! ('S d)), zq ~ (zqs !! d), ZpDict zp, ZqDict t zp zq' zq zqs)
      => D t (Div2 zp) zqs ('S d) -> D t zp zqs d -> D t zp zqs ('S d)
{-
getZpDict :: D t zp zqs d -> (Dict (ZpDict zp), D t (Div2 zp) zqs d)
getZpDict (DSZ d) = (Dict, d)
getZpDict (DSS d _) = (Dict, d)
-}
getZqDict :: (zq' ~ (zqs !! ('S d)), zq ~ (zqs !! d))
  => D t zp zqs ('S d) -> (Dict (ZqDict t zp zq' zq zqs), D t zp zqs d)
getZqDict (DZS d) = (Dict, d)
getZqDict (DSS _ d) = (Dict, d)


-- use a type-lvel map from PT index to CT index

-- singletons exports (:!!), which takes a TypeLit index; we need a TypeNatural index
type family (xs :: [k1]) !! (d :: Nat) :: k1 where
  (x ': xs) !! 'Z = x
  (x ': xs) !! 'S s = xs !! s

type M2M' m (m'map :: [(Factored,Factored)]) = FromJust (Lookup m m'map)

-- If you get compile errors about kinds, make sure that ALL arguments have
-- kind sigs! https://ghc.haskell.org/trac/ghc/ticket/13365
-- | Plaintext to ciphertext compiler.
data PT2CT
  (ctexpr :: * -> *)    -- ^ symantics of target ciphertext expression
  (m'map :: [(Factored,Factored)])
  (zqs :: [*])
  (d :: k)            -- ^ depth of computation
  (a :: *)              -- ^ type of the plaintext expression
  :: *
  where
    P2CTerm  :: (m' ~ M2M' m m'map,
                 ct ~ CT m zp (Cyc t m' zq),
                 zq ~ (zqs !! d),
                 m `Divides` m', Lift' zp, Reduce (LiftOf zp) zq, CElt t zq, Eq zp, Encode zp zq, -- Ring ct
                 CElt t zp, CElt t (LiftOf zp) --additional constraints for AddPublicCtx t m m' zp zq
                 )
             => D t zp zqs d -> ctexpr ct -> PT2CT ctexpr m'map zqs d (Cyc t m zp)

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

  (P2CTerm d a) +# (P2CTerm _ b) =
    P2CTerm d $ a + b \\ witness entailRingSymCT a
  (P2CTerm d a) +# (P2CLit b) = P2CTerm d $ addPublicCT b a
  (P2CLit a) +# (P2CTerm d b) = P2CTerm d $ addPublicCT a b
  (P2CLit a) +# (P2CLit b) = P2CLit $ a+b

  (P2CTerm d a) -# (P2CTerm _ b) =
    P2CTerm d $ a - b \\ witness entailRingSymCT a
  (P2CTerm d a) -# (P2CLit b) = P2CTerm d $ addPublicCT (-b) a
  (P2CLit a) -# (P2CTerm d b) =
    P2CTerm d $ addPublicCT a (-b) \\ witness entailRingSymCT b
  (P2CLit a) -# (P2CLit b) = P2CLit $ a-b

  -- still needs keyswitch
  (P2CTerm (getZqDict -> (Dict, d)) a) *# (P2CTerm _ b) =
    P2CTerm d $ rescaleCT $ (a * b \\ witness entailRingSymCT a)
{-
instance LambdaD (PT2CT ctexpr) where
  lamD = P2CLam
  appD (P2CLam f) = f
-}