{-# LANGUAGE BangPatterns, ConstraintKinds, DataKinds, FlexibleContexts,
             FlexibleInstances, GADTs, GeneralizedNewtypeDeriving,
             KindSignatures, MultiParamTypeClasses, NoImplicitPrelude,
             RankNTypes, RebindableSyntax, RoleAnnotations,
             ScopedTypeVariables, TypeOperators #-}

-- | A simple DSL for tensoring Repa arrays and other common functionality
-- on Repa arrays

module Crypto.Lol.Cyclotomic.Tensor.RepaTensor.RTCommon
( module R
, module Data.Array.Repa.Eval
, module Data.Array.Repa.Repr.Unboxed
, Arr(..), repl, replM, eval, evalM, fTensor, ppTensor
, Trans(Id), trans, dim, (.*), (@*), force
, mulMat, mulDiag
, scalarPow'
, sumS, sumAllS
) where

import Crypto.Lol.LatticePrelude as LP hiding ((!!))

import Control.DeepSeq              (NFData (..))
import Control.Monad.Identity
import Control.Monad.Random
import Data.Array.Repa              as R hiding (sumAllP, sumAllS, sumP,
                                          sumS, (*^), (+^), (-^), (/^))
import Data.Array.Repa.Eval         hiding (one, zero)
import Data.Array.Repa.Repr.Unboxed
import Data.Coerce
import Data.Singletons
import Data.Singletons.Prelude      hiding ((:.))
import Data.Type.Natural            hiding (Z)
import Data.Typeable
import qualified Data.Vector.Unboxed as U
import Test.QuickCheck

-- always unboxed (manifest); intermediate calculations can use
-- delayed arrays

-- | Indexed newtype for 1-dimensional Unbox repa arrays
newtype Arr (m :: Factored) r = Arr (Array U DIM1 r)
                              deriving (Eq, Show, Typeable, NFData)

-- the first argument, though phantom, affects representation
-- CJP: why must the second arg be nominal?
-- EAC: From https://ghc.haskell.org/trac/ghc/wiki/Roles#Thesolution:
--   "The exception to the above algorithm is for classes: all parameters for a class default to a nominal role."
-- Arr is a synonym for Array, which is an associated data type to the class Source. The parameter `r` above
-- corresponds to the parameter `e` in the definition of class Source, so it's role must be nominal.
type role Arr nominal nominal

-- | An 'Arr' filled with the argument.
repl :: forall m r . (Fact m, Unbox r) => r -> Arr m r
repl = let n = proxy totientFact (Proxy::Proxy m)
       in Arr . fromUnboxed (Z:.n) . U.replicate n

-- | Monadic version of 'repl'.
replM :: forall m r mon . (Fact m, Unbox r, Monad mon)
         => mon r -> mon (Arr m r)
replM = let n = proxy totientFact (Proxy::Proxy m)
        in liftM (Arr . fromUnboxed (Z:.n)) . U.replicateM n

instance (Unbox r) => NFData (Array U DIM1 r) where
  -- EAC: Repa doesn't define any NFData instances,
  -- I'm hoping deepSeqArray is a reasonable approx
  rnf x = deepSeqArray x ()

instance (Unbox r, Random r, Fact m) => Random (Arr m r) where
  random = runRand $ replM (liftRand random)

  randomR = error "randomR nonsensical for Arr"

instance (Arbitrary r, Unbox r, Fact m) => Arbitrary (Arr m r) where
    arbitrary = replM arbitrary
    shrink = shrinkNothing

-- | For a factored index, tensors up any function defined for (and
-- tagged by) any prime power
fTensor :: forall m r mon . (Fact m, Monad mon, Unbox r)
  => (forall pp . (PPow pp) => TaggedT pp mon (Trans r))
  -> TaggedT m mon (Trans r)

fTensor func = tagT $ go $ sUnF (sing :: SFactored m)
  where
    go :: Sing (pplist :: [PrimePower]) -> mon (Trans r)
    go spps = case spps of
          SNil -> return $ Id 1
          (SCons spp rest) -> do
            rest' <- go rest
            func' <- withWitnessT func spp
            return $ rest' @* func'

-- | For a prime power pp > 1, tensors up any function f defined for
-- (and tagged by) a prime to (I_(pp/p) \otimes f)
ppTensor :: forall pp r mon . (PPow pp, Monad mon)
            => (forall p . (NatC p) => TaggedT p mon (Trans r))
            -> TaggedT pp mon (Trans r)

ppTensor func = tagT $ case (sing :: SPrimePower pp) of
  -- intentionally no match for zero exponents, because that is
  -- ill-formed and indicates an internal error
  (SPP (STuple2 sp (SS se1))) -> do
    func' <- withWitnessT func sp
    let lts = withWitness valuePPow (SPP (STuple2 sp se1))
    return $ Id lts @* func'


-- deeply embedded DSL for transformations and their various
-- compositions

-- (dim(f), f) where f operates on innermost dimension of array
data Tensorable r = Tensorable
  Int (forall rep . Source rep r => Array rep DIM2 r -> Array D DIM2 r)

-- transform component: a Tensorable with particular I_l, I_r
type TransC r = (Tensorable r, Int, Int)

-- full transform: sequence of zero or more components
-- | a DSL for tensor transforms on Repa arrays
data Trans r = Id Int           -- ^| identity sentinel
             | TSnoc (Trans r) (TransC r) -- ^| (function) composition of transforms

dimC :: TransC r -> Int
dimC (Tensorable d _, l, r) = l*d*r

-- | Returns the (linear) dimension of a transform
dim :: Trans r -> Int
dim (Id n) = n
dim (TSnoc _ f) = dimC f        -- just use dimension of head

-- | smart constructor from a Tensorable
trans :: Int -> (forall rep . Source rep r => Array rep DIM2 r -> Array D DIM2 r) -> Trans r
trans d f = TSnoc (Id d) (Tensorable d f, 1, 1)

-- | compose transforms
(.*) :: Trans r -> Trans r -> Trans r
f .* g | dim f == dim g = f ..* g
       | otherwise = error $ "(.*): transform dimensions don't match "
                     LP.++ show (dim f) LP.++ ", " LP.++ show (dim g)
  where
    f' ..* (Id _) = f'          -- drop sentinel
    f' ..* (TSnoc rest g') = TSnoc (f' ..* rest) g'

-- | tensor/Kronecker product (otimes)
(@*) :: Trans r -> Trans r -> Trans r
-- merge identity transforms
(Id n) @* (Id m) = Id (n*m)
-- Id on left or right
i@(Id n) @* (TSnoc g' (g, l, r)) = TSnoc (i @* g') (g, n*l, r)
(TSnoc f' (f, l, r)) @* i@(Id n) = TSnoc (f' @* i) (f, l, r*n)
-- no Ids: compose
f @* g = (f @* Id (dim g)) .* (Id (dim f) @* g)

evalC :: (Unbox r) => TransC r -> Array U DIM1 r -> Array U DIM1 r
evalC (Tensorable d f, _, r) arr =
  arr `deepSeqArray` force $ unexpose r $ f $ expose d r arr

-- | Creates an evaluatable Haskell function from a tensored transform
eval :: (Unbox r) => Tagged m (Trans r) -> Arr m r -> Arr m r
eval x = coerce $ eval' $ untag x
  where eval' (Id _) = id
        eval' (TSnoc rest f) = eval' rest . evalC f

-- | Monadic version of 'eval'
evalM :: (Unbox r, Monad mon) => TaggedT m mon (Trans r) -> mon (Arr m r -> Arr m r)
evalM = liftM (eval . return) . untagT


-- | maps the innermost dimension to a 2-dim array with innermost dim d,
-- for performing a I_l \otimes f_d \otimes I_r transformation
expose !d !r !arr =
  let (sh :. sz) = extent arr
      f (s :. i :. j) = let imodr = i `mod` r
                            idx = (i-imodr)*d + j*r + imodr
                        in arr ! (s :. idx)
  in fromFunction (sh :. sz `div` d :. d) f

-- | inverse of expose
unexpose !r !arr =
  let (sh:.sz:.d) = extent arr
      f (s :. i) = let (idivr,imodr) = i `divMod` r
                       (idivrd,j) = idivr `divMod` d
                   in arr ! (s :. r*idivrd + imodr :. j)
  in fromFunction (sh :. sz*d) f

-- | general matrix multiplication along innermost dim of v
mulMat :: (Source r1 r, Source r2 r, Ring r, Unbox r, Elt r)
          => Array r1 DIM2 r -> Array r2 DIM2 r -> Array D DIM2 r
mulMat !m !v
  = let (Z :. mrows :. mcols) = extent m
        (sh :. vrows) = extent v
        f (sh' :. i) = sumAllS $ R.zipWith (*) (slice m (Z:.i:.All)) $ slice v (sh':.All)
    in if mcols == vrows then fromFunction (sh :. mrows) f
       else error "mulMatVec: mcols != vdim"

-- | multiplication by a diagonal matrix along innermost dim
mulDiag :: (Source r1 r, Source r2 r, Ring r, Unbox r, Elt r)
           => Array r1 DIM1 r -> Array r2 DIM2 r -> Array D DIM2 r
mulDiag !diag !arr = fromFunction (extent arr) f
  where f idx@(_ :. i) = arr! idx * diag! (Z:.i)

-- misc Tensor functions

-- | Embeds a scalar into a powerful-basis representation of a Repa array,
-- tagged by the cyclotomic index
scalarPow' :: forall m r . (Fact m, Additive r, Unbox r) => r -> Arr m r
scalarPow' = coerce . (go $ proxy totientFact (Proxy::Proxy m))
  where go n !r = let fct (Z:.0) = r
                      fct _ = LP.zero
                  in force $ fromFunction (Z:.n) fct

-- | Forces a delayed array to a manifest array.
force :: (Shape sh, Unbox r) => Array D sh r -> Array U sh r
-- CJP: computeS just until we figure out how to avoid nested parallel
-- computation!
--force = computeS
force = runIdentity . computeP

-- copied implementations of functions we need that normally require
-- Num

-- | Sum the inner-most dimension of an array sequentially
sumS :: (Source r a, Elt a, Unbox a, Additive a, Shape sh)
  => Array r (sh :. Int) a
  -> Array U sh a
sumS = foldS (+) LP.zero

-- | Sum all array indices to a scalar sequentially
sumAllS :: (Shape sh, Source r a, Elt a, Unbox a, Additive a)
  => Array r sh a
  -> a
sumAllS = foldAllS (+) LP.zero
