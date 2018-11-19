{-|
Module      : Crypto.Lol.Applications.Trapdoor
Description : Efficient lattice trapdoor operations from <http://web.eecs.umich.edu/~cpeikert/pubs/efftrap.pdf [MP12]>.
Copyright   : (c) Bogdan Manga, 2018
                  Chris Peikert, 2018
License     : GPL-3
Maintainer  : cpeikert@alum.mit.edu
Stability   : experimental
Portability : POSIX

Efficient lattice trapdoor operations from <http://web.eecs.umich.edu/~cpeikert/pubs/efftrap.pdf [MP12]>.
-}

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Lol.Applications.Trapdoor
( PublicKey, PublicParam(..), Trapdoor, LWEOutput, LWESecret(..), LWEError(..)
, TrapGenCtx, trapGen, trapTag, publicParam
, LWECtx, lweInv, lweRandomError, lweRandom, lweSecret
) where

import Control.Applicative hiding ((*>))
import Control.Monad.Random

import Crypto.Lol

import MathObj.Matrix as M

-- TYPES --

data    PublicKey gad tag rq = PK    { aBar    :: PublicParam rq
                                     , a'      :: Matrix rq
                                     , h       :: tag }
newtype PublicParam rq       = Param { unParam :: Matrix rq }
newtype Trapdoor gad rq      = Trap  { unTrap  :: Matrix rq }
data    LWEOutput gad rq     = Out   { bBar    :: Matrix rq
                                     , b'      :: Matrix rq }
newtype LWESecret rq         = Sec   { unSec   :: rq }
data    LWEError rq          = Err   { eBar    :: Matrix rq
                                     , e'      :: Matrix rq }

-- | Constraint synonym for generating a trapdoor.
type TrapGenCtx gad tag cm zq
  = (Reduce (cm (LiftOf zq)) (cm zq),
    Ring (cm zq), Module tag (cm zq), Gadget gad (cm zq),
    RoundedGaussianCyc cm (LiftOf zq))

-- | Constraint synonym for computing the LWE function.
type LWECtx gad tag rq r
  = (Gadget gad rq, Reduce r rq, Module tag rq)

-- METHODS --

-- | Generate a trapdoor by sampling over a rounded Gaussian distribution.
trapGen :: forall gad tag cm zq rnd .
  (TrapGenCtx gad tag cm zq, MonadRandom rnd)
  => PublicParam (cm zq)
  -> tag
  -> rnd (Trapdoor gad (cm zq), PublicKey gad tag (cm zq))
trapGen pp@(Param aBar) t = do
  let mBar = numColumns aBar
      tGad = rowMtx $ (t *>) <$> (gadget @gad)
  rBar :: Matrix (cm (LiftOf zq)) <- gaussianMtx mBar $ numColumns tGad
  r :: Matrix (cm (LiftOf zq)) <- gaussianMtx mBar $ numColumns tGad
  let (rBar', r') = (reduce <$> rBar, reduce <$> r)
  return (Trap rBar', PK pp (tGad - aBar * rBar' - r') t)

-- | Compute the LWE function.
lwe :: forall gad tag rq r . (LWECtx gad tag rq r)
  => PublicKey gad tag rq -> tag -> LWESecret rq -> LWEError r
  -> LWEOutput gad rq
lwe (PK (Param aBar) a' _) h' (Sec s) (Err eBar e') =
  let tagShift = rowMtx $ (h' *>) <$> gadget @gad
      bBar = (reduce <$> eBar) + scale s aBar
      b'   = (reduce <$> e') + scale s (a' + tagShift)
  in Out bBar b'

-- | Compute the LWE function with randomly-generated error.
lweRandomError :: forall gad tag cm zq rnd .
  (Gadget gad (cm zq), Reduce (cm (LiftOf zq)) (cm zq), Module tag (cm zq),
   MonadRandom rnd, RoundedGaussianCyc cm (LiftOf zq))
  => PublicKey gad tag (cm zq) -> tag -> LWESecret (cm zq)
  -> rnd (LWEOutput gad (cm zq))
lweRandomError a h' s = do
  e <- lweError a
  return $ lwe a h' s e

-- | Compute the LWE function with randomly-generated secret and error.
lweRandom :: forall gad tag cm zq rnd .
  (Gadget gad (cm zq), Reduce (cm (LiftOf zq)) (cm zq), Module tag (cm zq),
   MonadRandom rnd, RoundedGaussianCyc cm zq, RoundedGaussianCyc cm (LiftOf zq))
  => PublicKey gad tag (cm zq) -> tag
  -> rnd (LWESecret (cm zq), LWEOutput gad (cm zq))
lweRandom a h' = do
  s <- lweSecret
  lweOut <- lweRandomError a h' s
  return $ (s, lweOut)

-- | Generate an LWE secret by sampling from a rounded Gaussian distribution.
lweSecret :: (MonadRandom rnd, RoundedGaussianCyc cm zq)
  => rnd (LWESecret (cm zq))
lweSecret = do
  s <- roundedGaussian var
  return $ Sec s

-- | Generate an LWE error by sampling over a rounded Gaussian distribution.
lweError :: (MonadRandom rnd, RoundedGaussianCyc cm (LiftOf zq))
  => PublicKey gad tag (cm zq) -> rnd (LWEError (cm (LiftOf zq)))
lweError (PK (Param aBar) a' _) = do
  eBar <- gaussianMtx 1 $ numColumns aBar
  e'   <- gaussianMtx 1 $ numColumns a'
  return $ Err eBar e'

-- | Recover LWE secret from LWE output by using trapdoor.
lweInvSecret :: forall gad tag rq .
  (Field tag, ZeroTestable tag, Ring rq, Correct gad rq, Module tag rq)
  => Trapdoor gad rq -> tag -> LWEOutput gad rq
  -> Maybe (LWESecret rq)
lweInvSecret (Trap rBar) h (Out bBar b') =
  let s' = fst $ correct @gad $ head $ rows (bBar * rBar + b')
  in if isZero h then Nothing else Just $ Sec $ recip h *> s'

-- | Recover LWE error from LWE output by using LWE secret.
lweInvError :: (LiftCyc cm zq, Ring (cm zq))
  => PublicKey gad tag (cm zq) -> LWEOutput gad (cm zq) -> LWESecret (cm zq)
  -> LWEError (cm (LiftOf zq))
lweInvError (PK (Param aBar) a' _) (Out bBar b') (Sec s) =
  let eBar = liftDec <$> (bBar - scale s aBar)
      e'   = liftDec <$> (b' - scale s a')
  in Err eBar e'

-- | Recover LWE secret and LWE error by using trapdoor.
lweInv :: (Field tag, ZeroTestable tag, Ring (cm zq),
           Correct gad (cm zq), Module tag (cm zq),
           LiftCyc cm zq)
  => PublicKey gad tag (cm zq)
  -> Trapdoor gad (cm zq)
  -> tag
  -> LWEOutput gad (cm zq)
  -> Maybe (LWESecret (cm zq), LWEError (cm (LiftOf zq)))
lweInv a rBar h b = do
  s <- lweInvSecret rBar h b
  return (s, lweInvError a b s)

-- | Generate a uniformly-random tag.
trapTag :: (MonadRandom rnd, Random tag) => rnd tag
trapTag = getRandom

-- | Generate a uniformly-random public parameter.
publicParam :: (MonadRandom rnd, Random rq) => Int -> rnd (PublicParam rq)
publicParam mBar = do
  pp <- M.fromList 1 mBar <$> replicateM mBar getRandom
  return $ Param pp

-- SUBROUTINES --

-- | Generate random matrix with specified dimensions by sampling over a
-- rounded Gaussian distribution.
gaussianMtx :: (MonadRandom rnd, RoundedGaussianCyc cm a)
  => Int -> Int -> rnd (Matrix (cm a))
gaussianMtx r c = M.fromList r c <$> replicateM (r*c) (roundedGaussian var)

-- | Hard-coded value for variance of rounded Gaussian distribution.
var :: Double
var = 1.0

-- | Create one-row matrix from input list.
rowMtx :: [a] -> Matrix a
rowMtx a = M.fromList 1 (length a) a
