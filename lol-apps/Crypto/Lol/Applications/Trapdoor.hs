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

{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

module Crypto.Lol.Applications.TrapdoorGeneration where

import Control.Monad.Random

import Crypto.Lol

import MathObj.Matrix as M

-- TYPES --

data    PublicKey gad ff rq = PK    { aBar    :: PublicParam rq
                                    , a'      :: Matrix rq
                                    , h       :: Tag ff }
newtype PublicParam rq      = Param { unParam :: Matrix rq }
newtype Tag ff              = Tag   { unTag   :: ff }
newtype Trapdoor gad rq     = Trap  { unTrap  :: Matrix rq }
data    LWEOutput gad rq    = Out   { bBar    :: Matrix rq
                                    , b'      :: Matrix rq }
newtype LWESecret rq        = Sec   { unSec   :: rq }
data    LWEError rq         = Err   { eBar    :: Matrix rq
                                    , e'      :: Matrix rq }

-- METHODS --

genTrap :: forall ff gad rq r rnd .
  (r ~ LiftOf rq, Reduce r rq,
   Ring rq, Module ff rq, Gadget gad rq, RoundedGaussianCyc r,
   MonadRandom rnd)
  => PublicParam rq
  -> Tag ff
  -> rnd (Trapdoor gad rq, PublicKey gad ff rq)
genTrap aBar t = do
  let mBar = numColumns aBar
      tGad = (unTag t *>) <$> untag $ gadget @gad
  r :: Matrix r <- gaussianMtx mBar $ length tGad
  return (Trap r, PK aBar (tGad - aBar * reduce <$> r) t)

lweSecret :: forall ff gad rq .
  (Field ff, Ring rq, Correct gad rq, Module ff rq)
  => Trapdoor gad rq -> Tag ff -> LWEOutput gad rq -> LWESecret rq
lweSecret r (Tag h) (Out bBar b') =
  let s' = fst $ correct $ tag (bBar * r + b') @gad
  in recip h *> s'

lweError :: PublicKey gad ff rq -> LWEOutput gad rq -> LWESecret rq -> LWEError rq
lweError (PK aBar a' _) (Out bBar b') s = Err (bBar - s * aBar) (b' - s * a')

lweInv :: PublicKey gad ff rq -> Trapdoor gad rq -> Tag ff -> LWEOutput gad rq
  -> (LWESecret rq, LWEError rq)
lweInv a r h b = let s = lweSecret r h b in (s, lweError a b s)

lwe :: forall gad ff rq . (_)
  => Proxy gad
  -> PublicKey gad ff rq -> Tag ff -> LWESecret rq -> LWEError rq
  -> LWEOutput gad rq
lwe pg (PK aBar a' _) h' s (Err eBar e') =
  let tagShift = (unTag h' *>) <$> untag $ gadget @gad
  in LWEOut (eBar + s*aBar) (e' + s*a' + tagShift)

lweRand :: forall gad ff rq rnd . (MonadRandom rnd, Random rq)
  => Proxy gad
  -> PublicKey gad ff rq -> Tag ff -> LWESecret rq
  -> rnd (LWEOutput gad rq)
lweRand a h' s = do
  e <- rndError a
  return lwe a h' s e

rndSecret :: (MonadRandom rnd, Random rq, RoundedGaussianCyc rq)
  => rnd (LWESecret rq)
rndSecret = roundedGaussian var

rndError :: (MonadRandom rnd, Random rq, RoundedGaussianCyc rq)
  => PublicKey gad ff rq -> rnd (LWEError rq)
rndError pk = let dim1 = numColumns $ aBar pk
                  dim2 = numColumns $ a'   pk
              in Err (gaussianMtx 1 dim1) (gaussianMtx 1 dim2)

-- SUBROUTINES --

gaussianMtx :: (MonadRandom rnd, RoundedGaussianCyc a)
  => Int -> Int -> rnd (Matrix a)
gaussianMtx r c = M.fromList r c <$> replicateM (r*c) $ roundedGaussian var

-- BM: fixed value for variance OR pass as argument into functions?
var :: Double
var = 1.0
