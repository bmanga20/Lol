{-|
Module      : Crypto.Lol.Applications.Trapdoor
Description : Etagicient lattice trapdoor operations from <http://web.eecs.umich.edu/~cpeikert/pubs/etagtrap.pdf [MP12]>.
Copyright   : (c) Bogdan Manga, 2018
                  Chris Peikert, 2018
License     : GPL-3
Maintainer  : cpeikert@alum.mit.edu
Stability   : experimental
Portability : POSIX

Etagicient lattice trapdoor operations from <http://web.eecs.umich.edu/~cpeikert/pubs/etagtrap.pdf [MP12]>.
-}

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Lol.Applications.Trapdoor where

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

-- METHODS --

genTrap :: forall gad tag cm zq z rnd .
  (Reduce (cm (LiftOf zq)) (cm zq),
   Ring (cm zq), Module tag (cm zq), Gadget gad (cm zq),
   RoundedGaussianCyc cm (LiftOf zq), MonadRandom rnd)
  => PublicParam (cm zq)
  -> tag
  -> rnd (Trapdoor gad (cm zq), PublicKey gad tag (cm zq))
genTrap pp@(Param aBar) t = do
  let mBar = numColumns aBar
      tGad = (t *>) <$> (gadget @gad)
      tGadMtx = M.fromList 1 (length tGad) tGad
  r :: Matrix (cm (LiftOf zq)) <- gaussianMtx mBar $ length tGad
  let r' = reduce <$> r
  return (Trap r', PK pp (tGadMtx - aBar * r') t)

lweSecret :: forall gad tag rq .
  (Field tag, Ring rq, Correct gad rq, Module tag rq)
  => Trapdoor gad rq -> tag -> LWEOutput gad rq
  -> LWESecret rq
lweSecret (Trap r) h (Out bBar b') =
  let s' = fst $ correct @gad $ topRow (bBar * r + b')
  in Sec $ recip h *> s'

lweError :: (LiftCyc cm zq, Ring (cm zq))
  => PublicKey gad tag (cm zq) -> LWEOutput gad (cm zq) -> LWESecret (cm zq)
  -> LWEError (cm (LiftOf zq))
lweError (PK (Param aBar) a' _) (Out bBar b') (Sec s) =
  let bBarLift = liftDec <$> (bBar - scale s aBar)
      b'Lift   = liftDec <$> (b' - scale s a')
  in Err bBarLift b'Lift

lweInv :: (Field tag, Ring (cm zq), Correct gad (cm zq), Module tag (cm zq),
           LiftCyc cm zq)
  => PublicKey gad tag (cm zq)
  -> Trapdoor gad (cm zq)
  -> tag
  -> LWEOutput gad (cm zq)
  -> (LWESecret (cm zq), LWEError (cm (LiftOf zq)))
lweInv a r h b = let s = lweSecret r h b in (s, lweError a b s)

lwe :: forall gad tag rq r . (Gadget gad rq, Reduce r rq)
  => PublicKey gad tag rq -> tag -> LWESecret rq -> LWEError r
  -> LWEOutput gad rq
lwe (PK (Param aBar) a' _) h' (Sec s) (Err eBar e') =
  let tagShift = (h' *>) <$> gadget @gad
  in Out (reduce <$> eBar + scale s aBar) (reduce <$> e' + scale s $ a' + tagShift)

lweRand :: forall gad tag cm zq rnd .
  (Gadget gad (cm zq), Reduce (cm (LiftOf zq)) (cm zq),
   MonadRandom rnd, Random (cm zq), RoundedGaussianCyc cm (LiftOf zq))
  => PublicKey gad tag (cm zq) -> tag -> LWESecret (cm zq)
  -> rnd (LWEOutput gad (cm zq))
lweRand a h' s = do
  e <- rndError a
  return $ lwe a h' s e

rndSecret :: (MonadRandom rnd, Random (cm zq), RoundedGaussianCyc cm zq)
  => rnd (LWESecret (cm zq))
rndSecret = do
  s <- roundedGaussian var
  return $ Sec s

rndError :: (MonadRandom rnd, RoundedGaussianCyc cm (LiftOf zq))
  => PublicKey gad tag (cm zq) -> rnd (LWEError (cm (LiftOf zq)))
rndError (PK (Param aBar) a' _) = do
  eBar <- gaussianMtx 1 $ numColumns aBar
  e'   <- gaussianMtx 1 $ numColumns a'
  return $ Err eBar e'

-- SUBROUTINES --

gaussianMtx :: (MonadRandom rnd, RoundedGaussianCyc cm a)
  => Int -> Int -> rnd (Matrix (cm a))
gaussianMtx r c = M.fromList r c <$> replicateM (r*c) (roundedGaussian var)

-- BM: fixed value for variance OR pass as argument into functions?
var :: Double
var = 1.0

topRow :: Matrix a -> [a]
topRow = head . rows
