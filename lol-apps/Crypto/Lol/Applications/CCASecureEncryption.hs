{-|
Module      : Crypto.Lol.Applications.CCASecureEncryption
Description : Chosen Ciphertext-Secure Encryption from Section 6.3 of
              <http://web.eecs.umich.edu/~cpeikert/pubs/efftrap.pdf [MP12]>.
Copyright   : (c) Bogdan Manga, 2018
                  Chris Peikert, 2018
License     : GPL-3
Maintainer  : cpeikert@alum.mit.edu
Stability   : experimental
Portability : POSIX

Chosen Ciphertext-Secure Encryption from Section 6.3 of
<http://web.eecs.umich.edu/~cpeikert/pubs/efftrap.pdf [MP12]>.
-}

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Lol.Applications.CCASecureEncryption where

import Control.Monad.Random

import Crypto.Lol
import Crypto.Lol.Applications.Trapdoor as TD

import Data.Set

import MathObj.Matrix as M hiding (zero)

import qualified Prelude (sum)

type SecretKey gad rq = Trapdoor gad rq

data PublicKey' gad tag rq     = PK' { a  :: TD.PublicKey gad tag rq
                                     , u  :: Matrix rq }
data Ciphertext gad tag rq    = CTxt { h  :: tag
                                     , b  :: LWEOutput gad rq
                                     , b' :: LWEOutput gad rq }

gen :: (r ~ LiftOf rq, Reduce r rq, Ring rq, Module tag rq,
        Gadget gad rq, RoundedGaussianCyc cm r, MonadRandom rnd)
  => PublicParam rq
  -> rnd (SecretKey gad rq, PublicKey' gad tag rq)
gen aBar = do
  (r, a) <- genTrap aBar $ Tag zero
  u      <- gaussianMtx 1 $ cols    -- How to determine number of columns in U?
  return (r, PK' a u)

gen' :: (r ~ LiftOf rq, Reduce r rq, Ring rq, Module ff rq,
        Gadget gad rq, RoundedGaussianCyc cm r,
        MonadRandom rnd, Random rq)
  => Int
  -> rnd (SecretKey gad rq, PublicKey gad ff rq)
gen' = gen =<< rndPublicParam -- takes integer value for mBar as input

enc :: (Rescale msg rq, MonadRandom rnd, Random rq, Random tag)
  => PublicKey' gad tag rq -> msg -> rnd (Ciphertext gad tag rq)
enc (PK' a u) m = do
  h  <- rndTag
  s  <- rndSecret
  b  <- lweRand a h s
  b' <- lweRand u h s  -- What format/type will the matrix U be?
  return CTxt h b $ b' + rescale m

dec :: (Field tag, Ring rq, Correct gad rq, Module tag rq,
        Rescale rq msg)
  => PublicKey' gad tag rq -> SecretKey gad rq -> Ciphertext gad tag rq
  -> Maybe msg
dec (PK' a u) sk (CTxt h b b') =
  let (Sec s, e) = lweInv a sk h b
      plaintext  = rescale $ b' - scale s u
      shortError = errorSqNorm e < threshold
      nonZeroTag = h ~= zero
  in if nonZeroTag && shortError then Just plaintext else Nothing


-- SUBROUTINES --

errorSqNorm :: ((cm z) ~ LiftOf (cm zq), LiftCyc cm zq, GSqNormCyc cm z)
  => LWEError (cm zq) -> z
errorSqNorm (Err eBar e') = let sqNorm = Prelude.sum $ fmap (gSqNorm . liftCyc)
                            in sqNorm eBar + sqNorm e'

-- threshold ::
