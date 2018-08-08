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
{-# LANGUAGE PartialTypeSignatures #-}

module Crypto.Lol.Applications.CCASecureEncryption where

import Crypto.Lol
import Crypto.Lol.Applications.Trapdoor as TD

import Data.Set

import MathObj.Matrix as M

type SecretKey gad rq = Trapdoor gad rq

data PublicKey gad ff rq     = PK'  { a     :: TD.PublicKey gad ff rq
                                    , u     :: Matrix rq }
newtype Message rp           = Msg  { unMsg :: rq }
data    Ciphertext gad ff rq = CTxt { h     :: Tag ff
                                    , b     :: LWEOutput gad rq
                                    , b'    :: LWEOutput gad rq }

gen :: (r ~ LiftOf rq, Reduce r rq, Ring rq, Module ff rq,
        Gadget gad rq, RoundedGaussianCyc cm r, MonadRandom rnd)
  => PublicParam rq
  -> rnd (SecretKey gad rq, PublicKey gad ff rq)
gen aBar = do
  (r, a) <- genTrap aBar $ Tag zero
  u      <- gaussianMtx 1 $ cols    -- How to determine number of columns in U?
  return (r, PK' a u)

enc :: (Rescale rp rq, MonadRandom rnd, Random rq)
  => PublicKey gad ff rq -> Message rp -> rnd (Ciphertext gad ff rq)
enc (PK' a u) (Msg m) = do
  h  <- getRandom
  s  <- rndSecret
  b  <- lweRand a h s
  b' <- lweRand u h s
  return CTxt h b $ b' + rescale m

dec :: (Field ff, Ring rq, Correct gad rq, Module ff rq,
        Rescale rq rp)
  => PublicKey gad ff rq -> SecretKey gad rq -> Ciphertext gad ff rq
  -> Maybe (Message rp)
dec (PK' a u) sk (CTxt h b b') =
  let (Sec s, e) = lweInv a sk h b
      plaintext  = Msg $ rescale $ b' - scale s u
      shortError = errorSqNorm e < threshold
      nonZeroTag = h ~= zero
  in if nonZeroTag && shortError then Just plaintext else Nothing


-- SUBROUTINES --

errorSqNorm :: ((cm z) ~ LiftOf (cm zq), LiftCyc cm zq, GSqNormCyc cm z)
  => LWEError cm zq -> z
errorSqNorm (Err eBar e') = let sqNorm = sum $ fmap (gSqNorm . liftCyc) x
                            in sqNorm eBar + sqNorm e'

threshold ::
