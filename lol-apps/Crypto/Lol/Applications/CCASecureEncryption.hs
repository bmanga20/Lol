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
import Crypto.Lol.Applications.TrapdoorGeneration

import Data.Set

import MathObj.Matrix as M

type Zq q = ZqBasic q Int64
type U q n = Set (Vector q^n (Zq q))

type SecretKey = Trapdoor

data Ring f q n = {fx :: Vector n (Zq q)}

gen :: forall n rq rnd . (MonadRandom rnd, PosC n)
  => rnd (SecretKey gad rq, PublicKey gad rq)
gen = let rowDim = sPosToInt $ sing :: Sing n
      in genTrap Nothing $ zeroMatrix rowDim rowDim

enc :: PublicKey -> Message -> (U q n, Message)
enc pk m = let u = getRandom
               au = pk + matExtend (zeroMatrix n m') $ (hom u) * g
               s = randomMtx 1 n
               eBar =
               eOne =
               e = matExtend eBar eOne
               mEncoded = matExtend (zeroMatrix 1 (m - nk)) $ encode m
               b = 2 * s * au + e + mEncoded
           in (u, b)

dec ::


encode :: Matrix Int -> Matrix Bool -> Matrix Int
encode s m = if numRows s ~= numColumns s
                || numColumns s ~= numRows m
                || numColumns m ~= 1
             then error "encode: mismatched matrix dimensions"
             else encode' s m

encode' :: Matrix Int -> Matrix Bool -> Matrix Int
encode' s m = let m' = map (\x -> if x then 1 else 0) $ head $ columns m
              in s * m'

-- | Injective ring homomorphism from @R = Z_q[x]/f(x)@ to @Z_q^{n \times n}@
-- @hom a@ represents multiplication by @a \in R@
hom :: RingElt -> MatrixZq q
hom a = let n' = sPosToInt $ sing :: Sing n
            a' =
            mtxCols = take n' $ iterate multByX a'
        in transpose $ M.fromList n' n' $ concat mtxCols

multByX :: [Zq q] -> [Zq q]
multByX a = let f    =
                base = 0 : init a
                red  = map (* (last a)) f
          in zipWith (-) base red
