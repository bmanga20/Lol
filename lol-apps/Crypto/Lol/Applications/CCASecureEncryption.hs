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

module Crypto.Lol.Applications.CCASecureEncryption where

import Crypto.Lol
import Crypto.Lol.Applications.TrapdoorGeneration

import Data.Set

import MathObj.Matrix as M

type Zq q = ZqBasic q Int64
type U q n = Set (Vector q^n (Zq q))

gen :: forall n q d . PosC n => Distribution d -> Trapdoor q d
gen dist = let n = sPosToInt $ sing :: Sing n
           in genTrap dist Nothing $ zeroMatrix n n

enc :: PublicKey -> Message -> (U q n, Message)
enc pk m = let u = getRandom
               au =
               s =
               eBar =
               eOne =

               b =
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
-- @h(a)@ represents multiplication by @a \in R@
h :: RingElt -> MatrixZq q
h a = let n' = sPosToInt $ sing :: Sing n
          a' =
          mtxCols = take n' $ iterate multByX a'
      in transpose $ M.fromList n' n' $ concat mtxCols

multByX :: [Zq q] -> [Zq q]
multByX a = let f    =
                base = 0 : init a
                red  = map (* (last a)) f
            in zipWith (-) base red
