{-|
Module      : Crypto.Lol.Applications.TrapdoorGeneration
Description : Efficient lattice trapdoor generation from <http://web.eecs.umich.edu/~cpeikert/pubs/efftrap.pdf [MP12]>.
Copyright   : (c) Bogdan Manga, 2018
                  Chris Peikert, 2018
License     : GPL-3
Maintainer  : cpeikert@alum.mit.edu
Stability   : experimental
Portability : POSIX

Efficient lattice trapdoor generation from <http://web.eecs.umich.edu/~cpeikert/pubs/efftrap.pdf [MP12]>.
-}

module Crypto.Lol.Applications.TrapdoorGeneration where

import Crypto.Lol

import Data.Maybe

import MathObj.Matrix as M

type Zq q = ZqBasic q Int64
type MatrixZq q = Matrix (Zq q)

-- | Combines parity-check matrix @A@ with @G@-trapdoor @R@ and relevant tag @H@
-- Parameterized by prime @q@ and distribution identifier @d@
data Trapdoor q d = Trapdoor { a :: (Matrix (Zq q))
                             , r :: (Matrix Int)
                             , h :: (Matrix (Zq q)) }

data Distribution d =

gadgetMtx :: forall gad q . (_) => Int -> MatrixZq q
gadgetMtx n = let gadgetVec = Proxy :: Proxy gad
              in

basisMtx :: forall q . (SPos q) => Int -> MatrixZq q
basisMtx n =

genTrap :: Distribution d -> Maybe (MatrixZq q) -> Maybe (MatrixZq q) -> Trapdoor q d
genTrap dist aBar' h =
  let tagG = maybe g (*g) h                    -- | computes HG
      aBar = fromMaybe (randomMtx n m') aBar'  -- | value for \overline{A}
      r    = randomMtx m' w -- need to choose over distribution d...
      hgar = tagG - aBar * r
  in Trapdoor (matExtend aBar hgar) r tagG

invertLWE :: Oracle -> Trapdoor q d -> Matrix (Zq q) -> (Matrix (Zq q), Matrix Int)
invertLWE o t b =
  let ri = transpose $ matExtend (transpose (r t)) idMat
      bHat = transpose $ (transpose b) * ri
      bHatInv = o bHat
      s = (transpose (inverse (h t))) * (fst bHatInv)
      e = b - (transpose (a t)) * s
  in (s,e)

-- | sampleG algorithm: Gaussian sampling
-- want two versions, one when q = 2^k [MP12] and one for the other case [GM18]
sampleGauss ::

-- q = b^k [MP12]
sampleGaussPow ::

-- q < b^k [GM18]
sampleGaussArb ::


-- | takes matrices A and B with same number of rows, returns [A | B]
matExtend :: Matrix a -> Matrix a -> Matrix a
matExtend a b =
  | numRows a /= numRows b = error "matExtend: number of rows doesn't match"
  | otherwise = let aRows = ZipList $ rows a
                    bRows = ZipList $ rows b
                    combinedRows = getZipList $ (++) <$> aRows <*> bRows
                    r = numRows a
                    c = numColumns a + numColumns b
                in fromList r c $ concat abRows
