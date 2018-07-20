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

module Crypto.Lol.Applications.TrapdoorGeneration where

import Control.Monad.Random

import Crypto.Lol

import MathObj.Matrix as Mtx

-- TYPES --

data MatrixStatic (r :: SPos) (c :: SPos) a =
  MS :: r -> c -> Matrix a

data MatrixStatic (SPos r) (SPos c) a =
  something...

type family
mtxStatic :: r -> c -> a -> Matrix a

data PublicKey n gad rq = PK { aBar :: PublicParam n rq
                             , a'   :: Matrix rq  -- also a PublicParam?
                             , h    :: Tag n rq }

newtype PublicParam n rq = ABar (Matrix rq)

newtype Tag n rq = Tag (Matrix rq)

data Trapdoor gad rq = TD (Matrix rq)

data LWESecret = LWESec (Matrix rq)

data LWEError =

data LWEOutput = LWEOutput { sec :: LWESecret, err :: LWEError }


-- METHODS --

gadgetMtx :: GadgetMtx n gad
gadgetMtx

genTrap :: (MonadRandom rnd)
  => Maybe (PublicParam n rq)
  -> Maybe (Tag n rq)
  -> rnd (Trapdoor gad rq, PublicKey gad rq)
genTrap p t =
  let rowDim = sPosToInt $ sing :: Sing n
      aBar = fromMaybe (randomMtx rowDim $ numCols h) p
      tagH = fromMaybe (identityMtx rowDim) h
  in PK aBar 


lweSecret :: Trapdoor gad -> Tag -> LWEOutput -> LWESecret
lweSecret r h b =

lweInv :: PublicKey gad -> Trapdoor gad -> Tag -> LWEOutput
  -> (LWESecret, LWEError)
lweInv a r h b =
  let s = lweSecret r h b
      e =
  in (s,e)

lwe :: PublicKey -> Tag -> LWESecret -> LWEError -> LWEOutput
lwe a h' s e =

lweRand :: PublicKey -> Tag -> LWESecret -> LWEOutput
lweRand a h' s =
  let e = -- generate e of appropriate dimension ( = # cols in A )
  in lwe a h' s e

-- f in forward direction
syndrome ::
