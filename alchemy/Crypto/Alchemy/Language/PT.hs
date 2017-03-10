{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

module Crypto.Alchemy.Language.PT where

import Crypto.Lol hiding (Pos(..))
import Data.Type.Natural
import Crypto.Lol.Types.ZPP
import Crypto.Lol.Cyclotomic.Tensor

-- | Symantics for leveled plaintext operations of some depth @d@.

class SymPT expr where

  {- CJP: scrapping entailment here for the subtle reason that in the
 PT-to-CT compiler, the Additive instance for CT needs a weird extra
 constraint (namely, Eq zp) that shouldn't be exposed here.  But
 leaving it out makes it impossible to implement 'zero', and hence to
 construct the entailment.  Also, since we need a depth-aware
 multiplication operator, might as well have similar ones for
 addition/subtraction.

  -- | Entailment of additive group structure.  (Addends must be at
  -- the same depth as output.)

  entailAdditiveSymPT :: (rp ~ Cyc t m zp)
                      => Tagged (expr d rp)
                         ((Additive rp) :- Additive (expr d rp))
  -}
  addPublicPT :: (rp ~ Cyc t m zp, Additive rp) => rp -> expr d rp -> expr d rp
  mulPublicPT :: (rp ~ Cyc t m zp, Ring rp) => rp -> expr d rp -> expr d rp


  (+#) :: (rp ~ Cyc t m zp, Fact m, CElt t zp) =>
          -- CJP: generalize input depths?
          expr d rp -> expr d rp -> expr d rp

  neg :: (rp ~ Cyc t m zp, Fact m, CElt t zp) => expr d rp -> expr d rp

  -- | Plaintext multiplication.  Inputs must be one depth less than
  -- output (so we can't use 'Ring').

  (*#) :: (rp ~ Cyc t m zp, Fact m, CElt t zp) =>
          -- CJP: generalize input depths?
          expr ('S d) rp -> expr ('S d) rp -> expr d rp

  tunnelPT :: (e ~ FGCD r s, e `Divides` r, e `Divides` s, CElt t zp, ZPP zp,
               TElt t (ZpOf zp))
           => expr d (Cyc t r zp) -> expr d (Cyc t s zp)

(-#) :: (SymPT expr, rp ~ Cyc t m zp, Fact m, CElt t zp)
     => expr d rp -> expr d rp -> expr d rp
a -# b = a +# (neg b)