{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}

module Crypto.Alchemy.PTLang where

import Crypto.Lol hiding (Pos(..))
import Data.Type.Natural

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
  litPT :: rp -> expr d rp


  (+#), (-#) :: (rp ~ Cyc t m zp, Fact m, CElt t zp) =>
                -- CJP: generalize input depths?
                expr d rp -> expr d rp -> expr d rp

  -- | Plaintext multiplication.  Inputs must be one depth less than
  -- output (so we can't use 'Ring').

  (*#) :: (rp ~ Cyc t m zp, Fact m, CElt t zp) =>
          -- CJP: generalize input depths?
          expr ('S d) rp -> expr ('S d) rp -> expr d rp
-- EAC: d is now 'level' and we expect the zqs list to be (zq0, (zq0,zq1), ...) in increasing size
-- so that we can give more zqs than we end up using