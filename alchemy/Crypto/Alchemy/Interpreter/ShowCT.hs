{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE TypeFamilies        #-}

module Crypto.Alchemy.Interpreter.ShowCT where

import Algebra.Additive as Additive (C(..))
import Algebra.Ring as Ring (C)

import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.CT
import Crypto.Lol

data ShowCT (a :: *) = SCT {bindID::Int, unSCT::String}

instance Lambda ShowCT where
  lam f =
    -- EAC: use laziness!
    let (SCT i b) = f $ SCT i ("x" ++ show i)
    in SCT (i+1) $ "\\x" ++ show i ++ " -> " ++ "( " ++ b  ++ " )"
  app (SCT i f) (SCT _ a) = SCT i $ "( " ++ f ++ " ) " ++ a

instance SymCT ShowCT where

  type RescaleCtxCT   ShowCT t m m' zp zq' zq = ()
  type AddPubCtxCT    ShowCT t m m' zp     zq = (Show (Cyc t m zp))
  type MulPubCtxCT    ShowCT t m m' zp     zq = (Show (Cyc t m zp))
  type KeySwitchCtxCT ShowCT gad t m m' zp zq' zq = ()
  type TunnelCtxCT    ShowCT gad t e r s e' r' s' zp zq = ()

  rescaleCT (SCT _ a) = SCT 0 $ "rescale ( " ++ a ++ " )"
  addPublicCT a (SCT _ b) = SCT 0 $ "( " ++ show a ++ " )" ++ " + " ++ "( " ++ b ++ " )"
  mulPublicCT a (SCT _ b) = SCT 0 $ "( " ++ show a ++ " )" ++ " * " ++ "( " ++ b ++ " )"
  keySwitchQuadCT _ (SCT _ a) = SCT 0 $ "keySwitch <HINT> ( " ++ a ++ " )"
  tunnelCT _ (SCT _ a) = SCT 0 $ "tunnel <FUNC> " ++ "( " ++ a ++ " )"

instance Additive.C (ShowCT a) where
  zero = SCT 0 "0"
  (SCT _ a) + (SCT _ b) = SCT 0 $ "( " ++ a ++ " )" ++ " + " ++ "( " ++ b ++ " )"
  negate (SCT _ a) = SCT 0 $ "neg " ++ "( " ++ a ++ " )"

instance Ring.C (ShowCT a) where
  one = SCT 0 "1"
  (SCT _ a) * (SCT _ b)  = SCT 0 $ "( " ++ a ++ " )" ++ " * " ++ "( " ++ b ++ " )"

instance Lit ShowCT where
  type LitCtx ShowCT a = (Show a)
  lit a = SCT 0 $ show a