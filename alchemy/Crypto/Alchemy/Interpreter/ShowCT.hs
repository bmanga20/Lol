{-# LANGUAGE TypeFamilies #-}

module Crypto.Alchemy.Interpreter.ShowCT (ShowCT, showCT) where

import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.CT
import Crypto.Lol (Cyc)
import Crypto.Lol.Applications.SymmSHE (CT)

showCT :: ShowCT a -> String
showCT (SCT a) = a 0

data ShowCT (a :: *) = SCT (Int -> String)

instance SymCT ShowCT where

  type AdditiveCtxCT  ShowCT a = ()
  type RingCtxCT      ShowCT a = ()
  type ModSwitchCtxCT ShowCT a zp' = ()
  type RescaleCtxCT   ShowCT a zq' = ()
  type AddPubCtxCT    ShowCT (CT m zp (Cyc t m' zq)) = (Show (Cyc t m zp))
  type MulPubCtxCT    ShowCT (CT m zp (Cyc t m' zq)) = (Show (Cyc t m zp))
  type KeySwitchCtxCT ShowCT a zq' gad = ()
  type TunnelCtxCT    ShowCT t e r s e' r' s' zp zq gad = ()

  (SCT a) +^ (SCT b) = SCT $ \i -> "( " ++ a i ++ " )" ++ " + " ++ "( " ++ b i ++ " )"
  (SCT a) *^ (SCT b) = SCT $ \i -> "( " ++ a i ++ " )" ++ " * " ++ "( " ++ b i ++ " )"
  negCT (SCT a) = SCT $ \i -> "-( " ++ a i ++ " )"
  modSwitchPT (SCT a) = SCT $ \i -> "modSwitch $ " ++ a i
  rescaleCT (SCT a) = SCT $ \i -> "rescale $ " ++ a i
  addPublicCT a (SCT b) = SCT $ \i -> "( " ++ show a ++ " )" ++ " + " ++ "( " ++ b i ++ " )"
  mulPublicCT a (SCT b) = SCT $ \i -> "( " ++ show a ++ " )" ++ " * " ++ "( " ++ b i ++ " )"
  keySwitchQuadCT _ (SCT a) = SCT $ \i -> "keySwitch <HINT> $ " ++ a i
  tunnelCT _ (SCT a) = SCT $ \i -> "tunnel <FUNC> $ " ++ a i

instance Lambda ShowCT where
  lam f = SCT $ \i ->
    let x = "x" ++ show i
        (SCT b) = f $ SCT $ const x
    in "\\" ++ x ++ " -> " ++ (b $ i+1)
  app (SCT f) (SCT a) = SCT $ \i -> "( " ++ f i ++ " ) " ++ a i

instance Lit ShowCT where
  type LitCtx ShowCT a = (Show a)
  lit = SCT . const . show
