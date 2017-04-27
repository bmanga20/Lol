
module Crypto.Alchemy.Interpreter.ErrorCT where

import Crypto.Alchemy.Interpreter.EvalCT
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.SymCT

errorCT :: ErrorCT a -> ([String], I a)
errorCT (ECT s a) = (s,a)

data ErrorCT a = ECT ([String] -> [String]) (I a)

-- | Metacircular ciphertext symantics.
instance SymCT ErrorCT where

  type AdditiveCtxCT  ErrorCT a = (AdditiveCtxCT I a)
  type RingCtxCT      ErrorCT a = (RingCtxCT I a)
  type ModSwitchCtxCT ErrorCT (CT m zp (Cyc t m' zq)) zp'     = (ModSwitchCtxCT I (CT m zp (Cyc t m' zq)) zp')
  type RescaleCtxCT   ErrorCT (CT m zp (Cyc t m' zq)) zq'     = (RescaleCtxCT   I (CT m zp (Cyc t m' zq)) zq')
  type AddPubCtxCT    ErrorCT (CT m zp (Cyc t m' zq))         = (AddPubCtxCT    I (CT m zp (Cyc t m' zq)))
  type MulPubCtxCT    ErrorCT (CT m zp (Cyc t m' zq))         = (MulPubCtxCT    I (CT m zp (Cyc t m' zq)))
  type KeySwitchCtxCT ErrorCT (CT m zp (Cyc t m' zq)) zq' gad = (KeySwitchCtxCT I (CT m zp (Cyc t m' zq)) zq' gad)
  type TunnelCtxCT    ErrorCT t e r s e' r' s' zp zq gad      = (TunnelCtxCT    I t e r s e' r' s' zp zq gad)

  (ECT s1 a) +^ (ECT s2 b) = ECT (\s -> s1 s ++ s2 s) $ a +^ b
  (ECT s1 a) *^ (ECT s2 b) = ECT (\s -> s1 s ++ s2 s) $ a *^ b
  negCT (ECT s a) = ECT id $ negCT a
  modSwitchPT (ECT s a) = ECT s $ modSwitchPT a
  rescaleCT (ECT s a) = ECT s $ rescaleCT a
  addPublicCT b (ECT s a) = ECT s $ addPublicCT b a
  mulPublicCT b (ECT s a) = ECT s $ mulPublicCT b a
  keySwitchQuadCT (ECT s a) = ECT s $ keySwitchQuadCT a
  tunnelCT        f (ECT s a) = ECT s $ tunnelCT f a

instance Lambda ErrorCT where
  lam f = ECT (\s ->
    let (SCT b) = f $ ECT $ const s
    in "\\" ++ x ++ " -> " ++ (b $ i+1)
  app (ECT sf f) (ECT sa a) = ECT (sf . sa) $ app f a

instance Lit ErrorCT where
  type LitCtx ErrorCT a = (LitCtx I a)
  lit = ECT [] lit
