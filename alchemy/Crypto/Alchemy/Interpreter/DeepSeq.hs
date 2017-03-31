{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}

module Crypto.Alchemy.Interpreter.DeepSeq where

import Control.DeepSeq
import Crypto.Alchemy.Language.CT
import Crypto.Lol (Cyc)
import Crypto.Lol.Applications.SymmSHE (CT, TunnelInfo, KSQuadCircHint)

newtype DeepSeq ctexpr a = DS {runDeepSeq :: ctexpr a}

instance (SymCT ctexpr) => SymCT (DeepSeq ctexpr) where

  type AdditiveCtxCT  (DeepSeq ctexpr) ct     = (AdditiveCtxCT ctexpr ct)
  type RingCtxCT      (DeepSeq ctexpr) ct     = (RingCtxCT ctexpr ct)
  type ModSwitchCtxCT (DeepSeq ctexpr) ct zp' = (ModSwitchCtxCT ctexpr ct zp')
  type RescaleCtxCT   (DeepSeq ctexpr) ct zq' = (RescaleCtxCT ctexpr ct zq')
  type AddPubCtxCT    (DeepSeq ctexpr) (CT m zp (Cyc t m' zq))     =
    (NFData (Cyc t m zp), AddPubCtxCT ctexpr (CT m zp (Cyc t m' zq)))
  type MulPubCtxCT    (DeepSeq ctexpr) (CT m zp (Cyc t m' zq))     =
    (NFData (Cyc t m zp), MulPubCtxCT ctexpr (CT m zp (Cyc t m' zq)))
  type KeySwitchCtxCT (DeepSeq ctexpr) (CT m zp (Cyc t m' zq)) zq' gad =
    (NFData (KSQuadCircHint gad (Cyc t m' zq')), KeySwitchCtxCT ctexpr (CT m zp (Cyc t m' zq)) zq' gad)
  type TunnelCtxCT    (DeepSeq ctexpr) t e r s e' r' s' zp zq gad =
    (NFData (TunnelInfo gad t e r s e' r' s' zp zq), TunnelCtxCT ctexpr t e r s e' r' s' zp zq gad)

  (DS !a) +^ (DS !b) = DS $ a +^ b

  negCT (DS !a) = DS $ negCT a

  (DS !a) *^ (DS !b) = DS $ a *^ b

  modSwitchPT (DS !a) = DS $ modSwitchPT a

  rescaleCT (DS !a) = DS $ rescaleCT a

  addPublicCT a (DS !b) = a `deepseq` DS $ addPublicCT a b

  mulPublicCT a (DS !b) = a `deepseq` DS $ mulPublicCT a b

  keySwitchQuadCT a (DS !b) = a `deepseq` DS $ keySwitchQuadCT a b

  tunnelCT a (DS !b) = a `deepseq` DS $ tunnelCT a b
