{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Interpreter.ShowPT where

import Crypto.Alchemy.Depth
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.ModSwPT
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.TunnelPT

data ShowPT (d :: Depth) a = SPT {bindID::Int, unSPT::String}

instance AddPT (ShowPT) where
  type AddPubCtxPT   ShowPT d a = (Show a)
  type MulPubCtxPT   ShowPT d a = (Show a)
  type AdditiveCtxPT ShowPT d a = ()

  (SPT _ a) +# (SPT _ b) = SPT 0 $ "( " ++ a ++ " )" ++ " + " ++ "( " ++ b ++ " )"
  negPT (SPT _ a) = SPT 0 $ "neg $ " ++ a
  addPublicPT a (SPT _ b) = SPT 0 $ "( " ++ (show a) ++ " )" ++ " + " ++ "( " ++ b ++ " )"
  mulPublicPT a (SPT _ b) = SPT 0 $ "( " ++ (show a) ++ " )" ++ " * " ++ "( " ++ b ++ " )"

instance (Applicative mon) => MulPT mon ShowPT where

  type RingCtxPT ShowPT d a = ()

  (*#) = pure $ \(SPT _ a) (SPT _ b) -> SPT 0 $ "( " ++ a ++ " )" ++ " * " ++ "( " ++ b ++ " )"

instance ModSwPT ShowPT where

  type ModSwitchCtxPT ShowPT d a zp' = ()

  modSwitchDec (SPT _ a) = SPT 0 $ "modSwitchDec $ " ++ a

instance (Applicative mon) => TunnelPT mon (ShowPT d) where

  type TunnelCtxPT (ShowPT d) t e r s zp = ()

  tunnelPT _ = pure $ \(SPT _ a) -> SPT 0 $ "tunnel <FUNC> $ " ++ a

instance LambdaD ShowPT where
  lamD f =
    -- EAC: use laziness!
    let (SPT i b) = f $ SPT i ("x" ++ show i)
    in SPT (i+1) $ "\\x" ++ show i ++ " -> " ++ b
  appD (SPT i f) (SPT _ a) = SPT i $ "( " ++ f ++ " ) " ++ a

instance Lit (ShowPT d) where
  type LitCtx (ShowPT d) a = (Show a)
  lit a = SPT 0 $ show a