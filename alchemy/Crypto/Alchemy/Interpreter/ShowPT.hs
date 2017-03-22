{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE TypeFamilies        #-}

module Crypto.Alchemy.Interpreter.ShowPT where

import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.PT
import Crypto.Lol (Cyc)

data ShowPT (d :: k) (a :: *) = SPT {bindID::Int, unSPT::String}

instance LambdaD ShowPT where
  lamD f =
    -- EAC: use laziness!
    let (SPT i b) = f $ SPT i ("x" ++ show i)
    in SPT (i+1) $ "\\x" ++ show i ++ " -> " ++ "( " ++ b  ++ " )"
  appD (SPT i f) (SPT _ a) = SPT i $ "( " ++ f ++ " ) " ++ a

instance SymPT ShowPT where

  type AddPubCtxPT   ShowPT d t m zp     = (Show (Cyc t m zp))
  type MulPubCtxPT   ShowPT d t m zp     = (Show (Cyc t m zp))
  type AdditiveCtxPT ShowPT d t m zp     = ()
  type RingCtxPT     ShowPT d t m zp     = ()
  type TunnelCtxPT   ShowPT d t e r s zp = ()

  (SPT _ a) +# (SPT _ b) = SPT 0 $ "( " ++ a ++ " )" ++ " + " ++ "( " ++ b ++ " )"
  neg (SPT _ a) = SPT 0 $ "neg " ++ "( " ++ a ++ " )"
  (SPT _ a) *# (SPT _ b)  = SPT 0 $ "( " ++ a ++ " )" ++ " * " ++ "( " ++ b ++ " )"
  addPublicPT a (SPT _ b) = SPT 0 $ "( " ++ (show a) ++ " )" ++ " + " ++ "( " ++ b ++ " )"
  mulPublicPT a (SPT _ b) = SPT 0 $ "( " ++ (show a) ++ " )" ++ " * " ++ "( " ++ b ++ " )"
  tunnelPT _ (SPT _ a) = SPT 0 $ "tunnel <FUNC> " ++ "( " ++ a ++ " )"

instance Lit (ShowPT d) where
  type LitCtx (ShowPT d) a = (Show a)
  lit a = SPT 0 $ show a