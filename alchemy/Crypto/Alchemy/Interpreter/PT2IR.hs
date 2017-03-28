{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE RebindableSyntax     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Crypto.Alchemy.Interpreter.PT2IR where

import Control.Monad.Identity

import Crypto.Alchemy.Common
import Crypto.Alchemy.Language.Lam
import qualified Crypto.Alchemy.Language.IR as IR
import Crypto.Alchemy.Language.HomomAddPT
import Crypto.Alchemy.Language.HomomMulD
import Crypto.Alchemy.Language.HomomTunnel
import Crypto.Lol hiding (Pos(..), type (*))
import Crypto.Lol.Applications.SymmSHE (CT)

import Data.Kind
import Data.Type.Natural (Nat(..))

-- If you get compile errors about kinds, make sure that ALL arguments have
-- kind sigs! https://ghc.haskell.org/trac/ghc/ticket/13365
-- | Plaintext to ciphertext compiler.

-- The `forall` is right before the polymorphic argument in order to keep the
-- type polymorphic after partial application. (Otherwise the LamD instance won't compile)
-- See https://ghc.haskell.org/trac/ghc/ticket/13399.
data PT2IR :: (* -> *)
           -> [(Factored,Factored)]
           -> [*]
           -> forall k . k
           -> *
           -> * where
  P2ITerm  :: irexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d)))
              -> PT2IR irexpr m'map zqs d (Cyc t m zp)

  P2ILam :: (PT2IR irexpr m'map zqs da a -> PT2IR irexpr m'map zqs db b)
         -> PT2IR irexpr m'map zqs '(da,db) (a -> b)

instance (HomomAddIR irexpr) => HomomAddPT (PT2IR irexpr m'map zqs d) where

  type AddPubCtx   (PT2IR irexpr m'map zqs d) (Cyc t m zp) =
    (IR.AddPubCtx irexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d))))
  type MulPubCtx   (PT2IR irexpr m'map zqs d) (Cyc t m zp) =
    (IR.MulPubCtx irexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d))))
  type AdditiveCtx (PT2IR irexpr m'map zqs d) (Cyc t m zp) =
    (IR.AdditiveCtx (irexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d)))))

  (P2ITerm a) +# (P2ITerm b) = P2ITerm $ a IR.+# b

  neg (P2ITerm a) = P2ITerm $ IR.neg a

  addPublic a (P2ITerm b) = P2ITerm $ IR.addPublic a b

  mulPublic a (P2ITerm b) = P2ITerm $ IR.mulPublic a b
{-
instance (HomomMulD mon irexpr) => HomomMulD mon (PT2IR irexpr m'map zqs) where
  type RingCtxD (PT2IR irexpr m'map zqs) d t m zp =
    (Ring (irexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! ('S d))))),
     RescaleCtxIR irexpr t m (Lookup m m'map) zp (zqs !! ('S d)) (zqs !! d),
     KeySwitchCtxIR irexpr t m (Lookup m m'map) zp (zqs !! ('S d)))

  -- EAC: should key switch before the mul, only if necessary. Current signature of *# doesn't allow this...
  (*#) :: forall rp t m zp expr d . (rp ~ Cyc t m zp, expr ~ PT2IR irexpr m'map zqs, RingCtxD (PT2IR irexpr m'map zqs) d t m zp) =>
          -- CJP: generalize input depths?
          mon (expr ('S d) rp -> expr ('S d) rp -> expr d rp)
  (*#) = do
    (rescale' :: irexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! ('S d)))) -> irexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d)))) <- rescaleIR
    (ksIR :: irexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! ('S d)))) -> _) <- keySwitchQuadIR
    return $ \(P2ITerm a) (P2ITerm b) -> P2ITerm $ rescale' $ ksIR $ a * b

instance (HomomTunnel mon irexpr) => HomomTunnel mon (PT2IR irexpr m'map zqs d) where
  type TunnelCtx (PT2IR irexpr m'map zqs d) t e r s zp = (TunnelCtx irexpr t e r s (Lookup r m'map) (Lookup s m'map) zp (zqs !! d))

  -- EAC: TODO Need to modSwitch up before a *sequence* of tunnels, and down after. How do we detect this?
  tunnelPT :: forall (d :: Nat) t e r s zp . (TunnelCtxPT (PT2IR irexpr m'map zqs d) t e r s zp)
           => Linear t zp e r s -> mon (PT2IR irexpr m'map zqs d (Cyc t r zp) -> PT2IR irexpr m'map zqs d (Cyc t s zp))
  tunnelPT f = do
    (tunn :: irexpr (CT r zp (Cyc t (Lookup r m'map) (zqs !! d))) -> irexpr (CT s zp (Cyc t (Lookup s m'map) (zqs !! d)))) <- tunnelIR f
    return $ \(P2ITerm a) -> P2ITerm $ tunn a
-}
instance LambdaD (PT2IR irexpr m'map zqs) where
  lamD = P2ILam
  appD (P2ILam f) = f

instance Compile (PT2IR irexpr m'map zqs (d :: Nat)) irexpr (Cyc t m zp) where
  type CompiledType (PT2IR irexpr m'map zqs d) (Cyc t m zp) = CT m zp (Cyc t (Lookup m m'map) (zqs !! d))
  compile (P2ITerm a) = a

instance (Compile (PT2IR irexpr m'map zqs db) irexpr b, Lambda irexpr)
  => Compile (PT2IR irexpr m'map zqs '( (da :: Nat), db)) irexpr (Cyc t ma zpa -> b) where
  type CompiledType (PT2IR irexpr m'map zqs '(da,db)) (Cyc t ma zpa -> b) =
    (CompiledType (PT2IR irexpr m'map zqs da) (Cyc t ma zpa) -> CompiledType (PT2IR irexpr m'map zqs db) b)
  compile (P2ILam f) = lam $ compile . f . P2ITerm
