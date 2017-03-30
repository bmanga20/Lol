{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Crypto.Alchemy.Interpreter.DupRescale where

import Crypto.Alchemy.Language.CT
import Crypto.Alchemy.Language.Lam
import Crypto.Lol (Cyc)
import Crypto.Lol.Applications.SymmSHE (CT)
import Data.Typeable

-- unlike section 2.4 of the lecture notes, we don't use a function from the
-- context to the value
-- this is because *every* op would then have to call rescaleCT (if there's a context)
-- with the possible exception of rescaleCT itself, if the context is right.
-- Thus it seems cleaner to work "bottom-up" rather than "top-down".

runDupRescale :: DupRescale expr a -> expr a
runDupRescale (Ctx _ a) = a
runDupRescale (NoCtx a) = a

data DupRescale expr a where
  -- indicates that `expr a` is the result of a rescale from b to a
  -- holds the value both pre- and post-rescaling
  Ctx :: (Typeable b) => expr b -> expr a -> DupRescale expr a
  -- indicates that `expr a` is *not* the output of rescaleCT.
  NoCtx :: expr a -> DupRescale expr a

-- map, ignoring context
dupMap :: (expr a -> expr b) -> DupRescale expr a -> DupRescale expr b
dupMap f = NoCtx . f . runDupRescale

instance (SymCT expr) => SymCT (DupRescale expr) where

  type AdditiveCtxCT  (DupRescale expr) ct     = (AdditiveCtxCT  expr ct)
  type RingCtxCT      (DupRescale expr) ct     = (RingCtxCT      expr ct)
  type ModSwitchCtxCT (DupRescale expr) ct zp' = (ModSwitchCtxCT expr ct zp')
  type RescaleCtxCT   (DupRescale expr) t m m' zp zq zq' =
    (Typeable (CT m zp (Cyc t m' zq)),
     Typeable (CT m zp (Cyc t m' zq')),
     RescaleCtxCT expr t m m' zp zq zq')
  type AddPubCtxCT    (DupRescale expr) ct     = (AddPubCtxCT expr ct)
  type MulPubCtxCT    (DupRescale expr) ct     = (MulPubCtxCT expr ct)
  type KeySwitchCtxCT (DupRescale expr) ct zq' gad =
    (KeySwitchCtxCT expr ct zq' gad)
  type TunnelCtxCT    (DupRescale expr) t e r s e' r' s' zp zq gad =
    (TunnelCtxCT expr t e r s e' r' s' zp zq gad)

  a +^ b = NoCtx $ (runDupRescale a) +^ (runDupRescale b)

  negCT = dupMap negCT

  a *^ b = NoCtx $ (runDupRescale a) *^ (runDupRescale b)

  modSwitchPT = dupMap modSwitchPT

  rescaleCT :: forall ct zq' m zp t m' zq .
    (RescaleCtxCT (DupRescale expr) t m m' zp zq zq', ct ~ CT m zp (Cyc t m' zq))
            => (DupRescale expr) (CT m zp (Cyc t m' zq')) -> (DupRescale expr) ct
  rescaleCT (Ctx (prev :: expr ct') x) =
    case (eqT :: Maybe (ct' :~: ct)) of
      -- previous op scaled from zq -> zq', so rather than rescaling back down, we just use the un-rescaled value
      (Just Refl) -> NoCtx prev
      -- previous op was a rescale, but from a different modulus
      Nothing -> Ctx x $ rescaleCT x
  rescaleCT (NoCtx x) = Ctx x $ rescaleCT x

  addPublicCT = dupMap . addPublicCT

  mulPublicCT = dupMap . mulPublicCT

  keySwitchQuadCT = dupMap . keySwitchQuadCT

  tunnelCT = dupMap . tunnelCT

-- EAC: sharing implications?
-- consider: (\x -> (rescaleDown x) + (x *x)) (rescaleUp y)
-- if we simplify this to \y -> y + ((rescaleUp y)*(rescaleUp y)),
-- we end up doing the rescale twice (but remove the duplicate)
instance (Lambda expr) => Lambda (DupRescale expr) where
  lam f = NoCtx $ lam $ \a -> runDupRescale $ f $ NoCtx a
  app f a = NoCtx $ app (runDupRescale f) (runDupRescale a)