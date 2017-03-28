{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RebindableSyntax     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Crypto.Alchemy.Interpreter.PT2CT where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Random
import Control.Monad.Reader
import Control.Monad.State.Strict

import Crypto.Alchemy.Common
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.CT
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.HomomTunnel
import Crypto.Lol hiding (Pos(..))
import Crypto.Lol.Applications.SymmSHE hiding (tunnelCT)

import Data.Dynamic
import Data.Maybe (mapMaybe)
import Data.Type.Natural (Nat(..))

compile :: forall m'map zqs zq'map gad v ctexpr d a rnd mon .
  (MonadRandom rnd, mon ~ ReaderT v (StateT ([Dynamic],[Dynamic]) rnd))
  => v -> mon (PT2CT m'map zqs zq'map gad v ctexpr d a) -> rnd (ctexpr (F m'map zqs d a))
compile v a = runP2C <$> (flip evalStateT ([],[]) $ flip runReaderT v a)

type family F m'map zqs d a where
  F m'map zqs d (Cyc t m zp) = CT m zp (Cyc t (Lookup m m'map) (zqs !! d))
-- EAC: Not quite right: we shouldn't force `da` to be a Nat, otherwise `a` can't be a function!
  F m'map zqs ('N da db) (a -> b) =
    (F m'map zqs ('F da) a) -> (F m'map zqs db b)

newtype PT2CT :: [(Factored,Factored)]
           -> [*]
           -> [(*,*)]
           -> *
           -> *
           -> (* -> *)
           -> Depth
           -> *
           -> * where
  P2C :: {runP2C :: ctexpr (F m'map zqs d a)} -> PT2CT m'map zqs zq'map gad v ctexpr d a

instance (SymCT ctexpr) => AddPT (PT2CT m'map zqs zq'map gad v ctexpr d) where

  type AddPubCtxPT   (PT2CT m'map zqs zq'map gad v ctexpr d) t m zp =
    (AddPubCtxCT ctexpr t m (Lookup m m'map) zp (zqs !! d))
  type MulPubCtxPT   (PT2CT m'map zqs zq'map gad v ctexpr d) t m zp =
    (MulPubCtxCT ctexpr t m (Lookup m m'map) zp (zqs !! d))
  type AdditiveCtxPT (PT2CT m'map zqs zq'map gad v ctexpr d) t m zp =
    (AdditiveCtxCT ctexpr t m (Lookup m m'map) zp (zqs !! d))

  (P2C a) +# (P2C b) = P2C $ a +^ b

  negPT (P2C a) = P2C $ negCT a

  addPublicPT a (P2C b) = P2C $ addPublicCT a b

  mulPublicPT a (P2C b) = P2C $ mulPublicCT a b

instance (SymCT ctexpr, MonadRandom mon, MonadReader v mon, MonadState ([Dynamic],[Dynamic]) mon)
  => MulPT mon (PT2CT m'map zqs zq'map gad v ctexpr) where
  type RingCtxPT (PT2CT m'map zqs zq'map gad v ctexpr) ('F d) t m zp =
    (RingCtxCT ctexpr t m (Lookup m m'map) zp (zqs !! ('F ('S d))),
     RescaleCtxCT ctexpr t m (Lookup m m'map) zp (zqs !! ('F ('S d))) (zqs !! ('F d)),
     KeySwitchCtxCT ctexpr gad t m (Lookup m m'map) zp (Lookup (zqs !! ('F ('S d))) zq'map) (zqs !! ('F ('S d))),
     GenSKCtx t (Lookup m m'map) (LiftOf zp) v, KSHintCtx gad t (Lookup m m'map) (LiftOf zp) (Lookup (zqs !! ('F ('S d))) zq'map),
     Typeable (Cyc t (Lookup m m'map) (LiftOf zp)), Typeable (KSQuadCircHint gad (Cyc t (Lookup m m'map) (Lookup (zqs !! ('F ('S d))) zq'map))))

  -- EAC: should key switch before the mul, only if necessary. Current signature of *# doesn't allow this...
  (*#) :: forall rp t m zp zqid zq expr d .
    (rp ~ Cyc t m zp, zqid ~ ('F ('S d)), zq ~ (zqs !! zqid), expr ~ PT2CT m'map zqs zq'map gad v ctexpr,
     RingCtxPT (PT2CT m'map zqs zq'map gad v ctexpr) ('F d) t m zp) =>
          mon (expr zqid rp -> expr zqid rp -> expr ('F d) rp)
  (*#) = do
    hint :: KSQuadCircHint gad (Cyc t (Lookup m m'map) (Lookup zq zq'map)) <-
      getKSHint (Proxy::Proxy zq'map) (Proxy::Proxy (LiftOf zp)) (Proxy::Proxy zq)
    return $ \(P2C a) (P2C b) -> P2C $ rescaleCT $ keySwitchQuadCT hint $ a *^ b

instance (SymCT ctexpr, HomomTunnel mon ctexpr, MonadRandom mon, MonadReader v mon, MonadState ([Dynamic],[Dynamic]) mon)
  => HomomTunnel mon (PT2CT m'map zqs zq'map gad v ctexpr d) where
  type TunnelCtxPT (PT2CT m'map zqs zq'map gad v ctexpr d) t e r s zp =
    (TunnelCtxCT ctexpr gad t e r s (e * ((Lookup r m'map) / r)) (Lookup r m'map) (Lookup s m'map) zp (zqs !! d),
     GenSKCtx t (Lookup r m'map) (LiftOf zp) v, Typeable (Cyc t (Lookup r m'map) (LiftOf zp)),
     GenSKCtx t (Lookup s m'map) (LiftOf zp) v, Typeable (Cyc t (Lookup s m'map) (LiftOf zp)),
     GenTunnelInfoCtx t e r s (e * ((Lookup r m'map) / r)) (Lookup r m'map) (Lookup s m'map) (LiftOf zp) zp (zqs !! d) gad)
  -- EAC: TODO Need to modSwitch up before a *sequence* of tunnels, and down after. How do we detect this?
  tunnelPT :: forall t e r s zp . (TunnelCtxPT (PT2CT m'map zqs zq'map gad v ctexpr d) t e r s zp)
           => Linear t zp e r s -> mon (PT2CT m'map zqs zq'map gad v ctexpr d (Cyc t r zp) -> PT2CT m'map zqs zq'map gad v ctexpr d (Cyc t s zp))
  tunnelPT f = do
    thint :: TunnelInfo gad t e r s (e * ((Lookup r m'map) / r)) (Lookup r m'map) _ zp (zqs !! d) <- genTunnHint f
    return $ \(P2C a) -> P2C $ tunnelCT thint a

instance (Lambda ctexpr) => LambdaD (PT2CT m'map zqs zq'map gad v ctexpr) where
  lamD f = P2C $ lam $ runP2C . f . P2C
  appD (P2C f) = P2C . app f . runP2C

--runP2C :: PT2CT m'map zqs zq'map gad v ctexpr d a ->
{-
instance Compile (PT2CT ctexpr m'map zqs (d :: Nat)) ctexpr (Cyc t m zp) where
  type CompiledType (PT2CT ctexpr m'map zqs d) (Cyc t m zp) = CT m zp (Cyc t (Lookup m m'map) (zqs !! d))
  compile (P2C a) = a

instance (Compile (PT2CT ctexpr m'map zqs db) ctexpr b, Lambda ctexpr)
  => Compile (PT2CT ctexpr m'map zqs '( (da :: Nat), db)) ctexpr (Cyc t ma zpa -> b) where
  type CompiledType (PT2CT ctexpr m'map zqs '(da,db)) (Cyc t ma zpa -> b) =
    (CompiledType (PT2CT ctexpr m'map zqs da) (Cyc t ma zpa) -> CompiledType (PT2CT ctexpr m'map zqs db) b)
  compile (P2CLam f) = lam $ compile . f . P2C
-}


-- retrieve the scaled variance parameter from the Reader
getSvar :: (MonadReader v mon) => mon v
getSvar = ask

-- retrieve a key from the state, or generate a new one otherwise
getKey :: forall z v mon t m' . (MonadReader v mon, MonadState ([Dynamic], [Dynamic]) mon,
           MonadRandom mon, GenSKCtx t m' z v, Typeable (Cyc t m' z))
  => mon (SK (Cyc t m' z))
getKey = keyLookup >>= \case
  (Just s) -> return s
  -- generate a key with the variance stored in the Reader monad
  Nothing -> genSK =<< getSvar

-- not memoized right now, but could be if we also store the linear function as part of the lookup key
-- EAC: https://ghc.haskell.org/trac/ghc/ticket/13490
genTunnHint :: forall mon gad t e r s e' r' s' z zp zq v .
  (MonadReader v mon, MonadState ([Dynamic], [Dynamic]) mon, MonadRandom mon,
   GenSKCtx t r' z v, Typeable (Cyc t r' (LiftOf zp)),
   GenSKCtx t s' z v, Typeable (Cyc t s' (LiftOf zp)),
   GenTunnelInfoCtx t e r s e' r' s' z zp zq gad,
   z ~ LiftOf zp)
  => Linear t zp e r s -> mon (TunnelInfo gad t e r s e' r' s' zp zq)
genTunnHint linf = do
  skout <- getKey @z
  sk <- getKey @z
  tunnelInfo linf skout sk

-- retrieve a key-switch hint from the state, or generate a new one otherwise
getKSHint :: forall v mon t z gad m' (zq :: *) zq' map .
  (-- constraints for getKey
   MonadReader v mon, MonadState ([Dynamic], [Dynamic]) mon,
   MonadRandom mon, GenSKCtx t m' z v, Typeable (Cyc t m' z),
   -- constraints for hintLookup
   Typeable (KSQuadCircHint gad (Cyc t m' zq')),
   -- constraints for ksQuadCircHint
   zq' ~ Lookup zq map, KSHintCtx gad t m' z zq')
  => Proxy map -> Proxy z -> Proxy zq -> mon (KSQuadCircHint gad (Cyc t m' zq'))
getKSHint _ _ _ = hintLookup >>= \case
  (Just h) -> return h
  Nothing -> do
    sk :: SK (Cyc t m' z) <- getKey
    ksQuadCircHint sk

-- lookup a key in the state
keyLookup :: (Typeable a, MonadState ([Dynamic], b) mon) => mon (Maybe a)
keyLookup = (dynLookup . fst) <$> get

-- lookup a hint in the state
hintLookup :: (Typeable a, MonadState (b, [Dynamic]) mon) => mon (Maybe a)
hintLookup = (dynLookup . snd) <$> get

-- lookup an item in a dynamic list
dynLookup :: (Typeable a) => [Dynamic] -> Maybe a
dynLookup ds = case mapMaybe fromDynamic ds of
  [] -> Nothing
  [x] -> Just x
