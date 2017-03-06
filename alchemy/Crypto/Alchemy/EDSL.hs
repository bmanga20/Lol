{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Crypto.Alchemy.EDSL where

import Crypto.Alchemy.Lam ()
import Crypto.Alchemy.PTLang ()
import Crypto.Alchemy.CTLang ()
import Crypto.Alchemy.Interpreter.Evaluator ()
import Crypto.Alchemy.Interpreter.DepthEvaluator ()
import Crypto.Alchemy.Interpreter.PT2CT ()

{- CJP: vestigial from we had entailAdditiveSymPT
instance (SymCT ctexpr, Eq zp)
  => Additive.C (PT2CT ctexpr (d :: Nat) (Cyc t m zp)) where

  negate (P2CTerm a) = P2CTerm (\p zqs -> negate (a p zqs)
                                 \\ witness entailRingSymCT (a p zqs))
-}

