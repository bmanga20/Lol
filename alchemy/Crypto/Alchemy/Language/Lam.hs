{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Crypto.Alchemy.Language.Lam where

import Control.Monad.Identity
import Crypto.Alchemy.Depth

-- | Lambda abstraction and application.

class Lambda expr where
  -- | Abstract a Haskell function into the object language.
  lam :: (expr a -> expr b) -> expr (a -> b)

  -- | Apply an abstraction.
  app :: expr (a -> b) -> expr a -> expr b

class LambdaD expr where
  lamD :: (expr da a -> expr db b) -> expr ('L da db) (a->b)

-- lam* first weakens repeatedly, then reassociates in one go
lam1 :: (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall j . (Applicative j) => (m :. (i :. j)) (expr d1 a) -> (m :. (i :. j)) (expr d2 b))
    -> (m :. i) (expr ('L d1 d2) (a -> b))
lam1 f = lamPT $ f . var

lam2 :: (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall j . (Applicative j) => (m :. (i :. j)) (expr d1 a) -> (m :. (i :. j)) (expr d2 b) -> (m :. (i :. j)) (expr d3 c))
    -> (m :. i) (expr ('L d1 ('L d2 d3)) (a -> b -> c))
lam2 f = lamPT $ \x -> lamPT $ \y ->
  let reassoc = assocLR
      x' = reassoc $ weakenL x   -- embed from  i . j1       to m . (i . (j1 . j2))
      y' = reassoc y -- embed from (i . j1) . j2 to m . (i . (j1 . j2))
      z  = f (var x') (var y')
  in mapJ2 assocRL z  -- reassociate from m . (i . (j1 . j2)) to m . ((i . j1) . j2)

lam3 :: (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall j . (Applicative j) => (m :. (i :. j)) (expr d1 a) -> (m :. (i :. j)) (expr d2 b) -> (m :. (i :. j)) (expr d3 c) -> (m :. (i :. j)) (expr d4 d))
    -> (m :. i) (expr ('L d1 ('L d2 ('L d3 d4))) (a -> b -> c -> d))
lam3 f = lamPT $ \x -> lamPT $ \y -> lamPT $ \z ->
  let reassoc = assocLR . assocLR
      x' = reassoc $ weakenL $ weakenL x -- embed from  i . j1              to m . (i . (j1 . (j2 . j3)))
      y' = reassoc $ weakenL y     -- embed from (i . j1) . j2        to m . (i . (j1 . (j2 . j3)))
      z' = reassoc z   -- embed from ((i . j1) . j2) . j3 to m . (i . (j1 . (j2 . j3)))
      w = f (var x') (var y') (var z')
  in mapJ2 (assocRL . assocRL) w

lam4 :: (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall j . (Applicative j) => (m :. (i :. j)) (expr d1 a) -> (m :. (i :. j)) (expr d2 b) -> (m :. (i :. j)) (expr d3 c) -> (m :. (i :. j)) (expr d4 d) -> (m :. (i :. j)) (expr d5 e))
    -> (m :. i) (expr ('L d1 ('L d2 ('L d3 ('L d4 d5)))) (a -> b -> c -> d -> e))
lam4 f = lamPT $ \x -> lamPT $ \y -> lamPT $ \z -> lamPT $ \w ->
  let reassoc = assocLR . assocLR . assocLR
      x' = reassoc $ weakenL $ weakenL $ weakenL x -- embed from  i . j1              to m . (i . (j1 . (j2 . (j3 . j4)))
      y' = reassoc $ weakenL $ weakenL y     -- embed from (i . j1) . j2        to m . (i . (j1 . (j2 . j3)))
      z' = reassoc $ weakenL z   -- embed from ((i . j1) . j2) . j3 to m . (i . (j1 . (j2 . j3)))
      w' = reassoc w
      u = f (var x') (var y') (var z') (var w')
  in mapJ2 (assocRL . assocRL . assocRL) u

-- lam*' weakens in one go, then reassociates repeatedly (same sigs as corresponding lam* function)
lam1' :: (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall j . (Applicative j) => (m :. (i :. j)) (expr d1 a) -> (m :. (i :. j)) (expr d2 b))
    -> (m :. i) (expr ('L d1 d2) (a -> b))
lam1' f = lamPT $ f . var

lam2' :: (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall j . (Applicative j) => (m :. (i :. j)) (expr d1 a) -> (m :. (i :. j)) (expr d2 b) -> (m :. (i :. j)) (expr d3 c))
    -> (m :. i) (expr ('L d1 ('L d2 d3)) (a -> b -> c))
lam2' f = lamPT $ \x -> lamPT $ \y ->
  let x' = assocLR $ weakenL x   -- embed from  i . j1       to m . (i . (j1 . j2))
      y' = assocLR y -- embed from (i . j1) . j2 to m . (i . (j1 . j2))
      z  = f (var x') (var y')
  in mapJ2 assocRL z  -- reassociate from m . (i . (j1 . j2)) to m . ((i . j1) . j2)

lam3' :: (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall j . (Applicative j) => (m :. (i :. j)) (expr d1 a) -> (m :. (i :. j)) (expr d2 b) -> (m :. (i :. j)) (expr d3 c) -> (m :. (i :. j)) (expr d4 d))
    -> (m :. i) (expr ('L d1 ('L d2 ('L d3 d4))) (a -> b -> c -> d))
lam3' f = lamPT $ \x -> lamPT $ \y -> lamPT $ \z ->
  let x' = assocLR $ weakenL x -- embed from  i . j1              to m . (i . (j1 . (j2 . j3)))
      y' = assocLR $ assocLR $ weakenL y     -- embed from (i . j1) . j2        to m . (i . (j1 . (j2 . j3)))
      z' = assocLR $ assocLR z   -- embed from ((i . j1) . j2) . j3 to m . (i . (j1 . (j2 . j3)))
      w = f (var x') (var y') (var z')
  in mapJ2 (assocRL . assocRL) w

lam4' :: (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall j . (Applicative j) => (m :. (i :. j)) (expr d1 a) -> (m :. (i :. j)) (expr d2 b) -> (m :. (i :. j)) (expr d3 c) -> (m :. (i :. j)) (expr d4 d) -> (m :. (i :. j)) (expr d5 e))
    -> (m :. i) (expr ('L d1 ('L d2 ('L d3 ('L d4 d5)))) (a -> b -> c -> d -> e))
lam4' f = lamPT $ \x -> lamPT $ \y -> lamPT $ \z -> lamPT $ \w ->
  let x' = assocLR $ weakenL x -- embed from  i . j1              to m . (i . (j1 . (j2 . (j3 . j4)))
      y' = assocLR $ assocLR $ weakenL y     -- embed from (i . j1) . j2        to m . (i . (j1 . (j2 . j3)))
      z' = assocLR $ assocLR $ assocLR $ weakenL z   -- embed from ((i . j1) . j2) . j3 to m . (i . (j1 . (j2 . j3)))
      w' = assocLR $ assocLR $ assocLR $ w
      u = f (var x') (var y') (var z') (var w')
  in mapJ2 (assocRL . assocRL . assocRL) u



--Expected type: (:.) m (i'       :. j1) (expr d2 b) → (:.) m (i'       :. j1) (expr d3 c) → (:.) m (i'       :. j1) (expr d4 d)
--Actual   type: (:.) m ((i :. j) :. j1) (expr d2 b) → (:.) m ((i :. j) :. j1) (expr d3 c) → (:.) m ((i :. j) :. j1) (expr d4 d)

-- lam*Rec are very simple and make recursive calls
lam2Rec :: forall m i expr d1 d2 d3 a b c . (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall j' j . (Applicative j) => (m :. ((i :. j') :. j)) (expr d1 a) -> (m :. ((i :. j') :. j)) (expr d2 b) -> (m :. ((i :. j') :. j)) (expr d3 c))
    -> (m :. i) (expr ('L d1 ('L d2 d3)) (a -> b -> c))
lam2Rec f = lamPT $ \x -> lam1 $ f (var $ weakenL x)

lam3Rec :: forall m i expr d1 d2 d3 d4 a b c d . (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall i' j' j . (Applicative j, i' ~ (i :. j')) => (m :. (i' :. j)) (expr d1 a) -> (m :. (i' :. j)) (expr d2 b) -> (m :. (i' :. j)) (expr d3 c) -> (m :. (i' :. j)) (expr d4 d))
    -> (m :. i) (expr ('L d1 ('L d2 ('L d3 d4))) (a -> b -> c -> d))
lam3Rec f = lamPT $ \x -> lam2 $ f (var $ weakenL x)

lam4Rec :: forall m i expr d1 d2 d3 d4 d5 a b c d e . (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall i' j' j . (Applicative j, i' ~ (i :. j')) => (m :. (i' :. j)) (expr d1 a) -> (m :. (i' :. j)) (expr d2 b) -> (m :. (i' :. j)) (expr d3 c) -> (m :. (i' :. j)) (expr d4 d) -> (m :. (i' :. j)) (expr d5 e))
    -> (m :. i) (expr ('L d1 ('L d2 ('L d3 ('L d4 d5)))) (a -> b -> c -> d -> e))
lam4Rec f = lamPT $ \x -> lam3 $ f (var $ weakenL x)







weakenR :: (Applicative m,Applicative i,Applicative j) => (m :. i) (repr a) -> (m :. (i :. j)) (repr a)
weakenR = weaken

weakenL :: (Applicative m,Applicative i,Applicative j) => (m :. i) (repr a) -> ((m :. i) :. j) (repr a)
weakenL = liftJ

assocRL :: Functor m => (m :. (i1 :. i2)) a -> ((m :. i1) :. i2) a
assocRL = jassocm2

assocLR :: Functor m => ((m :. i1) :. i2) a -> (m :. (i1 :. i2)) a
assocLR = jassocp2




















-- from TSCore.hs
-- a simpler type is possible if we don't need let-insertion across binders
lamPT :: (Applicative m, AppLiftable i, LambdaD repr) =>
       (forall j. AppLiftable j =>
        (i :. j) (repr da a) -> (m :. (i :. j)) (repr db b))
       -> (m :. i) (repr ('L da db) (a->b))
lamPT f = fmap lamD $ J . fmap unJ . unJ $ f  $ J . pure $ id
















appPT :: (Applicative m, Lambda repr) => m (repr (a->b)) -> m (repr a) -> m (repr b)
appPT f x = app <$> f <*> x


vr :: forall i j m repr a. (Applicative m) =>
      Extends (m :. i) (m :. j) => i (repr a) -> (m :. j) (repr a)
vr = (weakens :: (m :. i) (repr a) -> (m :. j) (repr a)) . var


-- EAC: copied straight from TSCore.hs

-- Composition of two type constructors (kind * -> *)
newtype (i :. j) a = J{unJ:: i (j a)}

instance (Functor i, Functor j) => Functor (i :. j) where
  fmap f (J x) = J $ fmap (fmap f) x

instance (Applicative i, Applicative j) => Applicative (i :. j) where
  pure = J . pure . pure
  J f <*> J x = J $ (<*>) <$> f <*> x

liftJ :: (Applicative m, Applicative i) =>
          m a -> (m :. i) a
liftJ = J . fmap pure

-- A very common operation
mapJ2 :: Functor m => (i a -> j a) -> (m :. i) a -> (m :. j) a
mapJ2 f = J . fmap f . unJ

liftJ2 :: (Applicative m, Applicative i, Applicative j) =>
          (m :. i) a -> (m :. (i :. j)) a
liftJ2 = mapJ2 liftJ




-- EAC: not sure if we need this (also from TSCore.hs):


-- Composition of applicatives, just like any composition, is
-- associative
-- Here are the witnesses

jassocp2 :: Functor m => ((m :. i1) :. i2) a -> (m :. (i1 :. i2)) a
jassocp2 (J (J mi1i2)) = J (fmap J mi1i2)
jassocm2 :: Functor m => (m :. (i1 :. i2)) a -> ((m :. i1) :. i2) a
jassocm2 (J mJi1i2) = J . J $ (fmap unJ mJi1i2)

{- Nicolas Pouillard has commented:
'app_pull' is already known as 'Distributive.distribute' where
'Distributive' is the categorical dual of 'Traversable'.
 Hence 'distribute' is the inverse of 'sequenceA'.
-}

class Applicative j => AppLiftable j where
  app_pull :: Applicative i => i (j a) -> j (i a)

instance AppLiftable Identity where
  app_pull = Identity . fmap runIdentity

instance AppLiftable ((->) e) where
  app_pull ija = \e -> fmap ($ e) ija

-- Like regular Applicative, it is closed under composition

instance (AppLiftable j, AppLiftable k) => AppLiftable (j :. k) where
  app_pull = J . fmap app_pull . app_pull . fmap unJ


class (Applicative m, Applicative n) => Extends m n where
    weakens :: m a -> n a

instance Applicative m => Extends m m where
    weakens = id

-- The following is simple but obviously non-generic.
-- See the Regions paper for the generic, inductive weakening
instance (Applicative m, Applicative i) => Extends m (m :. i) where
    weakens = liftJ


instance (Applicative m, Applicative i, Applicative j) =>
   Extends (m :. i) (m :. (i :. j)) where
    weakens = liftJ2

instance (Applicative m,
          Applicative i,
          Applicative j1,
          Applicative j2) =>
   Extends (m :. i) (m :. ((i :. j1) :. j2)) where
    weakens = liftJ2 . liftJ2

instance (Applicative m,
          Applicative i,
          Applicative j1,
          Applicative j2,
          Applicative j3) =>
   Extends (m :. i) (m :. (((i :. j1) :. j2) :. j3)) where
    weakens = liftJ2 . liftJ2 . liftJ2

instance (Applicative m,
          Applicative i,
          Applicative j1,
          Applicative j2,
          Applicative j3,
          Applicative j4) =>
   Extends (m :. i) (m :. ((((i :. j1) :. j2) :. j3) :. j4)) where
    weakens = liftJ2 . liftJ2 . liftJ2 . liftJ2










-- We use higher-order abstract syntax for abstractions.
-- The body of lam could receive (m :. (i :. j)) (repr a)
-- However, that creates the fatal problem for let-insertion, where
-- m is CPSA w m' and using the variable in a let-expression, as in
--   lam (\x -> resetJ $ lam (\y -> genlet (x +: int 1)))
-- will hence affect the answer-type w of the outer lam.
-- After all, a variable is a value, that is, it is effect-free
-- and must be answer-type polymorphic. Therefore, we use the type
-- for the future-stage (i :. j) (repr a) variable.
-- The explicit environment (i :. j) makes it easy to to weakens,
-- weakening by arbitrary amounts.



-- Make a variable an expression
var :: Applicative m => i (repr a) -> (m :. i) (repr a)
var = J . pure

-- Just a specialization of liftJ2
weaken :: (Applicative m, Applicative i, Applicative j) =>
          (m :. i) (repr a) -> (m :. (i :. j)) (repr a)
weaken = liftJ2