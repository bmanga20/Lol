{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

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
  lamD :: (Applicative m, AppLiftable i) =>
           (forall j. AppLiftable j =>
            (i :. j) (expr da a) -> (m :. (i :. j)) (expr db b))
           -> (m :. i) (expr ('L da db) (a->b))

-- from TSCore.hs
-- a simpler type is possible if we don't need let-insertion across binders
lamPT :: (Applicative m, AppLiftable i, Lambda repr) =>
       (forall j. AppLiftable j =>
        (i :. j) (repr a) -> (m :. (i :. j)) (repr b))
       -> (m :. i) (repr (a->b))
lamPT f = fmap lam $ J . fmap unJ . unJ $ f  $ J . pure $ id

appPT :: (Applicative m, Lambda repr) => m (repr (a->b)) -> m (repr a) -> m (repr b)
appPT f x = app <$> f <*> x





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