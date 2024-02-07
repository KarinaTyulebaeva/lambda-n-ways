{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}

module FreeScoped.Nested where

import Data.Bifunctor
import Data.Bifunctor.TH (deriveBifunctor)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Unsafe.Coerce
import System.Exit (exitFailure)
import qualified Util.Syntax.Lambda as LC
import qualified Util.IdInt as IdInt
import qualified Util.Impl as LambdaImpl
import Control.DeepSeq
import GHC.Generics (Generic)


-- Term Functor (generating functor)
-- TermF
data TermNode scope term
  = AppNode term term
  | LamNode scope
  deriving (Show, Generic, NFData, Eq)
$(deriveBifunctor ''TermNode)

-- Free Scoped monads
-- data FS
data AST node var
  = VarT var
  | NodeT (node (AST node (Maybe var)) (AST node var))


deriving instance (forall scope term. (Show scope, Show term) => Show (node scope term), Show var) => Show (AST node var)

deriving instance (forall scope term. (Eq scope, Eq term) => Eq (node scope term), Eq var) => Eq (AST node var)
deriving instance (forall scope term. (Generic scope, Generic term) => Generic (node scope term)) => Generic (AST node n)
deriving instance (forall scope term. (NFData scope, NFData term) => NFData (node scope term), NFData var, forall scope term. (Generic scope, Generic term) => Generic (node scope term)) => NFData (AST node var)


type Term var = AST TermNode var

pattern VarP x = VarT x
pattern LamP s = NodeT (LamNode s)
pattern AppP t1 t2 = NodeT (AppNode t1 t2)

mapMaybe :: (a -> b) -> Maybe a -> Maybe b
mapMaybe _f Nothing = Nothing
mapMaybe f (Just x) = Just (f x)

mapAST :: Bifunctor t => (a -> b) -> AST t a -> AST t b
mapAST f (VarT x) = VarT (f x)
mapAST f (NodeT t) = NodeT (bimap (mapAST (mapMaybe f)) (mapAST f) t)

instance Bifunctor t => Functor (AST t) where
  fmap = mapAST

expandMaybeF :: Bifunctor t =>  Maybe (AST t a) ->  AST t (Maybe a)
expandMaybeF Nothing = VarT Nothing
expandMaybeF (Just a) = mapAST Just a

expandScope :: Bifunctor t => (var -> AST t var')
  -> Maybe var
  -> AST t (Maybe var')
expandScope _f Nothing = expandMaybeF Nothing
expandScope f (Just c) = expandMaybeF (Just (f c))

expandVarsF
  :: Bifunctor t
  => (var -> AST t var')
  -> AST t var
  -> AST t var'
expandVarsF f (VarT x) = f x
expandVarsF f (NodeT t) = NodeT (bimap ((expandVarsF (expandScope f))) (expandVarsF f) t)

substituteF
  :: Bifunctor node =>
  AST node var -> AST node (Maybe var) -> AST node var
substituteF arg term = expandVarsF f term where
    f Nothing = arg
    f (Just y) = VarP y

whnf :: Term var -> Term var
whnf e@(VarP _) = e
whnf e@(LamP _) = e
whnf (AppP func arg) =
  case whnf func of
    LamP b -> whnf (substituteF arg b)
    f' -> AppP f' arg

nfd :: Term var -> Term var
nfd e@(VarP _) = e
nfd (LamP body) = LamP (nfd body)
nfd (AppP func arg) =
  case whnf func of
    LamP b -> nfd (substituteF arg b)
    f' -> AppP (nfd f') (nfd arg)

abstract :: Eq var => var -> AST TermNode var -> AST TermNode var
abstract x = LamP . mapAST (match x) where
    match x y = if (x == y) then Nothing else Just y

fromLC :: LC.LC IdInt.IdInt -> Term Int
fromLC = \case
  LC.Var (IdInt.IdInt x) -> VarP x
  LC.App fun arg -> AppP (fromLC fun) (fromLC arg)
  LC.Lam (IdInt.IdInt x) body -> abstract x (fromLC body)

toLC :: Term Int -> LC.LC IdInt.IdInt
toLC = from 0
    where
        from :: Int ->  Term Int -> LC.LC IdInt.IdInt
        from _ (VarP x) = LC.Var (IdInt.IdInt x)
        from n (AppP fun arg) = LC.App (from n fun) (from n arg)
        from n (LamP body) = LC.Lam (IdInt.IdInt n) (from (succ n) (substituteF (VarP n) body))

impl :: LambdaImpl.LambdaImpl
impl =
  LambdaImpl.LambdaImpl
    { LambdaImpl.impl_name = "FreeScoped.NestedDeBrujn",
      LambdaImpl.impl_fromLC = fromLC,
      LambdaImpl.impl_toLC = toLC,
      LambdaImpl.impl_nf = nfd,
      LambdaImpl.impl_nfi = error "nfi unimplemented",
      LambdaImpl.impl_aeq = (==)
    }