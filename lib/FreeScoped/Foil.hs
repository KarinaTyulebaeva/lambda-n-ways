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

module FreeScoped.Foil where

import Data.Bifunctor
import Data.Bifunctor.TH (deriveBifunctor)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.IntSet as Set
import Unsafe.Coerce
import System.Exit (exitFailure)
import qualified Util.Syntax.Lambda as LC
import qualified Util.IdInt as IdInt
import qualified Util.Impl as LambdaImpl
import Control.DeepSeq
import GHC.Generics (Generic)

type Id = Int
type RawName = Id
type RawScope = Set.IntSet

data {- kind -} S
  = {- type -} VoidS
  -- | {- type -} Singleton
  -- | {- type -} List

newtype Scope (n :: S) = UnsafeScope RawScope
  deriving newtype NFData
newtype Name (n :: S) = UnsafeName RawName
  deriving newtype NFData
newtype NameBinder (n :: S) (l :: S) =
  UnsafeNameBinder (Name l)
    deriving newtype NFData

emptyScope :: Scope VoidS
emptyScope = UnsafeScope Set.empty

extendScope :: NameBinder n l -> Scope n -> Scope l
extendScope (UnsafeNameBinder (UnsafeName id)) (UnsafeScope scope) =
  UnsafeScope (Set.insert id scope)

rawFreshName :: RawScope -> RawName
rawFreshName scope | Set.null scope = 0
                   | otherwise = Set.findMax scope + 1

withFreshBinder
  :: Scope n
  -> (forall l. NameBinder n l -> r)
  -> r
withFreshBinder (UnsafeScope scope) cont =
  cont binder
  where
    binder = UnsafeNameBinder (UnsafeName (rawFreshName scope))

nameOf :: NameBinder n l -> Name l
nameOf (UnsafeNameBinder name) = name

rawMember :: RawName -> RawScope -> Bool
rawMember i s = Set.member i s

member :: Name l -> Scope n -> Bool
member (UnsafeName name) (UnsafeScope s) = rawMember name s

data Expr n where
  VarE :: Name n -> Expr n
  AppE :: Expr n -> Expr n -> Expr n
  LamE :: NameBinder n l -> Expr l -> Expr n

-- Distinct constraints
class ExtEndo (n :: S)

class (ExtEndo n => ExtEndo l ) => Ext (n:: S) (l :: S)
instance ( ExtEndo n => ExtEndo l ) => Ext n l

class Distinct (n :: S)
instance Distinct VoidS

type DExt n l = (Distinct l, Ext n l)

-- Safer scopes with distinct constraints
data DistinctEvidence ( n :: S) where
  Distinct :: Distinct n => DistinctEvidence n

unsafeDistinct :: DistinctEvidence n
unsafeDistinct = unsafeCoerce (Distinct :: DistinctEvidence VoidS)

data ExtEvidence ( n:: S) ( l :: S) where
  Ext :: Ext n l => ExtEvidence n l

unsafeExt :: ExtEvidence n l
unsafeExt = unsafeCoerce (Ext :: ExtEvidence VoidS VoidS)

withFresh :: Distinct n => Scope n
  -> (forall l . DExt n l => NameBinder n l -> r ) -> r
withFresh scope cont = withFreshBinder scope (\binder ->
  unsafeAssertFresh binder cont)

unsafeAssertFresh :: forall n l n' l' r. NameBinder n l
  -> (DExt n' l' => NameBinder n' l' -> r) -> r
unsafeAssertFresh binder cont =
  case unsafeDistinct @l' of
    Distinct -> case unsafeExt @n' @l' of
      Ext -> cont (unsafeCoerce binder)

withRefreshed :: Distinct o => Scope o -> Name i
  -> (forall o'. DExt o o' => NameBinder o o' -> r) -> r
withRefreshed scope@(UnsafeScope rawScope) name@(UnsafeName id) cont
  | Set.member id rawScope = withFresh scope cont
  | otherwise = unsafeAssertFresh (UnsafeNameBinder name) cont

-- generic sinking
concreteSink :: DExt n l => Expr n -> Expr l
concreteSink = unsafeCoerce

class Sinkable (e :: S -> *) where
  sinkabilityProof :: (Name n -> Name l) -> e n -> e l

instance Sinkable Name where
  sinkabilityProof rename = rename

sink :: (Sinkable e, DExt n l) => e n -> e l
sink = unsafeCoerce

instance Sinkable Expr where
  sinkabilityProof rename (VarE v) = VarE (rename v)
  sinkabilityProof rename (AppE f e) = AppE (sinkabilityProof rename f) (sinkabilityProof rename e)
  sinkabilityProof rename (LamE binder body) = extendRenaming rename binder \rename' binder' ->
    LamE binder' (sinkabilityProof rename' body)

extendRenaming :: (Name n -> Name n') -> NameBinder n l
  -> (forall l'. (Name l -> Name l') -> NameBinder n' l' -> r ) -> r
extendRenaming _ (UnsafeNameBinder name) cont =
  cont unsafeCoerce (UnsafeNameBinder name)

-- Substitution
data Substitution (e :: S -> *) (i :: S) (o :: S) =
  UnsafeSubstitution (forall n. Name n -> e n) (Map Int (e o))

lookupSubst :: Substitution e i o -> Name i -> e o
lookupSubst (UnsafeSubstitution f env) (UnsafeName id) =
    case Map.lookup id env of
        Just ex -> ex
        Nothing -> f (UnsafeName id)

identitySubst :: (forall n. Name n -> e n) -> Substitution e i i
identitySubst f = UnsafeSubstitution f Map.empty

addSubst :: Substitution e i o -> NameBinder i i' -> e o -> Substitution e i' o
addSubst (UnsafeSubstitution f env) (UnsafeNameBinder (UnsafeName id)) ex = UnsafeSubstitution f (Map.insert id ex env)

addRename :: Substitution e i o -> NameBinder i i' -> Name o -> Substitution e i' o
addRename s@(UnsafeSubstitution f env) b@(UnsafeNameBinder (UnsafeName name1)) n@(UnsafeName name2)
    | name1 == name2 = UnsafeSubstitution f env
    | otherwise = addSubst s b (f n)

instance (Sinkable e) => Sinkable (Substitution e i) where
  sinkabilityProof rename (UnsafeSubstitution f env) =
    UnsafeSubstitution f (fmap (sinkabilityProof rename) env)

data ScopedAST sig n where
  ScopedAST :: NameBinder n l -> AST sig l -> ScopedAST sig n

instance (forall l. NFData (AST sig l)) => NFData (ScopedAST sig n) where
  rnf (ScopedAST binder body) = rnf binder `seq` rnf body

data AST sig n where
  Var :: Name n -> AST sig n
  Node :: sig (ScopedAST sig n) (AST sig n) -> AST sig n

deriving instance (forall scope term. (Generic scope, Generic term) => Generic (sig scope term)) => Generic (AST sig n)
deriving instance (forall scope term. (NFData scope, NFData term) => NFData (sig scope term), forall scope term. (Generic scope, Generic term) => Generic (sig scope term)) => NFData (AST sig n)

instance Bifunctor sig => Sinkable (AST sig) where
  -- sinkabilityProof :: (Name n -> Name l) -> AST sig n -> AST sig l
  sinkabilityProof rename = \case
    Var name -> Var (rename name)
    Node node -> Node (bimap f (sinkabilityProof rename) node)
    where
      f (ScopedAST binder body) =
        extendRenaming rename binder $ \rename' binder' ->
          ScopedAST binder' (sinkabilityProof rename' body)

substitute
  :: (Bifunctor sig, Distinct o)
  => Scope o
  -> Substitution (AST sig) i o
  -> AST sig i
  -> AST sig o
substitute scope subst = \case
  Var name -> lookupSubst subst name
  Node node -> Node (bimap f (substitute scope subst) node)
  where
    f (ScopedAST binder body) =
      withRefreshed scope (nameOf binder) $ \binder' ->
        let subst' = addRename (sink subst) binder (nameOf binder')
            scope' = extendScope binder' scope
            body' = substitute scope' subst' body
        in ScopedAST binder' body'

data LambdaPiF scope term
  = AppF term term
  | LamF scope
  | PiF term scope
  deriving (Eq, Show, Functor, NFData, Generic)
deriveBifunctor ''LambdaPiF

type LambdaPi n = AST LambdaPiF n

pattern App :: LambdaPi n -> LambdaPi n -> LambdaPi n
pattern App fun arg = Node (AppF fun arg)

pattern Lam :: NameBinder n l -> LambdaPi l -> LambdaPi n
pattern Lam binder body = Node (LamF (ScopedAST binder body))

{-# COMPLETE Var, App, Lam #-}

whnf :: Distinct n => Scope n -> LambdaPi n -> LambdaPi n
whnf scope = \case
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let subst =  addSubst (identitySubst Var) binder arg
        in whnf scope (substitute scope subst body)
      fun' -> App fun' arg
  t -> t

nf :: Distinct n => Scope n -> LambdaPi n -> LambdaPi n
nf scope = \case
  Lam binder body -> unsafeAssertFresh binder \binder' ->
          let scope' = extendScope binder' scope
        in Lam binder' (nf scope' body)
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let subst =  addSubst (identitySubst Var) binder arg
        in nf scope (substitute scope subst body)
      fun' -> App (nf scope fun') (nf scope arg)
  t -> t

nfd :: LambdaPi VoidS -> LambdaPi VoidS
nfd term = nf emptyScope term

toLambdaPi :: Distinct n => Scope n -> Map Int (Name n) -> LC.LC IdInt.IdInt -> LambdaPi n
toLambdaPi scope env = \case
  LC.Var (IdInt.IdInt x) ->
    case Map.lookup x env of
      Just name -> Var name
      Nothing -> error ("unbound variable: " ++ show x)

  LC.App fun arg ->
    App (toLambdaPi scope env fun) (toLambdaPi scope env arg)

  LC.Lam (IdInt.IdInt x) body -> withFresh scope $ \binder ->
    let scope' = extendScope binder scope
        env' = Map.insert x (nameOf binder) (sink <$> env)
    in Lam binder (toLambdaPi scope' env' body)

fromLC :: LC.LC IdInt.IdInt -> LambdaPi VoidS
fromLC term = toLambdaPi emptyScope Map.empty term

fromLambdaPi :: LambdaPi n -> LC.LC IdInt.IdInt
fromLambdaPi = \case
  Var (UnsafeName id) -> LC.Var (IdInt.IdInt id)
  App fun arg -> LC.App (fromLambdaPi fun) (fromLambdaPi arg)
  Lam binder body ->
    let UnsafeName id = nameOf binder
    in LC.Lam (IdInt.IdInt id) (fromLambdaPi body)

two :: LambdaPi VoidS
two = withFresh emptyScope
  (\ s -> Lam s $ withFresh (extendScope s emptyScope)
    (\ z -> Lam z (App (Var (sink (nameOf s)))
                        (App (Var (sink (nameOf s)))
                             (Var (nameOf z))))))

appTwo = App two two


toLC :: LambdaPi n -> LC.LC IdInt.IdInt
toLC = fromLambdaPi

impl :: LambdaImpl.LambdaImpl
impl =
  LambdaImpl.LambdaImpl
    { LambdaImpl.impl_name = "FreeScoped.Foil",
      LambdaImpl.impl_fromLC = fromLC,
      LambdaImpl.impl_toLC = toLC,
      LambdaImpl.impl_nf = nfd,
      LambdaImpl.impl_nfi = error "nfi unimplemented",
      LambdaImpl.impl_aeq = error "aeq unimplemented"
    }
