{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BangPatterns #-}
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

module FreeScoped.Eager.Foil where

import Data.Bifunctor
import Data.Bifunctor.TH (deriveBifunctor)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Unsafe.Coerce
import System.Exit (exitFailure)
import qualified Util.Syntax.Lambda as LC
import qualified Util.IdInt as IdInt
import qualified Util.Impl as LambdaImpl
import Control.DeepSeq
import GHC.Generics (Generic)

type Id = Int
type RawName = Id
type RawScope = IntSet

data {- kind -} S
  = {- type -} VoidS
  -- | {- type -} Singleton
  -- | {- type -} List

newtype Scope (n :: S) = UnsafeScope RawScope
  deriving newtype NFData
newtype Name (n :: S) = UnsafeName RawName
  deriving newtype (NFData, Eq, Ord)
newtype NameBinder (n :: S) (l :: S) =
  UnsafeNameBinder (Name l)
    deriving newtype (NFData, Eq, Ord)

emptyScope :: Scope VoidS
emptyScope = UnsafeScope IntSet.empty

extendScope :: NameBinder n l -> Scope n -> Scope l
extendScope (UnsafeNameBinder (UnsafeName id)) (UnsafeScope scope) =
  UnsafeScope (IntSet.insert id scope)

rawFreshName :: RawScope -> RawName
rawFreshName scope | IntSet.null scope = 0
                   | otherwise = IntSet.findMax scope + 1

withFreshBinder
  :: Scope n
  -> (forall l. NameBinder n l -> r)
  -> r
withFreshBinder (UnsafeScope scope) cont =
  cont binder
  where
    binder = UnsafeNameBinder (UnsafeName (rawFreshName scope))

unsafeEquals :: NameBinder n l -> NameBinder n1 l1 -> Bool
unsafeEquals (UnsafeNameBinder (UnsafeName name1)) (UnsafeNameBinder (UnsafeName name2)) = name1 == name2

unsafeLess :: NameBinder n l -> NameBinder n1 l1 -> Bool
unsafeLess (UnsafeNameBinder (UnsafeName name1)) (UnsafeNameBinder (UnsafeName name2)) = name1 < name2

nameOf :: NameBinder n l -> Name l
nameOf (UnsafeNameBinder name) = name

rawMember :: RawName -> RawScope -> Bool
rawMember i s = IntSet.member i s

member :: Name l -> Scope n -> Bool
member (UnsafeName name) (UnsafeScope s) = rawMember name s

data Expr n where
  VarE :: {-# UNPACK #-} !(Name n) -> Expr n
  AppE :: Expr n -> Expr n -> Expr n
  LamE :: !(NameBinder n l) -> Expr l -> Expr n

instance Eq (Expr n) where
  VarE x == VarE y = x == y
  AppE f1 x1 == AppE f2 x2 = (f1 == f2) && (x1 == x2)
  LamE x1 body1 == LamE x2 body2 = (x1 == unsafeCoerce x2) && (unsafeCoerce body1 == body2)
  _ == _ = False

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
  | IntSet.member id rawScope = withFresh scope cont
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
newtype Substitution (sig :: * -> * -> *) (i :: S) (o :: S) =
  UnsafeSubstitution (IntMap (AST sig o))

lookupSubst :: Substitution sig i o -> Name i -> AST sig o
lookupSubst (UnsafeSubstitution env) (UnsafeName id) =
    case IntMap.lookup id env of
        Just ex -> ex
        Nothing -> Var (UnsafeName id)

identitySubst :: Substitution e i i
identitySubst = UnsafeSubstitution IntMap.empty

addSubst :: Substitution sig i o -> NameBinder i i' -> AST sig o -> Substitution sig i' o
addSubst (UnsafeSubstitution env) (UnsafeNameBinder (UnsafeName id)) ex = UnsafeSubstitution (IntMap.insert id ex env)

addRename :: Substitution sig i o -> NameBinder i i' -> Name o -> Substitution sig i' o
addRename s@(UnsafeSubstitution env) b@(UnsafeNameBinder (UnsafeName name1)) n@(UnsafeName name2)
    | name1 == name2 = UnsafeSubstitution (IntMap.delete name1 env)
    | otherwise = addSubst s b (Var n)

instance Bifunctor sig => Sinkable (Substitution sig i) where
  sinkabilityProof rename (UnsafeSubstitution env) =
    UnsafeSubstitution (fmap (sinkabilityProof rename) env)

data ScopedAST sig n where
  ScopedAST :: !(NameBinder n l) -> !(AST sig l) -> ScopedAST sig n

instance (forall l. NFData (AST sig l)) => NFData (ScopedAST sig n) where
  rnf (ScopedAST binder body) = rnf binder `seq` rnf body

data AST sig n where
  Var :: {-# UNPACK #-} !(Name n) -> AST sig n
  Node :: {-# UNPACK #-} (sig (ScopedAST sig n) (AST sig n)) -> AST sig n

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
  -> Substitution sig i o
  -> AST sig i
  -> AST sig o
substitute !scope !subst = \case
  Var name -> lookupSubst subst name
  Node node -> Node $! (bimap f (substitute scope subst) node)
  where
    f !(ScopedAST binder body) =
      withRefreshed scope (nameOf binder) $ \binder' ->
        let !subst' = addRename (sink subst) binder (nameOf binder')
            !scope' = extendScope binder' scope
            !body' = substitute scope' subst' body
        in ScopedAST binder' body'

data LambdaPiF scope term
  = AppF !term !term
  | LamF !scope
  | PiF !term !scope
  deriving (Eq, Show, Functor, NFData, Generic)
deriveBifunctor ''LambdaPiF

type LambdaPi n = AST LambdaPiF n

pattern App :: LambdaPi n -> LambdaPi n -> LambdaPi n
pattern App fun arg = Node (AppF fun arg)

pattern Lam :: NameBinder n l -> LambdaPi l -> LambdaPi n
pattern Lam binder body = Node (LamF (ScopedAST binder body))

{-# COMPLETE Var, App, Lam #-}

instance Eq (LambdaPi n) where
  Var x == Var y = x == y
  App f1 x1 == App f2 x2 = (f1 == f2) && (x1 == x2)
  Lam x1 body1 == Lam x2 body2 = (x1 == unsafeCoerce x2) && (unsafeCoerce body1 == body2)
  _ == _ = False

whnf :: Distinct n => Scope n -> LambdaPi n -> LambdaPi n
whnf !scope = \case
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let !subst =  addSubst identitySubst binder arg
        in whnf scope $! (substitute scope subst body)
      fun' -> App fun' arg
  t -> t

nf :: Distinct n => Scope n -> LambdaPi n -> LambdaPi n
nf !scope = \case
  Lam binder body -> unsafeAssertFresh binder \binder' ->
          let !scope' = extendScope binder' scope
        in Lam binder' $! (nf scope' body)
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let !subst = addSubst identitySubst binder arg
        in nf scope $! (substitute scope subst body)
      fun' -> (App $! (nf scope fun')) $! (nf scope arg)
  t -> t

nfd :: LambdaPi VoidS -> LambdaPi VoidS
nfd term = nf emptyScope term

toLambdaPi :: Distinct n => Scope n -> IntMap (Name n) -> LC.LC IdInt.IdInt -> LambdaPi n
toLambdaPi scope env = \case
  LC.Var (IdInt.IdInt x) ->
    case IntMap.lookup x env of
      Just name -> Var name
      Nothing -> error ("unbound variable: " ++ show x)

  LC.App fun arg ->
    App (toLambdaPi scope env fun) (toLambdaPi scope env arg)

  LC.Lam (IdInt.IdInt x) body -> withFresh scope $ \binder ->
    let scope' = extendScope binder scope
        env' = IntMap.insert x (nameOf binder) (sink <$> env)
    in Lam binder (toLambdaPi scope' env' body)

captureLc :: LC.LC IdInt.IdInt
captureLc = LC.App (LC.Lam (IdInt.IdInt 1) (LC.Lam (IdInt.IdInt 2) (LC.App (LC.Var (IdInt.IdInt 2)) (LC.Var (IdInt.IdInt 1))))) (LC.Lam (IdInt.IdInt 2) (LC.Lam (IdInt.IdInt 1) (LC.App (LC.Var (IdInt.IdInt 1)) (LC.Var (IdInt.IdInt 2)))))

appCaptue :: LC.LC IdInt.IdInt
appCaptue = LC.App captureLc (LC.Lam (IdInt.IdInt 1) (LC.Var (IdInt.IdInt 1)))

appCaptue2 :: LC.LC IdInt.IdInt
appCaptue2 = LC.App (toLC (whnf emptyScope (fromLC captureLc))) (LC.Lam (IdInt.IdInt 1) (LC.Var (IdInt.IdInt 1)))

fromLC :: LC.LC IdInt.IdInt -> LambdaPi VoidS
fromLC term = toLambdaPi emptyScope IntMap.empty term

fromLambdaPi :: LambdaPi n -> LC.LC IdInt.IdInt
fromLambdaPi = \case
  Var (UnsafeName id) -> LC.Var (IdInt.IdInt id)
  App fun arg -> LC.App (fromLambdaPi fun) (fromLambdaPi arg)
  Lam binder body ->
    let UnsafeName id = nameOf binder
    in LC.Lam (IdInt.IdInt id) (fromLambdaPi body)

toLC :: LambdaPi n -> LC.LC IdInt.IdInt
toLC = fromLambdaPi


-- Unsafe renaming of a raw name
unsafeRenameVar :: IntMap RawName -> RawName -> RawName
unsafeRenameVar subst name1 = case IntMap.lookup name1 subst of
  Just name2 -> name2
  Nothing -> name1

-- unsafe implementation of aeq for LambdaPi terms which ignores foil invariants
unsafeAeq
  :: IntMap RawName
  -> IntMap RawName
  -> IntSet
  -> IntSet
  -> LambdaPi n
  -> LambdaPi l
  -> Bool
unsafeAeq subst1 subst2 target1 target2 (Var (UnsafeName x)) (Var (UnsafeName y))
  | IntSet.member x target1 = False
  | IntSet.member y target2 = False
  | otherwise = (unsafeRenameVar subst1 x) == (unsafeRenameVar subst2 y)
unsafeAeq subst1 subst2 target1 target2 (App fun1 arg1) (App fun2 arg2)
  = and
    [ unsafeAeq subst1 subst2 target1 target2 fun1 fun2
    , unsafeAeq subst1 subst2 target1 target2 arg1 arg2 ]
unsafeAeq subst1 subst2 target1 target2
  (Lam binder1@(UnsafeNameBinder (UnsafeName name1)) body1)
  (Lam binder2@(UnsafeNameBinder (UnsafeName name2)) body2)
  | unsafeEquals binder1 binder2 = unsafeAeq subst1 subst2 target1 target2 body1 body2
  | unsafeLess binder1 binder2 =
        let subst2' = IntMap.insert name2 name1 subst2
            target2' = IntSet.insert name1 target2
        in unsafeAeq subst1 subst2' target1 target2' body1 body2
  | otherwise =
        let (UnsafeName name1) = nameOf binder1
            subst1' = IntMap.insert name1 name2 subst1
            target1' = IntSet.insert name2 target1
        in unsafeAeq subst1' subst2 target1' target2 body1 body2
unsafeAeq _ _ _ _ _ _ = False

-- aeq
--   :: Renaming n     -- ^
--   -> Renaming n     -- ^
--   -> Scope n        -- ^
--   -> Scope n        -- ^
--   -> LambdaPi n     -- ^
--   -> LambdaPi n     -- ^
--   -> Bool
-- aeq subst1 subst2 target1 target2 (Var x) (Var y)
--   | member x target1 = False
--   | member y target2 = False
--   | otherwise = (renameVar subst1 x) == (renameVar subst2 y)
-- aeq subst1 subst2 target1 target2 (App fun1 arg1) (App fun2 arg2)
--   = and
--     [ aeq subst1 subst2 target1 target2 fun1 fun2
--     , aeq subst1 subst2 target1 target2 arg1 arg2 ]
-- aeq subst1 subst2 target1 target2 (Lam binder1 body1) (Lam binder2 body2)
--   | unsafeEquals binder1 binder2 = aeq (sink subst1) (sink subst2) (sink target1) (sink target2) body1 (sink body2)
--   | unsafeLess binder1 binder2 = unsafeAssertFresh binder1 \binder1New ->
--     let (UnsafeName name2) = nameOf binder2
--         (Renaming env2) = sink subst2
--         subst2' = Renaming (IntMap.insert name2 (nameOf binder1New) env2)
--         target2' = extendScope binder1New target2
--           in aeq (sink subst1) (sink subst2') (sink target1) target2' body1 (sink body2)
--   | otherwise = unsafeAssertFresh binder2 \binder2New ->
--     let (UnsafeName name1) = nameOf binder1
--         (Renaming env1) = sink subst1
--         subst1' = Renaming (IntMap.insert name1 (nameOf binder2New) env1)
--         target1' = extendScope binder2New target1
--           in aeq (sink subst1') (sink subst2) target1' (sink target2) (sink body1) body2
-- aeq _ _ _ _ _ _ = False

aeq_impl :: LambdaPi n -> LambdaPi n -> Bool
aeq_impl = (==)

impl :: LambdaImpl.LambdaImpl
impl =
  LambdaImpl.LambdaImpl
    { LambdaImpl.impl_name = "FreeScoped.Eager.Foil",
      LambdaImpl.impl_fromLC = fromLC,
      LambdaImpl.impl_toLC = toLC,
      LambdaImpl.impl_nf = nfd,
      LambdaImpl.impl_nfi = error "nfi unimplemented",
      LambdaImpl.impl_aeq = aeq_impl
    }
