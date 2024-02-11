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
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PatternGuards #-}

module Foil.Foil where

import Data.Map (Map)
import qualified Data.Map as Map
import Unsafe.Coerce
import System.Exit (exitFailure)
import qualified Util.Syntax.Lambda as LC
import qualified Util.IdInt as IdInt
import qualified Util.Impl as LambdaImpl
import Data.IntMap
import qualified Data.IntMap as IntMap
import Control.DeepSeq
import GHC.Generics (Generic)
import Data.IntSet
import qualified Data.IntSet as IntSet
import qualified Data.Maybe

type Id = Int
type Label = String
type RawName = (Id, Label)
type RawScope = Map Int Label

data {- kind -} S
  = {- type -} VoidS
  -- | {- type -} Singleton
  -- | {- type -} List

data Scope (n :: S) = UnsafeScope RawScope
  deriving (Generic, NFData)
data Name (n :: S) = UnsafeName RawName
    deriving (Generic, NFData)
data NameBinder (n :: S) (l :: S) =
  UnsafeNameBinder (Name l)
    deriving (Generic, NFData)

ppName :: Name n -> Label
ppName (UnsafeName (id, name)) = name

emptyScope :: Scope VoidS
emptyScope = UnsafeScope Map.empty

extendScope :: NameBinder n l -> Scope n -> Scope l
extendScope (UnsafeNameBinder (UnsafeName (id, name))) (UnsafeScope scope) =
  UnsafeScope (Map.insert id name scope)

rawFreshName :: RawScope -> Label -> RawName
rawFreshName scope labelToBind | Map.null scope = (0, labelToBind ++ show 0)
                               | otherwise =
                                  let (maxId, _) = Map.findMax scope
                                    in (maxId + 1, labelToBind ++ show (maxId + 1))

withFreshBinder
  :: Scope n
  -> Label
  -> (forall l. NameBinder n l -> r)
  -> r
withFreshBinder (UnsafeScope scope) labelToBind cont =
  cont binder
  where
    binder = UnsafeNameBinder (UnsafeName (rawFreshName scope labelToBind))

nameOf :: NameBinder n l -> Name l
nameOf (UnsafeNameBinder name) = name

idOf :: Name l -> Id
idOf (UnsafeName (id, _)) = id

rawMember :: RawName -> RawScope -> Bool
rawMember (i, x) s = Map.member i s

member :: Name l -> Scope n -> Bool
member (UnsafeName name) (UnsafeScope s) = rawMember name s

data Expr n where
  VarE :: Name n -> Expr n
  AppE :: Expr n -> Expr n -> Expr n
  LamE :: NameBinder n l -> Expr l -> Expr n


instance (forall l. NFData (Expr l)) where
  rnf (LamE binder body) = rnf binder `seq` rnf body
  rnf (AppE fun arg) = rnf fun `seq` rnf arg
  rnf (VarE name) = rnf name

-- >>> putStrLn $ ppExpr identity
-- λx1. x1
-- >>> putStrLn $ ppExpr two
-- λx1. λx2. x1(x1(x2))
ppExpr :: Expr n -> String
ppExpr expr = case expr of
  VarE name -> ppName name
  AppE e1 e2 -> ppExpr e1 ++ "(" ++ ppExpr e2 ++ ")"
  LamE x body -> "λ" ++ ppName (nameOf x) ++ ". " ++ ppExpr body


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

withFresh :: Distinct n => Scope n -> Label
  -> (forall l . DExt n l => NameBinder n l -> r ) -> r
withFresh scope labelToBind cont = withFreshBinder scope labelToBind (\binder ->
  unsafeAssertFresh binder cont)

unsafeAssertFresh :: forall n l n' l' r. NameBinder n l
  -> (DExt n' l' => NameBinder n' l' -> r) -> r
unsafeAssertFresh binder cont =
  case unsafeDistinct @l' of
    -- #FIXME: when using originally @l' and @n' gives an error about type variables not in scope
    Distinct -> case unsafeExt @n' @l' of
      Ext -> cont (unsafeCoerce binder)

withRefreshed :: Distinct o => Scope o -> Name i
  -> (forall o'. DExt o o' => NameBinder o o' -> r) -> r
withRefreshed scope@(UnsafeScope scopemap) name@(UnsafeName (id, x)) cont =
  case Map.lookup id scopemap of
     Just label -> withFresh scope label cont
     Nothing -> unsafeAssertFresh (UnsafeNameBinder name) cont

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
  UnsafeSubstitution (forall n. Name n -> e n) (IntMap (e o))

lookupSubst :: Substitution e i o -> Name i -> e o
lookupSubst (UnsafeSubstitution f env) (UnsafeName (id, label)) =
    case IntMap.lookup id env of
        Just ex -> ex
        Nothing -> f (UnsafeName (id, label))

identitySubst :: (forall n. Name n -> e n) -> Substitution e i i
identitySubst f = UnsafeSubstitution f IntMap.empty

addSubst :: Substitution e i o -> NameBinder i i' -> e o -> Substitution e i' o
addSubst (UnsafeSubstitution f env) (UnsafeNameBinder (UnsafeName (id, label))) ex = UnsafeSubstitution f (IntMap.insert id ex env)

addRename :: Substitution e i o -> NameBinder i i' -> Name o -> Substitution e i' o
addRename s@(UnsafeSubstitution f env) b@(UnsafeNameBinder (UnsafeName name1)) n@(UnsafeName name2)
    | name1 == name2 = UnsafeSubstitution f (IntMap.delete (fst name1) env)
    | otherwise = addSubst s b (f n)

instance (Sinkable e) => Sinkable (Substitution e i) where
  sinkabilityProof rename (UnsafeSubstitution f env) =
    UnsafeSubstitution f (fmap (sinkabilityProof rename) env)


-- Substitute part
substitute :: Distinct o => Scope o -> Substitution Expr i o -> Expr i -> Expr o
substitute scope subst = \case
    VarE name -> lookupSubst subst name
    AppE f x -> AppE (substitute scope subst f) (substitute scope subst x)
    LamE binder body -> withRefreshed scope (nameOf binder) (\binder' ->
        let subst' = addRename (sink subst) binder (nameOf binder')
            scope' = extendScope binder' scope
            body' = substitute scope' subst' body in LamE binder' body'
        )

whnf :: Distinct n => Scope n -> Expr n -> Expr n
whnf scope = \case
  AppE fun arg ->
    case whnf scope fun of
      LamE binder body ->
        let subst =  addSubst (identitySubst VarE) binder arg
        in whnf scope (substitute scope subst body)
      fun' -> AppE fun' arg
  t -> t

nf :: Distinct n => Scope n -> Expr n -> Expr n
nf scope expr = case expr of
  LamE binder body -> unsafeAssertFresh binder \binder' ->
          let scope' = extendScope binder' scope
        in LamE binder' (nf scope' body)
  AppE fun arg ->
    case whnf scope fun of
      LamE binder body ->
        let subst =  addSubst (identitySubst VarE ) binder arg
        in nf scope (substitute scope subst body)
      fun' -> AppE (nf scope fun') (nf scope arg)
  t -> t

nfd :: Expr VoidS -> Expr VoidS
nfd = nf emptyScope

toLambdaPi :: Distinct n => Scope n -> IntMap (Name n) -> LC.LC IdInt.IdInt -> Expr n
toLambdaPi scope env = \case
  LC.Var (IdInt.IdInt x) ->
    case IntMap.lookup x env of
      Just name -> VarE name
      Nothing -> error ("unbound variable: " ++ show x)
  LC.App fun arg ->
    AppE (toLambdaPi scope env fun) (toLambdaPi scope env arg)

  LC.Lam (IdInt.IdInt x) body -> withFresh scope "aa" $ \binder ->
    let scope' = extendScope binder scope
        env' = IntMap.insert x (nameOf binder) (sink <$> env)
    in LamE binder (toLambdaPi scope' env' body) 
        


fromLC :: LC.LC IdInt.IdInt -> Expr VoidS
fromLC = toLambdaPi emptyScope IntMap.empty

toLC :: Expr n -> LC.LC IdInt.IdInt
toLC = \case
    VarE (UnsafeName (x, label)) -> LC.Var (IdInt.IdInt x)
    AppE fun arg -> LC.App (toLC fun) (toLC arg)
    LamE binder body ->
      let UnsafeName (id, label) = nameOf binder
      in LC.Lam (IdInt.IdInt id) (toLC body)

unsafeEquals :: NameBinder n l -> NameBinder n1 l1 -> Bool
unsafeEquals (UnsafeNameBinder (UnsafeName name1)) (UnsafeNameBinder (UnsafeName name2)) = name1 == name2

unsafeLess :: NameBinder n l -> NameBinder n1 l1 -> Bool
unsafeLess (UnsafeNameBinder (UnsafeName name1)) (UnsafeNameBinder (UnsafeName name2)) = name1 < name2

unsafeRenameVar :: IntMap RawName -> RawName -> RawName
unsafeRenameVar subst (id, label) = Data.Maybe.fromMaybe (id, label) (IntMap.lookup id subst)

unsafeAeq
  :: IntMap RawName
  -> IntMap RawName
  -> IntSet
  -> IntSet
  -> Expr n
  -> Expr l
  -> Bool
unsafeAeq subst1 subst2 target1 target2 (VarE (UnsafeName (x, label))) (VarE (UnsafeName (y, label2)))
  | IntSet.member x target1 = False
  | IntSet.member y target2 = False
  | otherwise = unsafeRenameVar subst1 (x, label) == unsafeRenameVar subst2 (y, label2)
unsafeAeq subst1 subst2 target1 target2 (AppE fun1 arg1) (AppE fun2 arg2)
  = unsafeAeq subst1 subst2 target1 target2 fun1 fun2 && unsafeAeq subst1 subst2 target1 target2 arg1 arg2
unsafeAeq subst1 subst2 target1 target2
  (LamE binder1@(UnsafeNameBinder (UnsafeName (name1, label1))) body1)
  (LamE binder2@(UnsafeNameBinder (UnsafeName (name2, label2))) body2)
  | unsafeEquals binder1 binder2 = unsafeAeq subst1 subst2 target1 target2 body1 body2
  | unsafeLess binder1 binder2 =
        let subst2' = IntMap.insert name2 name1 (fmap fst subst2)
            target2' = IntSet.insert name1 target2
        in unsafeAeq subst1 (fmap addLabel subst2') target1 target2' body1 body2
  | otherwise =
        let (UnsafeName name1) = nameOf binder1
            subst1' = IntMap.insert (fst name1) name2 (fmap fst subst1)
            target1' = IntSet.insert name2 target1
        in unsafeAeq (fmap addLabel subst1') subst2 target1' target2 body1 body2
        where addLabel :: Id -> (Id, Label)
              addLabel id = (id, "Label" ++ show id)
unsafeAeq _ _ _ _ _ _ = False

aeq_impl :: Expr n -> Expr n -> Bool
aeq_impl = unsafeAeq IntMap.empty IntMap.empty IntSet.empty IntSet.empty

impl :: LambdaImpl.LambdaImpl
impl =
  LambdaImpl.LambdaImpl
    { LambdaImpl.impl_name = "Foil.Foil",
      LambdaImpl.impl_fromLC = fromLC,
      LambdaImpl.impl_toLC = toLC,
      LambdaImpl.impl_nf = nfd,
      LambdaImpl.impl_nfi = error "nfi unimplemented",
      LambdaImpl.impl_aeq = aeq_impl
    }