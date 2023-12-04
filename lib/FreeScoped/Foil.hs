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

module FreeScoped.Foil (impl) where

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

type Id = Int
type Label = Id
type RawName = (Id, Label)
type RawScope = Map Int Label

data {- kind -} S
  = {- type -} VoidS
  -- | {- type -} Singleton
  -- | {- type -} List

data Scope (n :: S) = UnsafeScope RawScope
data Name (n :: S) = UnsafeName RawName
data NameBinder (n :: S) (l :: S) =
  UnsafeNameBinder (Name l)

ppName :: Name n -> String
ppName (UnsafeName (id, name)) = show name

emptyScope :: Scope VoidS
emptyScope = UnsafeScope Map.empty

extendScope :: NameBinder n l -> Scope n -> Scope l
extendScope (UnsafeNameBinder (UnsafeName (id, name))) (UnsafeScope scope) =
  UnsafeScope (Map.insert id name scope)

rawFreshName :: RawScope -> Label -> RawName
rawFreshName scope labelToBind | Map.null scope = (0, labelToBind)
                               | otherwise =
                                  let (maxId, _) = Map.findMax scope
                                    in (maxId + 1, labelToBind + (maxId + 1))

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
  UnsafeSubstitution (forall n. Name n -> e n) (Map Int (e o))

lookupSubst :: Substitution e i o -> Name i -> e o
lookupSubst (UnsafeSubstitution f env) (UnsafeName (id, label)) =
    case Map.lookup id env of
        Just ex -> ex
        Nothing -> f (UnsafeName (id, label))

identitySubst :: (forall n. Name n -> e n) -> Substitution e i i
identitySubst f = UnsafeSubstitution f Map.empty

addSubst :: Substitution e i o -> NameBinder i i' -> e o -> Substitution e i' o
addSubst (UnsafeSubstitution f env) (UnsafeNameBinder (UnsafeName (id, label))) ex = UnsafeSubstitution f (Map.insert id ex env)

addRename :: Substitution e i o -> NameBinder i i' -> Name o -> Substitution e i' o
addRename s@(UnsafeSubstitution f env) b@(UnsafeNameBinder (UnsafeName name1)) n@(UnsafeName name2)
    | name1 == name2 = UnsafeSubstitution f env
    | otherwise = addSubst s b (f n)

instance (Sinkable e) => Sinkable (Substitution e i) where
  sinkabilityProof rename (UnsafeSubstitution f env) =
    UnsafeSubstitution f (fmap (sinkabilityProof rename) env)

data ScopedAST sig n where
  ScopedAST :: NameBinder n l -> AST sig l -> ScopedAST sig n

data AST sig n where
  Var :: Name n -> AST sig n
  Node :: sig (ScopedAST sig n) (AST sig n) -> AST sig n

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
  deriving (Eq, Show, Functor)
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
  Lam binder body -> Lam binder (nf body)
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let subst =  addSubst (identitySubst Var) binder arg
        in nf scope (substitute scope subst body)
      fun' -> App (nf fun') (nf arg)
  t -> t

toLambdaPi :: Distinct n => Scope n -> Map Int (Name n) -> LC.LC IdInt.IdInt -> LambdaPi n
toLambdaPi scope env = \case
  LC.Var (IdInt.IdInt x) ->
    case Map.lookup x env of
      Just name -> Var name
      Nothing -> error ("unbound variable: " ++ x)

  LC.App fun arg ->
    App (toLambdaPi scope env fun) (toLambdaPi scope env arg)

  LC.Lam (IdInt.IdInt x) body -> withFresh scope x $ \binder ->
    let scope' = extendScope binder scope
        env' = Map.insert x (nameOf binder) (sink <$> env)
    in Lam binder (toLambdaPi scope' env' body)

toDB :: LC.LC IdInt.IdInt -> LambdaPi n
toDB = toLambdaPi emptyScope Map.empty

fromLambdaPi :: LambdaPi n -> LC.LC IdInt.IdInt 
fromLambdaPi = \case
  Var x -> LC.Var (IdInt.IdInt x)
  App fun arg -> LC.App (fromLambdaPi fun) (fromLambdaPi arg)
  Lam binder body ->
    let UnsafeName (id, x) = nameOf binder
    in LC.Lam (IdInt.IdInt x) (fromLambdaPi body)


fromDB :: LambdaPi n -> LC.LC IdInt.IdInt
fromDB = fromLambdaPi

impl :: LambdaImpl.LambdaImpl
impl =
  LambdaImpl.LambdaImpl
    { LambdaImpl.impl_name = "FreeScoped.Foil",
      LambdaImpl.impl_fromLC = toDB,
      LambdaImpl.impl_toLC = fromDB,
      LambdaImpl.impl_nf = nf,
      LambdaImpl.impl_nfi = error "nfi unimplemented",
      LambdaImpl.impl_aeq = error "aeq unimplemented"
    }
