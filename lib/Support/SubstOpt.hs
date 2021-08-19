{-# LANGUAGE DefaultSignatures #-}

-- | Based directly on transliteration of Coq output for Ott Locally Nameless Backend
-- Then with multi substitutions
-- And caching openning substitutions at binders
-- and caching closing substitutions at binders
-- and removing types so we can use ints instead of unary nats
module Support.SubstOpt where

import qualified Control.Monad.State as State
import qualified Data.IntMap as IM
import Data.List (elemIndex)
import qualified Data.Set as S
import GHC.Generics
import Util.IdInt (IdInt (..), firstBoundId)
import Util.Impl (LambdaImpl (..))
import Util.Imports hiding (S, from, to)
import qualified Util.Lambda as LC

-- 0. Original (Ott derived version)
-- lennart: 1.03s
-- random: 0.807 ms

-- 1. (TypedOtt) Well-typed (slows it down)
-- lennart: 1.43s
-- random: 1.8ms

-- 2. (ParScoped) Well-typed multisubst

-- 3. (Opt) Combo multisubst for open & close
-- lennart: 3.05 ms
-- random: 0.135 ms

-- 5. back to ints, with some general cleanup
-- NOTE: actually caching close at binder incurs a small penalty (second #s)
-- lennart: 2.76 ms / 3.13 ms
-- random: 0.116 ms / 0.126 ms
-- con20: 721ns / 678ns
-- capt9: 387ns / 386ns
--- (NOTE: dlists instead of lists slows things down)
--- What about Data.Sequence???

-------------------------------------------------------------------
class VarC a where
  var :: Var -> a

  isvar :: a -> Maybe Var
  isvar _ = Nothing
  {-# INLINE isvar #-}

class AlphaC a where
  fv :: a -> Set IdInt
  default fv :: (Generic a, GAlpha (Rep a)) => a -> Set IdInt
  fv x = gfv (from x)

  -- | replace bound variables with a list of free variables
  multi_open_rec :: [IdInt] -> a -> a

  -- | replace free variables (noted as "IdInt") with their respective bound variables
  multi_close_rec :: Int -> [IdInt] -> a -> a
  default multi_close_rec :: (Generic a, GAlpha (Rep a)) => Int -> [IdInt] -> a -> a
  multi_close_rec k vs x = to (gmulti_close_rec k vs (from x))

  {-# INLINE fv #-}
  {-# INLINE multi_close_rec #-}

class AlphaC a => SubstC b a where
  -- | substitute for bound variables
  multi_subst_bv :: [b] -> a -> a
  default multi_subst_bv :: (Generic a, VarC b, GOpen b (Rep a), a ~ b) => [b] -> a -> a
  multi_subst_bv vs x =
    case isvar x of
      Just v -> substBvVar vs v
      Nothing -> to (gmulti_subst_bv vs (from x))
  {-# INLINE multi_subst_bv #-}

--------------------------------------------------------------

data Var = B Int | F IdInt deriving (Generic, Eq)

instance NFData Var

instance VarC Var where
  var = id
  isvar x = Just x

instance AlphaC Var where
  fv (B _) = S.empty
  fv (F x) = S.singleton x

  multi_close_rec k xs (F x) =
    case elemIndex x xs of
      Just n -> B (n + k)
      Nothing -> F x
  multi_close_rec _k _xs (B n2) = (B n2)
  {-# INLINE fv #-}
  {-# INLINE multi_close_rec #-}

  multi_open_rec vs v = substBvVar (map F vs) v

substBvVar :: VarC a => [a] -> Var -> a
substBvVar _ (F x) = var (F x)
substBvVar vs (B i) = vs !! i
{-# INLINEABLE substBvVar #-}

substFvVar :: VarC a => a -> IdInt -> Var -> a
substFvVar _ _ (B n) = var (B n)
substFvVar u y (F x) = if x == y then u else (var (F x))
{-# INLINEABLE substFvVar #-}

-------------------------------------------------------------------

-- Caching open/close at binders.
-- To speed up this implementation, we delay the execution of open / close
-- in a binder so that multiple traversals can fuse together

data Bind a where
  Bind :: !a -> Bind a
  BindSubst :: ![a] -> !a -> Bind a
  BindOpen :: ![IdInt] -> !a -> Bind a
  BindClose :: !Int -> ![IdInt] -> !a -> Bind a

instance (NFData a) => NFData (Bind a) where
  rnf (BindSubst s a) = rnf s `seq` rnf a
  rnf (Bind a) = rnf a
  rnf (BindOpen s a) = rnf s `seq` rnf a
  rnf (BindClose k v a) =
    rnf k
      `seq` rnf v
      `seq` rnf a

instance (Eq a, SubstC a a) => Eq (Bind a) where
  b1 == b2 = unbind b1 == unbind b2

-- create a binding by "abstracting a variable"
bind :: a -> Bind a
bind = Bind
{-# INLINEABLE bind #-}

unbind :: SubstC a a => Bind a -> a
unbind (Bind a) = a
-- this is always 0 because multi_subst_bv never
-- goes under binders
unbind (BindSubst ss a) = multi_subst_bv ss a
unbind (BindOpen ss a) = multi_open_rec ss a
unbind (BindClose k vs a) = multi_close_rec k vs a
{-# INLINEABLE unbind #-}

instance (SubstC a a) => AlphaC (Bind a) where
  fv :: Bind a -> Set IdInt
  fv b = fv (unbind b)

  multi_open_rec vn (BindOpen vm b) = BindOpen (vm <> vn) b
  multi_open_rec vn b = BindOpen vn (unbind b)

  multi_close_rec k xs b = case b of
    (BindClose k0 ys a) -> (BindClose k0 (ys <> xs) a)
    _ -> (BindClose (k + 1) xs (unbind b))
  {-# INLINE fv #-}
  {-# INLINE multi_close_rec #-}

instance SubstC a a => SubstC a (Bind a) where
  -- we know k will be 0 here because we never need to
  -- go under a binder with multi_subst_bv. We just gather the
  -- substitutions together at the first binder that we find.
  multi_subst_bv vn (BindSubst vm b) = (BindSubst (vm <> vn) b)
  {- multi_subst_bv k vn (BindSubst vm _b) =
    error $
      "multi_subst_bv BindSubst called with k=" ++ show k
        ++ "|vn|="
        ++ show (length vn)
        ++ " and |vm|="
        ++ show (length vm) -}
  multi_subst_bv vn b = (BindSubst vn (unbind b))
  {- multi_subst_bv k _vn _b =
    error $ "multi_subst_bv Bind called with k=" ++ show k -}
  {-# INLINE multi_subst_bv #-}

-- keep track of the opening that has been done already
-- via bound-variable substitution
-- a substitution looks like
-- k=1    0 -> 0 , 1 -> 1 , k+1 -> x, k+2 -> y, ...
-- as we apply it underneath a binding, it needs to be converted to
-- a larger scope (where the newly bound variables are left alone).
-- k=2    0 -> 0 , 1 -> 1 , 2 -> 2, k+1 -> x, k+2 -> y, ...
-- more generally, we have the scope depth k and a n-ary mapping for variables k+i for 0<=i<n

-- | Note: the binding should be localy closed
instantiate :: (SubstC a a) => Bind a -> a -> a
instantiate (BindSubst vs e) u = multi_subst_bv (u : vs) e -- this needs to be 0
instantiate b u = multi_subst_bv [u] (unbind b)
{-# INLINEABLE instantiate #-}

-----------------------------------------------------------------

open :: SubstC a a => Bind a -> IdInt -> a
open b x = multi_open_rec [x] (unbind b)
{-# INLINEABLE open #-}

close :: IdInt -> a -> Bind a
close x e = BindClose 0 [x] e
{-# INLINEABLE close #-}

---------------------------------------------------------------------

class GAlpha f where
  gfv :: f a -> Set IdInt
  gmulti_close_rec :: Int -> [IdInt] -> f a -> f a

class GOpen b f where
  gmulti_subst_bv :: [b] -> f a -> f a

-------------------------------------------------------------------
newtype Ignore a = Ignore a

-- Constant types
instance (SubstC b c) => GOpen b (K1 i c) where
  gmulti_subst_bv vs (K1 c) = K1 (multi_subst_bv vs c)
  {-# INLINE gmulti_subst_bv #-}

instance GOpen b U1 where
  gmulti_subst_bv _v U1 = U1
  {-# INLINE gmulti_subst_bv #-}

instance GOpen b f => GOpen b (M1 i c f) where
  gmulti_subst_bv vs = M1 . gmulti_subst_bv vs . unM1
  {-# INLINE gmulti_subst_bv #-}

instance GOpen b V1 where
  gmulti_subst_bv _vs = id
  {-# INLINE gmulti_subst_bv #-}

instance (GOpen b f, GOpen b g) => GOpen b (f :*: g) where
  gmulti_subst_bv vs (f :*: g) = gmulti_subst_bv vs f :*: gmulti_subst_bv vs g
  {-# INLINE gmulti_subst_bv #-}

instance (GOpen b f, GOpen b g) => GOpen b (f :+: g) where
  gmulti_subst_bv vs (L1 f) = L1 $ gmulti_subst_bv vs f
  gmulti_subst_bv vs (R1 g) = R1 $ gmulti_subst_bv vs g
  {-# INLINE gmulti_subst_bv #-}

instance SubstC b (Ignore a) where
  multi_subst_bv _ = id
  {-# INLINE multi_subst_bv #-}

instance SubstC b Int where
  multi_subst_bv _ = id
  {-# INLINE multi_subst_bv #-}

instance SubstC b Bool where
  multi_subst_bv _ = id
  {-# INLINE multi_subst_bv #-}

instance SubstC b () where
  multi_subst_bv _ = id
  {-# INLINE multi_subst_bv #-}

instance SubstC b Char where
  multi_subst_bv _ = id
  {-# INLINE multi_subst_bv #-}

instance SubstC b Var where
  multi_subst_bv _ = id
  {-# INLINE multi_subst_bv #-}

instance (Generic a, AlphaC a, GOpen b (Rep [a])) => SubstC b [a] where
  multi_subst_bv xs x = to $ gmulti_subst_bv xs (from x)
  {-# INLINE multi_subst_bv #-}

instance (Generic a, AlphaC a, GOpen b (Rep (Maybe a))) => SubstC b (Maybe a) where
  multi_subst_bv xs x = to $ gmulti_subst_bv xs (from x)
  {-# INLINE multi_subst_bv #-}

instance (Generic (Either a1 a2), AlphaC (Either a1 a2), GOpen b (Rep (Either a1 a2))) => SubstC b (Either a1 a2) where
  multi_subst_bv xs x = to $ gmulti_subst_bv xs (from x)
  {-# INLINE multi_subst_bv #-}

instance (Generic (a, b), AlphaC (a, b), GOpen c (Rep (a, b))) => SubstC c (a, b) where
  multi_subst_bv xs x = to $ gmulti_subst_bv xs (from x)
  {-# INLINE multi_subst_bv #-}

instance
  ( Generic (a, b, d),
    AlphaC (a, b, d),
    GOpen c (Rep (a, b, d))
  ) =>
  SubstC c (a, b, d)
  where
  multi_subst_bv xs x = to $ gmulti_subst_bv xs (from x)
  {-# INLINE multi_subst_bv #-}

----------------------------------------------------------------

instance (AlphaC c) => GAlpha (K1 i c) where
  gfv (K1 c) = (fv c)
  gmulti_close_rec x xs (K1 c) = K1 (multi_close_rec x xs c)
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance GAlpha U1 where
  gfv U1 = S.empty
  gmulti_close_rec _ _ = id
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance GAlpha f => GAlpha (M1 i c f) where
  gfv = gfv . unM1
  gmulti_close_rec x xs = M1 . gmulti_close_rec x xs . unM1
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance GAlpha V1 where
  gfv _s = S.empty
  gmulti_close_rec _ _ = id
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance (GAlpha f, GAlpha g) => GAlpha (f :*: g) where
  gfv (f :*: g) = gfv f `S.union` gfv g
  gmulti_close_rec x xs (f :*: g) =
    gmulti_close_rec x xs f :*: gmulti_close_rec x xs g
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance (GAlpha f, GAlpha g) => GAlpha (f :+: g) where
  gfv (L1 f) = gfv f
  gfv (R1 g) = gfv g
  gmulti_close_rec x xs (L1 f) = L1 $ gmulti_close_rec x xs f
  gmulti_close_rec x xs (R1 g) = R1 $ gmulti_close_rec x xs g
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance AlphaC (Ignore a) where
  fv _ = S.empty
  multi_open_rec _ = id
  multi_close_rec _ _ = id
  {-# INLINE fv #-}
  {-# INLINE multi_close_rec #-}

instance AlphaC Int where
  fv _ = S.empty
  multi_open_rec _ = id
  multi_close_rec _ _ = id
  {-# INLINE fv #-}
  {-# INLINE multi_close_rec #-}

instance AlphaC Bool where
  fv _ = S.empty
  multi_open_rec _ = id
  multi_close_rec _ _ = id
  {-# INLINE fv #-}
  {-# INLINE multi_close_rec #-}

instance AlphaC () where
  fv _ = S.empty
  multi_open_rec _ = id
  multi_close_rec _ _ = id
  {-# INLINE fv #-}
  {-# INLINE multi_close_rec #-}

instance AlphaC Char where
  fv _ = S.empty
  multi_open_rec _ = id
  multi_close_rec _ _ = id
  {-# INLINE fv #-}
  {-# INLINE multi_close_rec #-}

instance AlphaC String where
  fv _ = S.empty
  multi_open_rec _ = id
  multi_close_rec _ _ = id
  {-# INLINE fv #-}
  {-# INLINE multi_close_rec #-}

instance AlphaC a => AlphaC [a]

instance AlphaC a => AlphaC (Maybe a)

instance (AlphaC a1, AlphaC a2) => AlphaC (Either a1 a2)

instance (AlphaC a, AlphaC b) => AlphaC (a, b)

instance (AlphaC a, AlphaC b, AlphaC d) => AlphaC (a, b, d)
