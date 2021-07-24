{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module LocallyNameless.Unbound (nf, LocallyNameless.Unbound.aeq, aeqd, fromDB, toDB, nfu, impl) where

import qualified Control.DeepSeq as DS
import Unbound.LocallyNameless as U
  ( Alpha,
    Bind,
    FreshM,
    Name,
    R,
    Rep (..),
    Subst (isvar),
    SubstName (SubstName),
    aeq,
    bind,
    derive,
    name2Integer,
    runFreshM,
    s2n,
    substBind,
    unbind,
    type (:*:) ((:*:)),
  )
import Util.IdInt hiding (FreshM)
import Util.Impl
import qualified Util.Lambda as LC

data Exp
  = Var !(U.Name Exp)
  | Lam !(U.Bind (U.Name Exp) Exp)
  | App !Exp !Exp
  deriving (Show)

instance DS.NFData Exp where
  rnf (Var n) = DS.rnf n
  rnf (Lam bnd) = DS.rnf bnd -- DS.rnf bnd
  rnf (App e1 e2) = DS.rnf e1 `seq` DS.rnf e2

-- Use RepLib to derive representation types

$(U.derive [''Exp])

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "LocallyNameless.Unbound",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfu,
      impl_nfi = error "nfi unimplementd for unbound",
      impl_aeq = aeqd
    }

--With representation types, the default implementation of Alpha
--provides alpha-equivalence and free variable calculation.

aeq :: LC.LC IdInt -> LC.LC IdInt -> Bool
aeq x y = U.aeq (toDB x) (toDB y)

aeqd :: Exp -> Exp -> Bool
aeqd = U.aeq

instance U.Alpha Exp

-- | The subst class uses generic programming to implement capture
-- avoiding substitution. It just needs to know where the variables
-- are.
instance U.Subst Exp Exp where
  isvar (Var x) = Just (U.SubstName x)
  isvar _ = Nothing

nfu :: Exp -> Exp
nfu = runFreshM . nfd

nf :: LC.LC IdInt -> LC.LC IdInt
nf = fromDB . nfu . toDB

--Computing the normal form proceeds as usual.

nfd :: Exp -> FreshM Exp
nfd e@(Var _) = return e
nfd (Lam e) =
  do
    (x, e') <- U.unbind e
    e1 <- nfd e'
    return $ Lam (U.bind x e1)
nfd (App f a) =
  case whnf f of
    Lam b -> nfd (U.substBind b a)
    f' -> App <$> nfd f' <*> nfd a

--Compute the weak head normal form.

whnf :: Exp -> Exp
whnf e@(Var _) = e
whnf e@(Lam _) = e
whnf (App f a) =
  case whnf f of
    Lam b -> whnf (substBind b a)
    f' -> App f' a

--Convert from LC type to DB type (try to do this in linear time??)

toDB :: LC.LC IdInt -> Exp
toDB = to
  where
    to :: LC.LC IdInt -> Exp
    to (LC.Var v) = Var (i2n v)
    to (LC.Lam x b) = Lam (bind (i2n x) (to b))
    to (LC.App f a) = App (to f) (to a)

-- Convert back from deBruijn to the LC type.

n2i :: Name Exp -> IdInt
n2i n = IdInt (fromInteger (name2Integer n))

i2n :: IdInt -> Name Exp
i2n (IdInt x) = s2n (show x)

fromDB :: Exp -> LC.LC IdInt
fromDB = runFreshM . from
  where
    from :: Exp -> FreshM (LC.LC IdInt)
    from (Var n) = return $ LC.Var (n2i n)
    from (Lam b) = do
      (x, a) <- unbind b
      LC.Lam (n2i x) <$> from a
    from (App f a) = LC.App <$> from f <*> from a
