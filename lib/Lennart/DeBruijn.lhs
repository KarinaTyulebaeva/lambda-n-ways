The DeBruijn module implements the Normal Form function by
using de Bruijn indicies. 

It is originally from Lennart Augustsson's implementation
but has been modified to to fit into this setting.

> module Lennart.DeBruijn(impl) where
> import Data.List(elemIndex)
> import Data.Maybe(mapMaybe)
> import Util.Lambda
> import Util.IdInt
> import Control.DeepSeq
> import GHC.Generics ( Generic )

> import Util.Impl

> impl :: LambdaImpl
> impl = LambdaImpl {
>             impl_name   = "Lennart.DeBruijn"
>           , impl_fromLC = toDB
>           , impl_toLC   = fromDB
>           , impl_nf     = nfd
>           , impl_nfi    = nfi
>           , impl_aeq    = (==)
>        }


Variables are represented by their binding depth, i.e., how many
$\lambda$s out the binding $\lambda$ is.  

> data DB = DVar !Int | DLam DB | DApp DB DB
>   deriving (Eq, Generic)

> instance NFData DB where


Computing the normal form proceeds as usual.

> nfd :: DB -> DB
> nfd e@(DVar _) = e
> nfd (DLam e) = DLam (nfd e)
> nfd (DApp f a) =
>     case whnf f of
>         DLam b -> nfd (instantiate b a)
>         f' -> DApp (nfd f') (nfd a)

Compute the weak head normal form.

> whnf :: DB -> DB
> whnf e@(DVar _) = e
> whnf e@(DLam _) = e
> whnf (DApp f a) =
>     case whnf f of
>         DLam b -> whnf (instantiate b a)
>         f' -> DApp f' a


Bounded versions

> nfi :: Int -> DB -> Maybe DB
> nfi 0 _e = Nothing
> nfi _n e@(DVar _) = return e
> nfi n (DLam b) = DLam <$> nfi (n-1) b
> nfi n (DApp f a) = do
>     f' <- whnfi (n-1) f 
>     case f' of
>         DLam b -> nfi (n-1) (instantiate b a)
>         _ -> DApp <$> nfi n f' <*> nfi n a

> whnfi :: Int -> DB -> Maybe DB
> whnfi 0 _e = Nothing
> whnfi _n e@(DVar _) = return e
> whnfi _n e@(DLam _) = return e
> whnfi n (DApp f a) = do
>     f' <- whnfi (n-1) f 
>     case whnf f' of
>         DLam b -> whnfi (n-1) (instantiate b a)
>         _ -> return $ DApp f' a

-----------------------------------------------------------

Convert to deBruijn indicies.  Do this by keeping a list of the bound
variable so the depth can be found of all variables.  Do not touch
free variables.

> toDB :: LC IdInt -> DB
> toDB = to []
>   where to vs (Var v@(IdInt i)) = maybe (DVar i) DVar (elemIndex v vs)
>         to vs (Lam x b) = DLam (to (x:vs) b)
>         to vs (App f a) = DApp (to vs f) (to vs a)

Convert back from deBruijn to the LC type.

> fromDB :: DB -> LC IdInt
> fromDB = from firstBoundId
>   where from (IdInt n) (DVar i) | i < 0     = Var (IdInt i)
>                                 | i >= n    = Var (IdInt i)
>                                 | otherwise = Var (IdInt (n-i-1))
>         from n (DLam b) = Lam n (from (succ n) b)
>         from n (DApp f a) = App (from n f) (from n a)

----------------------------------------------------------

Substitution needs to adjust the inserted expression
so the free variables refer to the correct binders.
This must happen for each occurrence of the substituted term
(as they could be at different binding depths).
(See the 'apply' function.)

> instantiate :: DB -> DB -> DB
> instantiate b a = subst 0 a b
> {-# INLINE instantiate #-}

> subst :: Int -> DB -> DB -> DB
> subst o s (DVar i) = apply o s i
> subst o s (DLam e) = DLam (subst (o+1) s e)
> subst o s (DApp f a) = DApp (subst o s f) (subst o s a)

> apply :: Int -> DB -> Int -> DB
> apply o s i
>  | i == o    = adjust s 0
>  | i >  o    = DVar (i-1)    -- adjust free variables down 
>  | otherwise = DVar i
>  where 
>    -- increment all "free" variables by `o`
>    -- initially, this operation should be called with n=0
>    adjust :: DB -> Int -> DB
>    adjust e@(DVar j) n | j >= n = DVar (j+o)
>                       | otherwise = e
>    adjust (DLam e) n = DLam (adjust e (n+1))
>    adjust (DApp f a) n = DApp (adjust f n) (adjust a n)
> {-# INLINE apply #-}
