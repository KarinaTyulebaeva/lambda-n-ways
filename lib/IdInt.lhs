A fast type of identifiers, Ints, for $\lambda$-expressions.

> {-# LANGUAGE DeriveGeneric #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE InstanceSigs #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> 
> module IdInt(IdInt(..), firstBoundId, FreshM, convVar, Nominal(..),
>      ) where

> import Data.List(union, (\\))
> import qualified Data.Map as M
> import Control.Monad.State
> import GHC.Generics
> import Control.DeepSeq
> import Test.QuickCheck
> import Data.Coerce(coerce)

An IdInt is just another name for an Int.

> newtype IdInt = IdInt Int
>     deriving (Eq, Ord, Generic)
>
> instance NFData IdInt
>

It is handy to make IdInt enumerable.

> instance Enum IdInt where
>     toEnum i = IdInt i
>     fromEnum (IdInt i) = i

> firstBoundId :: IdInt
> firstBoundId = toEnum 0

We show IdInts so they look like variables.  Negative numbers
are free variables.

> instance Show IdInt where
>    show (IdInt i) = if i < 0 then "f" ++ show (-i) else "x" ++ show i
> instance Read IdInt where
>    -- skip "x" then read int
>    readsPrec _ (_:str) = coerce ((readsPrec 0 str)::[(Int,String)])


** Generating IdInts

Only generate positive idint

> instance Arbitrary IdInt where
>    arbitrary = IdInt <$> arbitrarySizedNatural
>    shrink (IdInt 0) = []
>    shrink (IdInt n) = [IdInt (n-1)]

** Freshening IdInts

Find a new identifier not in a given set

> class (Ord v, Enum v) => Nominal v where
>    newId  :: [v] -> v

> instance Nominal IdInt where
>   newId :: [IdInt] -> IdInt
> 
>   newId [] = firstBoundId
>   newId vs = succ (maximum vs)


The state monad has the next unused Int and a mapping of identifiers to IdInt.

> type FreshM v a = State (Int, M.Map v IdInt) a

The only operation we do in the monad is to convert a variable.
If the variable is in the map the use it, otherwise add it.

> convVar :: (Ord v) => v -> FreshM v IdInt
> convVar v = do
>    (i, m) <- get
>    case M.lookup v m of
>        Nothing -> do
>            let ii = toEnum i
>            put (i+1, M.insert v ii m)
>            return ii
>        Just ii -> return ii



------------------------------------------------

