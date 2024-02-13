module Suite where

import qualified Core.Nf
import qualified DeBruijn.Bound
import qualified DeBruijn.CPDT
import qualified DeBruijn.Cornell
import qualified DeBruijn.Kit
import qualified DeBruijn.Krivine
import qualified DeBruijn.KrivineScoped
import qualified DeBruijn.Lazy.Bound
import qualified DeBruijn.Lazy.CPDT
import qualified DeBruijn.Lazy.Cornell
import qualified DeBruijn.Lazy.Kit
import qualified DeBruijn.Lazy.Lennart
import qualified DeBruijn.Lazy.Lift
import qualified DeBruijn.Lazy.Nested
import qualified DeBruijn.Lazy.Par.B
import qualified DeBruijn.Lazy.Par.Fun
import qualified DeBruijn.Lazy.Par.GB
import qualified DeBruijn.Lazy.Par.L
import qualified DeBruijn.Lazy.Par.P
import qualified DeBruijn.Lazy.Par.Scoped
import qualified DeBruijn.Lazy.TAPL
import qualified DeBruijn.Lennart
import qualified DeBruijn.Lift
import qualified DeBruijn.Nested
import qualified DeBruijn.Par.B
import qualified DeBruijn.Par.Fun
import qualified DeBruijn.Par.GB
import qualified DeBruijn.Par.L
import qualified DeBruijn.Par.P
import qualified DeBruijn.Par.Scoped
import qualified DeBruijn.TAPL
import qualified FreeScoped.Eager.Foil
import qualified FreeScoped.Eager.Nested
import qualified FreeScoped.Foil
import qualified FreeScoped.Nested
import qualified Lennart.DeBruijn
import qualified Lennart.HOAS
import qualified Lennart.Simple
import qualified Lennart.SimpleOrig
import qualified Lennart.Unique
import qualified LocallyNameless.GenericInstOpt
import qualified LocallyNameless.GenericOpt
import qualified LocallyNameless.Lazy.GenericInstOpt
import qualified LocallyNameless.Lazy.GenericOpt
import qualified LocallyNameless.Lazy.Opt
import qualified LocallyNameless.Lazy.Ott
import qualified LocallyNameless.Lazy.ParOpt
import qualified LocallyNameless.Lazy.ParScoped
import qualified LocallyNameless.Lazy.SupportOpt
import qualified LocallyNameless.Lazy.TypedOtt
import qualified LocallyNameless.Opt
import qualified LocallyNameless.Ott
import qualified LocallyNameless.ParOpt
import qualified LocallyNameless.ParScoped
import qualified LocallyNameless.SupportInstOpt
import qualified LocallyNameless.SupportOpt
import qualified LocallyNameless.TypedOpt
import qualified LocallyNameless.TypedOtt
import qualified NBE.Aelig
import qualified NBE.Boesflug
import qualified NBE.Felgenhauer
import qualified NBE.Kovacs
import qualified NBE.KovacsNamed
import qualified NBE.KovacsScoped
import qualified NBE.KovacsScoped2
import qualified Named.Lazy.NominalG
import qualified Named.Lazy.Simple
import qualified Named.Lazy.SimpleGH
import qualified Named.Lazy.SimpleH
import qualified Named.Lazy.SimpleM
import qualified Named.Lennart
import qualified Named.NominalG
import qualified Named.Simple
import qualified Named.SimpleGH
import qualified Named.SimpleH
import qualified Named.SimpleM
import qualified Named.Unique
import qualified Unbound.UnboundGenerics
import qualified Unbound.UnboundNonGenerics
-- allow newer GHCs
--import qualified Unbound.UnboundRep
import Util.Impl (LambdaImpl)
import qualified Foil.Foil
import qualified Foil.Eager.Foil

-- | Implementations used in the benchmarking/test suite
-- must be a single variable name for Makefile
impls :: [LambdaImpl]
impls = all_impls

interleave :: [a] -> [a] -> [a]
interleave (a1 : a1s) (a2 : a2s) = a1 : a2 : interleave a1s a2s
interleave _ _ = []

broken :: [LambdaImpl]
broken =
  []

--------------------------------------------------------------------------
--------------------------------------------------------------------------
-- divided by implementation strategy
--

all_impls :: [LambdaImpl]
all_impls =
  freeScoped
  ++ debruijn ++ debruijn_lazy
  ++ locallyNameless ++ locallyNameless_lazy ++ named ++ named_lazy
  ++ lennart
  ++ unbound
  ++ nbe

all_debruijn :: [LambdaImpl]
all_debruijn = debruijn ++ debruijn_lazy

all_locallyNameless :: [LambdaImpl]
all_locallyNameless = locallyNameless ++ locallyNameless_lazy

-- | deBruijn index-based implementations
debruijn :: [LambdaImpl]
debruijn =
  [ -- single substitutions
    DeBruijn.TAPL.impl,
    DeBruijn.Cornell.impl,
    DeBruijn.Lennart.impl,
    DeBruijn.Lift.impl,
    -- parallel substitutions
    DeBruijn.Par.L.impl,
    DeBruijn.Par.Fun.impl,
    DeBruijn.Par.P.impl,
    DeBruijn.Par.B.impl,
    DeBruijn.Par.GB.impl,
    -- Well-scoped single
    DeBruijn.CPDT.impl,
    DeBruijn.Nested.impl,
    DeBruijn.Bound.impl, -- bound
    -- well-scoped parallel
    DeBruijn.Kit.impl,
    DeBruijn.Par.Scoped.impl
    -- DeBruijn.Nested2.impl, --fails test suite
  ]

debruijn_lazy :: [LambdaImpl]
debruijn_lazy =
  [ -- single substitutions
    DeBruijn.Lazy.TAPL.impl,
    DeBruijn.Lazy.Cornell.impl,
    DeBruijn.Lazy.Lift.impl,
    DeBruijn.Lazy.Lennart.impl,
    -- parallel substitutions
    DeBruijn.Lazy.Par.Fun.impl,
    DeBruijn.Lazy.Par.L.impl,
    DeBruijn.Lazy.Par.P.impl,
    DeBruijn.Lazy.Par.B.impl,
    DeBruijn.Lazy.Par.GB.impl,
    -- Well-scoped single
    DeBruijn.Lazy.CPDT.impl,
    DeBruijn.Lazy.Nested.impl,
    DeBruijn.Lazy.Bound.impl, -- bound
    -- Well-scoped parallel
    DeBruijn.Lazy.Kit.impl,
    DeBruijn.Lazy.Par.Scoped.impl
  ]

freeScoped :: [LambdaImpl]
freeScoped =
  [ FreeScoped.Foil.impl,
    FreeScoped.Nested.impl,
    Foil.Foil.impl,
    Foil.Eager.Foil.impl,
    FreeScoped.Eager.Foil.impl,
    FreeScoped.Eager.Nested.impl
  ]

-- | Locally Nameless based implmentations
locallyNameless :: [LambdaImpl]
locallyNameless =
  [ LocallyNameless.Ott.impl,
    LocallyNameless.TypedOtt.impl,
    LocallyNameless.ParScoped.impl,
    LocallyNameless.ParOpt.impl,
    LocallyNameless.Opt.impl,
    LocallyNameless.SupportOpt.impl,
    LocallyNameless.SupportInstOpt.impl,
    LocallyNameless.GenericOpt.impl,
    LocallyNameless.GenericInstOpt.impl,
    LocallyNameless.TypedOpt.impl
  ]

locallyNameless_lazy :: [LambdaImpl]
locallyNameless_lazy =
  [ LocallyNameless.Lazy.Ott.impl,
    LocallyNameless.Lazy.TypedOtt.impl,
    LocallyNameless.Lazy.ParScoped.impl,
    LocallyNameless.Lazy.ParOpt.impl,
    LocallyNameless.Lazy.Opt.impl,
    LocallyNameless.Lazy.SupportOpt.impl,
    LocallyNameless.Lazy.GenericOpt.impl
  ]

unbound :: [LambdaImpl]
unbound =
  [ Unbound.UnboundGenerics.impl, -- unbound-generics
    Unbound.UnboundNonGenerics.impl -- no generic programming
  ]

-- | Name based/nominal implementations
named :: [LambdaImpl]
named =
  [ Named.SimpleH.impl,
    Named.SimpleGH.impl,
    Named.SimpleM.impl,
    Named.Lennart.impl,
    Named.Simple.impl,
    Named.Unique.impl
    -- Named.Nom -- too slow
    -- Named.NominalG -- too slow
  ]

named_lazy :: [LambdaImpl]
named_lazy =
  [ Named.Lazy.SimpleH.impl,
    Named.Lazy.SimpleGH.impl,
    Named.Lazy.SimpleM.impl
    -- Named.Lazy.NominalG -- too slow
  ]

lennart :: [LambdaImpl]
lennart =
  [ -- Other
    --Lennart.Unique.impl -- buggy
    --Lennart.SimpleOrig.impl -- buggy
    Lennart.Simple.impl,
    Lennart.DeBruijn.impl,
    Lennart.HOAS.impl
  ]

nbe :: [LambdaImpl]
nbe =
  [ NBE.Aelig.impl,
    -- NBE.Boesflug.impl, -- hangs on full
    NBE.Felgenhauer.impl,
    NBE.Kovacs.impl,
    NBE.KovacsNamed.impl,
    NBE.KovacsScoped.impl,
    NBE.KovacsScoped2.impl,
    DeBruijn.Krivine.impl,
    DeBruijn.KrivineScoped.impl
  ]

---------------------------------------------------
---------------------------------------------------

-- implementations available on hackage
hackage :: [LambdaImpl]
hackage =
  [ -- Named.Nom.impl, -- https://hackage.haskell.org/package/nom
    -- really, really slow.
    Named.NominalG.impl, -- nominal, generally too slow (12s vs. <200 ms for everything else)
    -- https://hackage.haskell.org/package/nominal
    Named.Lazy.NominalG.impl,
    -- Unbound.UnboundRep.impl, -- unbound
    Unbound.UnboundGenerics.impl, -- unbound-generics
    DeBruijn.Bound.impl, -- bound
    DeBruijn.Lazy.Bound.impl -- bound
  ]

generic :: [LambdaImpl]
generic =
  [ DeBruijn.Par.GB.impl,
    DeBruijn.Lazy.Par.GB.impl,
    LocallyNameless.GenericOpt.impl,
    LocallyNameless.Lazy.GenericOpt.impl,
    Named.SimpleGH.impl
  ]

---------------------------------------------------
---------------------------------------------------
-- same implementations, roughly divided by speed

fast :: [LambdaImpl]
fast =
  [ Lennart.HOAS.impl,
    LocallyNameless.Opt.impl,
    LocallyNameless.Lazy.Opt.impl,
    LocallyNameless.SupportInstOpt.impl,
    LocallyNameless.GenericInstOpt.impl,
    LocallyNameless.ParOpt.impl,
    LocallyNameless.Lazy.ParOpt.impl,
    DeBruijn.Par.Scoped.impl,
    DeBruijn.Lazy.Par.Scoped.impl,
    DeBruijn.Par.B.impl,
    DeBruijn.Lazy.Par.B.impl,
    DeBruijn.Par.GB.impl,
    DeBruijn.Lazy.Par.GB.impl,
    DeBruijn.Bound.impl,
    DeBruijn.Lazy.Bound.impl,
    Named.SimpleH.impl,
    Named.Lazy.SimpleH.impl,
    Named.SimpleGH.impl,
    Named.Lazy.SimpleGH.impl
  ]

-- fastest implementation in each category in the NF benchmark
fast_nf :: [LambdaImpl]
fast_nf =
  [ LocallyNameless.Opt.impl, -- 2.56
    LocallyNameless.SupportOpt.impl, -- 2.59
    DeBruijn.Par.Scoped.impl, -- 3.00
    LocallyNameless.GenericOpt.impl, -- 4.36
    --	LocallyNameless.TypedOpt.impl, -- 3.27
    DeBruijn.Lazy.Par.Scoped.impl, -- 5.35
    DeBruijn.Bound.impl, -- 6.07
    DeBruijn.Par.B.impl, -- 7.43
    LocallyNameless.ParOpt.impl, -- 7.46
    DeBruijn.Par.GB.impl, -- 8.51
    DeBruijn.Lazy.Par.GB.impl, -- 11.4
    DeBruijn.Lazy.Par.B.impl, -- 13
    DeBruijn.Lazy.Bound.impl, -- 13.09
    Lennart.HOAS.impl, -- 17.4
    Named.SimpleH.impl, -- 122
    Named.Lazy.SimpleH.impl, -- 166
    Named.Lazy.SimpleGH.impl, -- 169
    Named.SimpleGH.impl -- 193
  ]

fast_random :: [LambdaImpl]
fast_random =
  [ Lennart.HOAS.impl, -- 1
    LocallyNameless.Lazy.Opt.impl, -- 363 -- 178
    LocallyNameless.Opt.impl, -- 434 -- 264
    DeBruijn.Lazy.Par.Scoped.impl, -- 269 -- 261
    --        LocallyNameless.Lazy.TypedOpt.impl, -- 312 -- 316
    --        LocallyNameless.TypedOpt.impl, -- 321 -- 327
    DeBruijn.Lazy.Par.B.impl, -- 356 -- 344
    LocallyNameless.Lazy.ParOpt.impl, -- 557 -- 546
    LocallyNameless.ParOpt.impl, -- 678 -- 684
    DeBruijn.Par.Scoped.impl, -- 876 -- 1360
    DeBruijn.Par.B.impl, -- 954 -- 1310
    Named.SimpleH.impl, -- 7780 -- 11200
    DeBruijn.Bound.impl -- 8440 -- 9500
  ]

-- Fast implementations overall
fast_impls :: [LambdaImpl]
fast_impls =
  fast_debruijn ++ fast_debruijn_lazy ++ fast_locally_nameless ++ fast_named

fast_debruijn :: [LambdaImpl]
fast_debruijn =
  [ DeBruijn.Par.B.impl,
    --DeBruijn.Par.FB.impl,
    DeBruijn.Bound.impl, -- bound
    DeBruijn.Nested.impl
  ]

fast_debruijn_lazy :: [LambdaImpl]
fast_debruijn_lazy =
  [ DeBruijn.Lazy.Par.B.impl,
    --DeBruijn.Lazy.Par.FB.impl,
    DeBruijn.Lazy.Bound.impl, -- bound
    DeBruijn.Lazy.Nested.impl
  ]

fast_locally_nameless :: [LambdaImpl]
fast_locally_nameless =
  [ LocallyNameless.Opt.impl,
    LocallyNameless.ParOpt.impl
    --    LocallyNameless.TypedOpt.impl,
  ]

fast_named :: [LambdaImpl]
fast_named =
  [ Named.SimpleH.impl,
    Named.SimpleGH.impl,
    Named.SimpleM.impl
  ]

slow :: [LambdaImpl]
slow =
  [ DeBruijn.Par.L.impl,
    DeBruijn.Par.Fun.impl,
    DeBruijn.Par.P.impl,
    LocallyNameless.ParScoped.impl,
    --    LocallyNameless.TypedOtt.impl,
    Named.Simple.impl,
    Named.Unique.impl
  ]

really_slow :: [LambdaImpl]
really_slow = [Named.NominalG.impl] -- nominal

--------------------------------------------------------------
--------------------------------------------------------------
-- Versions discussed in the Haskell.love talk Sept 2021

love_talk :: [LambdaImpl]
love_talk = basic_lazy ++ basic_strict ++ opt_lazy ++ opt_strict ++ opt_lazy_generic ++ opt_strict_generic

basic_lazy :: [LambdaImpl]
basic_lazy =
  [ -- Lennart.SimpleOrig.impl,
    Lennart.Simple.impl,
    Lennart.DeBruijn.impl,
    LocallyNameless.Lazy.Ott.impl
  ]

basic_strict :: [LambdaImpl]
basic_strict =
  [ Named.Lennart.impl,
    -- Named.Simple.impl,
    DeBruijn.Lennart.impl,
    LocallyNameless.Ott.impl
  ]

opt_strict :: [LambdaImpl]
opt_strict =
  [ Named.SimpleH.impl,
    DeBruijn.Par.B.impl,
    LocallyNameless.Opt.impl
  ]

opt_lazy :: [LambdaImpl]
opt_lazy =
  [ Named.Lazy.SimpleH.impl,
    DeBruijn.Lazy.Par.B.impl,
    LocallyNameless.Lazy.Opt.impl
  ]

opt_strict_generic :: [LambdaImpl]
opt_strict_generic =
  [ Named.SimpleGH.impl,
    DeBruijn.Par.GB.impl,
    LocallyNameless.GenericInstOpt.impl
  ]

opt_lazy_generic :: [LambdaImpl]
opt_lazy_generic =
  [ Named.Lazy.SimpleGH.impl,
    DeBruijn.Lazy.Par.GB.impl,
    LocallyNameless.Lazy.GenericInstOpt.impl
  ]

love_all :: [LambdaImpl]
love_all =
  [ Lennart.Simple.impl,
    Named.Lennart.impl,
    Named.SimpleH.impl,
    Named.Lazy.SimpleH.impl,
    Named.SimpleGH.impl,
    Named.Lazy.SimpleGH.impl,
    Lennart.DeBruijn.impl,
    DeBruijn.Lennart.impl,
    DeBruijn.Par.B.impl,
    DeBruijn.Lazy.Par.B.impl,
    DeBruijn.Par.GB.impl,
    DeBruijn.Lazy.Par.GB.impl,
    LocallyNameless.Lazy.Ott.impl,
    LocallyNameless.Ott.impl,
    LocallyNameless.Opt.impl,
    LocallyNameless.Lazy.Opt.impl,
    LocallyNameless.GenericInstOpt.impl,
    LocallyNameless.Lazy.GenericInstOpt.impl
  ]
