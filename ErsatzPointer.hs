{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE ViewPatterns #-}

-- |
--
-- Ersatz pointer: a safe and friendly interface to weak pointers in GHC.
--
-- This module merely wraps the existing weak pointer interface provided by "System.Mem.Weak" in a different skin; its
-- primary purpose is to teach users how to use weak pointers with diagrams and intuitive names.
--
-- Nonetheless, even if you already understand how to use weak pointers, you may be interested in using this library
-- because of two small improvements:
--
-- * The 'Source' type class, which classifies types that are safe to use as the source of a weak pointer, per the
--   disclaimer:
--
--     /"WARNING: weak pointers to ordinary non-primitive Haskell types are particularly fragile, because the compiler is free to optimise away or duplicate the underlying data structure."/
--
-- * The 'Material' phantom type, which allows one to create weak pointers that cannot be finalized early.
--
-- This module is intended to be imported qualified:
--
-- @
-- import ErsatzPointer qualified as Ersatz (Pointer, PointerReference)
-- import ErsatzPointer qualified as ErsatzPointer
-- @
module ErsatzPointer
  ( -- * Ersatz pointer
    Pointer (Pointer),
    construct,
    construct_,
    onDemolish,

    -- * Ersatz pointer reference
    PointerReference,
    Material (..),
    dereference,
    demolish,

    -- * Source
    Source (..),
    PrimitiveIdentity,
  )
where

import Data.Coerce (coerce)
import Data.Functor (void)
import Data.IORef (IORef)
import GHC.Base (IO (IO), UnliftedRep, mkWeak#, mkWeakNoFinalizer#)
import GHC.Conc (TVar (TVar), ThreadId (ThreadId))
import GHC.Exts (TYPE)
import GHC.IO ()
import GHC.IORef (IORef (IORef))
import GHC.MVar (MVar (MVar))
import GHC.STRef (STRef (STRef))
import GHC.Weak (Weak (Weak))
import qualified System.Mem.Weak as Weak

-- | An __ersatz pointer__ from object @__a__@ to object @__b__@.
data Pointer a b = forall (a# :: TYPE UnliftedRep).
  Pointer_
  { source :: a,
    sourceIdentity# :: a#,
    target :: b,
    maybeFinalizer :: !(Maybe (IO ()))
  }

{-# COMPLETE Pointer #-}

pattern Pointer :: Source a => a -> b -> Pointer a b
pattern Pointer source target <-
  Pointer_ {source, target}
  where
    Pointer source target =
      case primitiveIdentity source of
        PrimitiveIdentity# sourceIdentity# ->
          Pointer_
            { source,
              sourceIdentity#,
              target,
              maybeFinalizer = Nothing
            }

-- | /Construct/ an __ersatz pointer__ @__p__@ made of material @__t__@ from object @__a__@ to object @__b__@.
--
-- When this function is called,
--
-- * A relationship is established between @__a__@ and @__b__@ such that if @__a__@ is still alive, then @__b__@ is too,
--   exactly as if @__a__@ contained an actual pointer to @__b__@, as in (for example) the relationship between a record
--   and one of its fields.
--
-- * An __ersatz pointer reference__ @__r__@ is created, and can be used to determine whether @__p__@ is still
--   /constructed/, which will be the case until either:
--
--     * @__a__@ is garbage-collected
--     * @__p__@ is /demolished/ explicitly, which is only possible if it is made of __straw__.
--
-- Note that it may be the case that
--
-- * @__a__@ already contains an actual pointer to @__b__@.
-- * @__a__@ and @__b__@ are the same object.
--
-- In either case, /constructing/ an __ersatz pointer__ from @__a__@ to @__b__@ may still be useful, because @__r__@ can
-- then be used to determine whether @__a__@ has been garbage-collected, so long as @__r__@ is not /demolished/
-- explicitly.
--
-- ==== __👉 Diagram: constructing an ersatz pointer between distinct objects__
--
-- @
--              ┌ /Memory/ ───┐
--              │ __a__       __b__ │
--              └───────────┘
--
--                    ┊
--                    ▼
--
-- ┌ /Code/ ────────────────────────────────┐
-- │ __r__ \<- 'construct' \@''Straw' ('Pointer' __a__ __b__) │
-- └──────────────────────────────────────┘
--
--                    ┊
--                    ▼
--
--              ┌ /Memory/ ───┐
--              │ __a__ ──__p__─➤ __b__ │
--              │     ⇡     │
--              │     __r__     │
--              └───────────┘
-- @
construct :: forall t a b. Pointer a b -> IO (PointerReference t a b)
construct pointer@Pointer_ {sourceIdentity#, maybeFinalizer} =
  coerce (makeWeakPointer sourceIdentity# pointer maybeFinalizer)

-- | Like 'construct', but does not return the __ersatz pointer reference__ @__r__@.
construct_ :: Pointer a b -> IO ()
construct_ =
  void . construct

-- | Schedule an @IO@ action to be run when @__p__@ is /demolished/, which is either when @__a__@ is garbage-collected,
-- or when @__p__@ is /demolished/ explicitly, whichever comes first.
--
-- @
-- 'Pointer' a b
--   & 'onDemolish' f
-- @
onDemolish :: IO () -> Pointer a b -> Pointer a b
onDemolish finalizer pointer =
  pointer {maybeFinalizer = maybeFinalizer pointer <> Just finalizer}

-- | An __ersatz pointer reference__ is a reference to an __ersatz pointer__, and is evidence that the pointer was
-- /constructed/ at some point.
newtype PointerReference (t :: Material) a b
  = PointerReference (Weak (Pointer a b))

-- | The __material__ an __ersatz pointer reference__ was /constructed/ with.
--
-- Following the three little pigs, one of __straw__ can be /demolished/, but one of __brick__ cannot.
data Material
  = Straw
  | Brick

-- | /Dereference/ an __ersatz pointer reference__ @__r__@ to determine whether the corresponding __ersatz pointer__
-- @__p__@ from @__a__@ to @__b__@ is still /constructed/.
--
-- In general, if @__a__@ and @__b__@ are different objects, there are three possible cases.
--
-- * @__p__@ is still /constructed/, because @__a__@ (and therefore @__b__@) are still alive.
--
-- @
-- ┌ /Memory/ ───┐
-- │ __a__ ──__p__─➤ __b__ │
-- │     ⇡     │
-- │     __r__     │
-- └───────────┘
-- @
--
-- * @__p__@ was /demolished/ because @__a__@ was garbage-collected; it is unknown whether @__b__@ is still alive,
--   because @__b__@ may still be referred to by another object.
--
-- @
-- ┌ /Memory/ ───┐
-- │         ? │
-- │     ⇡     │
-- │     __r__     │
-- └───────────┘
-- @
--
-- * @__p__@ was /demolished/ explicitly; it is unknown whether @__a__@ is still alive, and whether @__b__@ is still
--   alive.
--
--     This case is not possible @__p__@ is made of __brick__.
--
-- @
-- ┌ /Memory/ ───┐
-- │ ?       ? │
-- │     ⇡     │
-- │     __r__     │
-- └───────────┘
-- @
dereference :: PointerReference t a b -> IO (Maybe (Pointer a b))
dereference (PointerReference weak) =
  Weak.deRefWeak weak

-- | /Demolish/ an __ersatz pointer__ @__p__@ from @__a__@ to @__b__@, which
--
-- 1. Undoes the relationship established by 'construct', i.e. makes it no longer the case that if @__a__@ is alive,
--    @__b__@ is too.
-- 2. Causes any registered 'onDemolish' actions to be run immediately.
--
-- This action is a no-op if @__p__@ was alread /demolished/, either because @__a__@ was already garbage-collected, or
-- because it was /demolished/ explicitly.
--
-- @
--  ┌ /Memory/ ───┐
--  │ __a__ ──__p__─➤ __b__ │
--  │     ⇡     │
--  │     __r__     │
--  └───────────┘
--
--        ┊
--        ▼
--
-- ┌ /Code/ ──────┐
-- │ 'demolish' __r__ │
-- └────────────┘
--
--        ┊
--        ▼
--
--  ┌ /Memory/ ───┐
--  │ __a__       __b__ │
--  │     ⇡     │
--  │     __r__     │
--  └───────────┘
-- @
demolish :: PointerReference 'Straw a b -> IO ()
demolish (PointerReference weak) =
  Weak.finalize weak

------------------------------------------------------------------------------------------------------------------------
-- Source

-- | The class of types that can be used as the source of an __ersatz pointer__.
--
-- This includes types whose values have a primitive identity, but may also include product types that contain such a
-- type via user-defined instances.
--
-- ==== __👉 Example: user-defined instance__
--
-- @
-- data MyRecord = MyRecord
--   { ...
--   , ref :: IORef ()
--   , ...
--   }
--
-- instance 'Source' MyRecord where
--   'primitiveIdentity' MyRecord{ref} = 'primitiveIdentity' ref
-- @
--
-- Take care when writing such instances: a user of a `MyRecord` value should not be able to obtain a reference to the
-- `ref` contained within, either directly or via a closure.
class Source a where
  primitiveIdentity :: a -> PrimitiveIdentity

instance Source (IORef a) where
  primitiveIdentity :: IORef a -> PrimitiveIdentity
  primitiveIdentity (IORef (STRef var#)) = PrimitiveIdentity# var#

instance Source (MVar a) where
  primitiveIdentity :: MVar a -> PrimitiveIdentity
  primitiveIdentity (MVar var#) = PrimitiveIdentity# var#

instance Source ThreadId where
  primitiveIdentity :: ThreadId -> PrimitiveIdentity
  primitiveIdentity (ThreadId id#) = PrimitiveIdentity# id#

instance Source (TVar a) where
  primitiveIdentity :: TVar a -> PrimitiveIdentity
  primitiveIdentity (TVar var#) = PrimitiveIdentity# var#

-- | The primitive identity of a value.
data PrimitiveIdentity where
  PrimitiveIdentity# :: forall (a :: TYPE UnliftedRep). a -> PrimitiveIdentity

-- The type that System.Mem.Weak.mkWeak *should* have - unlifted first argument. (Even that isn't good enough - we
-- really want to know this value has a primitive identity, hence the 'Source' class above).
makeWeakPointer :: forall (source# :: TYPE UnliftedRep) target. source# -> target -> Maybe (IO ()) -> IO (Weak target)
makeWeakPointer source# target = \case
  Nothing ->
    IO \s0# ->
      case mkWeakNoFinalizer# source# target s0# of
        (# s1#, weak# #) -> (# s1#, Weak weak# #)
  Just (IO finalizer#) ->
    IO \s0# ->
      case mkWeak# source# target finalizer# s0# of
        (# s1#, weak# #) -> (# s1#, Weak weak# #)
