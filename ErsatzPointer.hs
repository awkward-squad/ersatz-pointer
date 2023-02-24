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

module ErsatzPointer
  ( -- * Ersatz pointer
    (:=>) ((:=>)),
    establish,
    establish_,
    onDismantle,

    -- * Ersatz pointer reference
    (:=>?),
    dereference,
    dismantle,

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

-- | An __ersatz pointer__.
data a :=> b = forall (a# :: TYPE UnliftedRep).
  ErsatzPointer
  { source :: a,
    sourceIdentity# :: a#,
    target :: b,
    maybeFinalizer :: !(Maybe (IO ()))
  }

{-# COMPLETE (:=>) #-}

pattern (:=>) :: Source a => a -> b -> (a :=> b)
pattern source :=> target <-
  ErsatzPointer {source, target}
  where
    source :=> target =
      case primitiveIdentity source of
        PrimitiveIdentity# sourceIdentity# ->
          ErsatzPointer
            { source,
              sourceIdentity#,
              target,
              maybeFinalizer = Nothing
            }

-- | /Establish/ an __ersatz pointer__ @__p__@ from object @__a__@ to object @__b__@.
--
-- When this function is called,
--
-- * A relationship is established between @__a__@ and @__b__@ such that if @__a__@ is still alive, then @__b__@ is too,
--   exactly as if @__a__@ contained an actual pointer to @__b__@, as in (for example) the relationship between a record
--   and one of its fields.
--
-- * An __ersatz pointer reference__ @__r__@ is created, and can be used to determine whether @__p__@ is still
--   /established/, which will be the case until either @__a__@ is garbage-collected, or @__p__@ is /dismantled/
--   explicitly, whichever comes first.
--
-- @
--        ┌ /Memory/ ───┐
--        │ __a__       __b__ │
--        └───────────┘
--
--              ┊
--              ▼
--
-- ┌ /Code/ ────────────────────┐
-- │ __r__ \<- 'establish' (__a__ ':=>' __b__) │
-- └──────────────────────────┘
--
--              ┊
--              ▼
--
--        ┌ /Memory/ ───┐
--        │ __a__ ──__p__─➤ __b__ │
--        │     ⇡     │
--        │     __r__     │
--        └───────────┘
-- @
--
-- Note that it may be the case that
--
-- * @__a__@ already cotains an actual pointer to @__b__@.
-- * @__a__@ and @__b__@ are the same object.
--
-- In either case, /establishing/ an __ersatz pointer__ from @__a__@ to @__b__@ may still be useful, because @__r__@ can
-- then be used to determine whether @__a__@ has been garbage-collected, so long as @__r__@ is not /dismantled/
-- explicitly.
establish :: (a :=> b) -> IO (a :=>? b)
establish pointer@ErsatzPointer {sourceIdentity#, maybeFinalizer} =
  coerce (makeWeakPointer sourceIdentity# pointer maybeFinalizer)

-- | Like 'establish', but does not return the __ersatz pointer reference__ @__r__@.
--
-- This is not useful if either
--
-- * @__a__@ already cotains an actual pointer to @__b__@.
-- * @__a__@ and @__b__@ are the same object.
establish_ :: (a :=> b) -> IO ()
establish_ =
  void . establish

-- | Schedule an @IO@ action to be run when @__p__@ is /dismantled/, which is either when @__a__@ is garbage-collected,
-- or when @__p__@ is /dismantled/ explicitly, whichever comes first.
onDismantle :: IO () -> (a :=> b) -> (a :=> b)
onDismantle finalizer pointer =
  pointer {maybeFinalizer = maybeFinalizer pointer <> Just finalizer}

-- | An __ersatz pointer reference__ is a reference to an __ersatz pointer__, and is evidence that the pointer was
-- /established/ at some point.
newtype a :=>? b
  = ErsatzPointerReference (Weak (a :=> b))

-- | /Dereference/ an __ersatz pointer reference__ @__r__@ to determine whether the corresponding __ersatz pointer__
-- @__p__@ from @__a__@ to @__b__@ is still /established/.
--
-- In general, if @__a__@ and @__b__@ are different objects, there are three possible cases, only two of which are
-- distinguishable.
--
-- * @__p__@ is still /established/, because @__a__@ (and therefore @__b__@) are still alive.
--
-- @
-- ┌ /Memory/ ───┐
-- │ __a__ ──__p__─➤ __b__ │
-- │     ⇡     │
-- │     __r__     │
-- └───────────┘
-- @
--
-- * @__p__@ was /dismantled/ because @__a__@ was garbage-collected; it is unknown whether @__b__@ is still alive,
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
-- * @__p__@ was /dismantled/ explicitly; it is unknown whether @__a__@ is still alive, and whether @__b__@ is still
--   alive.
--
-- @
-- ┌ /Memory/ ───┐
-- │ ?       ? │
-- │     ⇡     │
-- │     __r__     │
-- └───────────┘
-- @
dereference :: (a :=>? b) -> IO (Maybe (a :=> b))
dereference (ErsatzPointerReference weak) =
  Weak.deRefWeak weak

-- | /Dismantle/ an __ersatz pointer__ @__p__@ from @__a__@ to @__b__@, which
--
-- 1. Undoes the relationship established by 'establish', i.e. makes it no longer the case that if @__a__@ is alive,
--    @__b__@ is too.
-- 2. Causes any registered 'onDismantle' actions to be run immediately.
--
-- This action is a no-op if @__p__@ was alread /dismantled/, either because @__a__@ was already garbage-collected, or
-- because it was /dismantled/ explicitly.
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
-- ┌ /Code/ ───────┐
-- │ 'dismantle' __r__ │
-- └─────────────┘
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
dismantle :: (a :=>? b) -> IO ()
dismantle (ErsatzPointerReference weak) =
  Weak.finalize weak

------------------------------------------------------------------------------------------------------------------------
-- Source

-- | The class of types that can be used as the source of an __ersatz pointer__.
--
-- This includes types whose values have a primitive identity, but may also include product types that contain such a
-- type via user-defined instances.
--
-- ==== __👉 Example user-defined instance__
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
