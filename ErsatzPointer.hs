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

import Data.Functor
import Data.Kind
import GHC.Conc
import GHC.Exts
import GHC.IO
import GHC.IORef
import GHC.MVar
import GHC.STRef
import GHC.Weak
import System.Mem.Weak

-- | An __ersatz pointer__.
data a :=> b = forall (a# :: TYPE 'UnliftedRep).
  Kv
  { key :: a,
    key# :: !PrimitiveIdentity,
    value :: b,
    maybeFinalizer :: !(Maybe (IO ()))
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
establish v@Kv {key, key#, value, maybeFinalizer} =
  withPrimitiveIdentity key# \k# -> do
    w <-
      case maybeFinalizer of
        Nothing -> weakNoFinalizer k# v
        Just finalizer -> weak k# v finalizer
    pure (W w)

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
onDismantle :: (a :=> b) -> IO () -> (a :=> b)
onDismantle x f =
  x {maybeFinalizer = maybeFinalizer x <> Just f}

-- | An __ersatz pointer reference__ is a reference to an __ersatz pointer__, and is evidence that the pointer was
-- /established/ at some point.
newtype a :=>? b
  = W (Weak (a :=> b))

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
dereference (W w) =
  deRefWeak w

{-# COMPLETE (:=>) #-}

pattern (:=>) :: Source a => a -> b -> (a :=> b)
pattern a :=> b <-
  Kv {key = a, value = b}
  where
    key :=> value =
      Kv {key, key#, value, maybeFinalizer}
      where
        key# = primitiveIdentity key
        maybeFinalizer = Nothing

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
dismantle (W w) =
  finalize w

------------------------------------------------------------------------------------------------------------------------
-- Source

-- | The class of types that can be used as the source of an __ersatz pointer__.
--
-- This includes types whose values have a primitive identity ('IORef', 'MVar', and 'TVar'), but may also include
-- product types that contain such a type via user-defined instances.
--
-- ==== __Example user-defined instance__
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
class Source a where
  primitiveIdentity :: a -> PrimitiveIdentity

instance Source (IORef a) where
  primitiveIdentity :: IORef a -> PrimitiveIdentity
  primitiveIdentity (IORef (STRef var#)) = SMutVar# var#

instance Source (MVar a) where
  primitiveIdentity :: MVar a -> PrimitiveIdentity
  primitiveIdentity (MVar var#) = SMVar# var#

instance Source (TVar a) where
  primitiveIdentity :: TVar a -> PrimitiveIdentity
  primitiveIdentity (TVar var#) = STVar# var#

-- | The primitive identity of a value.
data PrimitiveIdentity where
  SMutVar# :: MutVar# s a -> PrimitiveIdentity
  SMVar# :: MVar# s a -> PrimitiveIdentity
  STVar# :: TVar# s a -> PrimitiveIdentity

withPrimitiveIdentity :: PrimitiveIdentity -> (forall (a :: TYPE 'UnliftedRep). a -> r) -> r
withPrimitiveIdentity s k =
  case s of
    SMutVar# var# -> k var#
    SMVar# var# -> k var#
    STVar# var# -> k var#

------------------------------------------------------------------------------------------------------------------------
-- Misc. utils

weak :: forall (k# :: TYPE 'UnliftedRep) v. k# -> v -> IO () -> IO (Weak v)
weak k# v (IO f#) =
  IO \s0# ->
    case mkWeak# k# v f# s0# of
      (# s1#, w# #) -> (# s1#, Weak w# #)

weakNoFinalizer :: forall (k# :: TYPE 'UnliftedRep) v. k# -> v -> IO (Weak v)
weakNoFinalizer k# v =
  IO \s0# ->
    case mkWeakNoFinalizer# k# v s0# of
      (# s1#, w# #) -> (# s1#, Weak w# #)
