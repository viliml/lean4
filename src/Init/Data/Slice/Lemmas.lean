/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Slice.Operations
import all Init.Data.Slice.Operations
import Init.Data.Iterators.Lemmas.Consumers

public section

namespace Std.Slice

open Std.Iterators

variable {γ : Type u} {β : Type v}

theorem Internal.iter_eq_toIteratorIter {γ : Type u} {s : Slice γ}
    [ToIterator s id β] :
    Internal.iter s = ToIterator.iter s :=
  (rfl)

theorem Internal.size_eq_size_iter {s : Slice γ} [ToIterator s id β]
    [Iterator (ToIterator.State s id) id β] [IteratorSize (ToIterator.State s id) id] :
    s.size = (Internal.iter s).size :=
  (rfl)

theorem Internal.toArray_eq_toArray_iter {s : Slice γ} [ToIterator s id β]
    [Iterator (ToIterator.State s id) id β] [IteratorCollect (ToIterator.State s id) id id]
    [Finite (ToIterator.State s id) id] :
    s.toArray = (Internal.iter s).toArray :=
  (rfl)

theorem Internal.toList_eq_toList_iter {s : Slice γ} [ToIterator s id β]
    [Iterator (ToIterator.State s id) id β] [IteratorCollect (ToIterator.State s id) id id]
    [Finite (ToIterator.State s id) id] :
    s.toList = (Internal.iter s).toList :=
  (rfl)

theorem Internal.toListRev_eq_toListRev_iter {s : Slice γ} [ToIterator s id β]
    [Iterator (ToIterator.State s id) id β] [Finite (ToIterator.State s id) id] :
    s.toListRev = (Internal.iter s).toListRev :=
  (rfl)

@[simp]
theorem size_toArray_eq_size {s : Slice γ} [ToIterator s id β]
    [Iterator (ToIterator.State s id) id β] [IteratorSize (ToIterator.State s id) id]
    [IteratorCollect (ToIterator.State s id) id id] [Finite (ToIterator.State s id) id]
    [LawfulIteratorSize (ToIterator.State s id)]
    [LawfulIteratorCollect (ToIterator.State s id) id id] :
    s.toArray.size = s.size := by
  simp [Internal.size_eq_size_iter, Internal.toArray_eq_toArray_iter,
    Iter.size_toArray_eq_size]

@[simp]
theorem length_toList_eq_size {s : Slice γ} [ToIterator s id β]
    [Iterator (ToIterator.State s id) id β] [IteratorSize (ToIterator.State s id) id]
    [IteratorCollect (ToIterator.State s id) id id] [Finite (ToIterator.State s id) id]
    [LawfulIteratorSize (ToIterator.State s id)]
    [LawfulIteratorCollect (ToIterator.State s id) id id] :
    s.toList.length = s.size := by
  simp [Internal.size_eq_size_iter, Internal.toList_eq_toList_iter,
    Iter.length_toList_eq_size]

@[simp]
theorem length_toListRev_eq_size {s : Slice γ} [ToIterator s id β]
    [Iterator (ToIterator.State s id) id β] [IteratorSize (ToIterator.State s id) id]
    [IteratorCollect (ToIterator.State s id) id id] [Finite (ToIterator.State s id) id]
    [LawfulIteratorSize (ToIterator.State s id)]
    [LawfulIteratorCollect (ToIterator.State s id) id id] :
    s.toListRev.length = s.size := by
  simp [Internal.size_eq_size_iter, Internal.toListRev_eq_toListRev_iter,
    Iter.length_toListRev_eq_size]

end Std.Slice
