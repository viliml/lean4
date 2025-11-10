/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Partial
public import Init.Data.Iterators.Consumers.Monadic.Collect

@[expose] public section

/-!
# Collectors

This module provides consumers that collect the values emitted by an iterator in a data structure.
Concretely, the following operations are provided:

* `Iter.toList`, collecting the values in a list
* `Iter.toListRev`, collecting the values in a list in reverse order but more efficiently
* `Iter.toArray`, collecting the values in an array

Some operations are implemented using the `IteratorCollect` and `IteratorCollectPartial`
typeclasses.
-/

namespace Std.Iterators

@[always_inline, inline, inherit_doc IterM.toArray]
def Iter.toArray {α : Type w} {β : Type w}
    [Iterator α id β] [Finite α id] [IteratorCollect α id id] (it : Iter (α := α) β) : Array β :=
  it.toIterM.toArray

@[always_inline, inline, inherit_doc IterM.Partial.toArray]
def Iter.Partial.toArray {α : Type w} {β : Type w}
    [Iterator α id β] [IteratorCollectPartial α id id] (it : Iter.Partial (α := α) β) : Array β :=
  it.it.toIterM.allowNontermination.toArray

@[always_inline, inline, inherit_doc IterM.toListRev]
def Iter.toListRev {α : Type w} {β : Type w}
    [Iterator α id β] [Finite α id] (it : Iter (α := α) β) : List β :=
  it.toIterM.toListRev

@[always_inline, inline, inherit_doc IterM.Partial.toListRev]
def Iter.Partial.toListRev {α : Type w} {β : Type w}
    [Iterator α id β] (it : Iter.Partial (α := α) β) : List β :=
  it.it.toIterM.allowNontermination.toListRev

@[always_inline, inline, inherit_doc IterM.toList]
def Iter.toList {α : Type w} {β : Type w}
    [Iterator α id β] [Finite α id] [IteratorCollect α id id] (it : Iter (α := α) β) : List β :=
  it.toIterM.toList

@[always_inline, inline, inherit_doc IterM.Partial.toList]
def Iter.Partial.toList {α : Type w} {β : Type w}
    [Iterator α id β] [IteratorCollectPartial α id id] (it : Iter.Partial (α := α) β) : List β :=
  it.it.toIterM.allowNontermination.toList

end Std.Iterators
