/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Basic
import Init.Data.Vector.InsertIdx
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Data and collection counts for saved tables

`Run` stores a value with work and cell counts, while `TailPacket` stores a nonempty sequence
with a certified tail length. Its list and vector conversions preserve the entries and the total
length.

`collect` appends a list to an array and records recursive calls and pushes. `finish` converts a
packet into a vector through this collector, with exact counts supplied by `finish_spec`.

## Main statements

* `TailPacket.toVector_prepend`: compatibility of packet prepending with vector insertion.
* `collect_spec`: the collected entries and exact call and push counts.
* `finish_spec`: the resulting vector and exact collection counts.

For background on classical computation and resource bounds, see [KitaevShenVyalyi2002].

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false
open scoped BigOperators

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable

/-- A value together with natural-number counts for work and cells. -/
structure Run (α : Type) where
  value : α
  work : ℕ
  cells : ℕ
  deriving Repr

/-- A nonempty sequence represented by a head and a list tail of certified length `n`. -/
structure TailPacket (α : Type) (n : ℕ) where
  head : α
  rest : List α
  rest_length : rest.length = n

namespace TailPacket
variable {α : Type} {n : ℕ}

/-- Convert a tail packet to the list consisting of its head followed by its tail. -/
def toList (p : TailPacket α n) : List α := p.head :: p.rest

/-- The list associated with a tail packet has length `n + 1`. -/
@[simp] theorem toList_length (p : TailPacket α n) :
    p.toList.length = n+1 := by simp [toList,p.rest_length]

/-- Prepend `x` to a tail packet, increasing its certified tail length by one. -/
def prepend (p : TailPacket α n) (x : α) : TailPacket α (n+1) :=
  ⟨x,p.head :: p.rest,by simp [p.rest_length]⟩

/-- Convert a tail packet to a vector of length `n + 1` through its list representation. -/
def toVector (p : TailPacket α n) : Vector α (n+1) :=
  ⟨p.toList.toArray,by simp⟩

/-- Converting a packet to a vector and then to a list gives its original list representation. -/
@[simp] theorem toVector_toList (p : TailPacket α n) :
    p.toVector.toList = p.toList := rfl

/-- The entry at index zero of a packet's vector representation is its head. -/
@[simp] theorem toVector_head (p : TailPacket α n) :
    p.toVector[0] = p.head := by simp [toVector,toList]

/-- Converting a prepended packet to a vector agrees with inserting the new entry at index zero
of the original vector. -/
theorem toVector_prepend (p : TailPacket α n) (x : α) :
    (p.prepend x).toVector = p.toVector.insertIdx 0 x := by
  apply Vector.toList_inj.mp
  rw [Vector.toList_insertIdx]
  rfl

end TailPacket

/-- A value together with recorded recursive-call and array-push counts. -/
structure Collection (α : Type) where
  value : α
  calls : ℕ
  pushes : ℕ

/-- Append the entries of a list to an array by recursive pushes, recording the number of calls
and pushes. -/
def collect {α : Type} : List α → Array α → Collection (Array α)
  | [], acc => ⟨acc,1,0⟩
  | x :: xs, acc =>
    let child := collect xs (acc.push x)
    ⟨child.value,child.calls+1,child.pushes+1⟩

/-- Collection appends exactly `xs` to the accumulator entries, uses `xs.length + 1` recursive
calls, and records `xs.length` pushes. -/
theorem collect_spec {α : Type} (xs : List α) (acc : Array α) :
    (collect xs acc).value.toList = acc.toList ++ xs ∧
    (collect xs acc).calls = xs.length+1 ∧
    (collect xs acc).pushes = xs.length := by
  induction xs generalizing acc with
  | nil => simp [collect]
  | cons x xs ih =>
    rcases ih (acc.push x) with ⟨hv,hc,hp⟩
    simp [collect,hv,hc,hp,List.append_assoc]

/-- The array produced by collection has size `acc.size + xs.length`. -/
theorem collect_size {α : Type} (xs : List α) (acc : Array α) :
    (collect xs acc).value.size = acc.size+xs.length := by
  have h := congrArg List.length (collect_spec xs acc).1
  simpa using h

/-- Collect a packet's entries into an initially empty array and return the resulting vector
with its collection counts. -/
def finish {α : Type} {n : ℕ} (p : TailPacket α n) :
    Collection (Vector α (n+1)) :=
  let xs := p.toList
  let out := collect xs (Array.emptyWithCapacity (n+1))
  ⟨⟨out.value,by simp [out,xs,collect_size]⟩,out.calls,out.pushes⟩

/-- Finishing a packet gives `p.toVector`, with exactly `n + 2` recursive calls and `n + 1`
pushes. -/
theorem finish_spec {α : Type} {n : ℕ} (p : TailPacket α n) :
    (finish p).value = p.toVector ∧
    (finish p).calls = n+2 ∧ (finish p).pushes = n+1 := by
  have h := collect_spec p.toList (Array.emptyWithCapacity (n+1))
  refine ⟨?_,?_,?_⟩
  · apply Vector.toList_inj.mp
    simpa [finish] using h.1
  · simpa [finish,Nat.add_assoc] using h.2.1
  · simpa [finish] using h.2.2

end Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable
