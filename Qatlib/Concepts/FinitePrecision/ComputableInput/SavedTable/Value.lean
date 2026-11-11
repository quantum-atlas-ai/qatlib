/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Data

/-!
# Value semantics of saved table construction

This module implements value gathering and array collection for saved tables. `gather` evaluates
a function along a list, `collect` appends its results to an array, and `tabulate` constructs a
vector from the full finite index list.

The results identify this explicit construction with `Vector.ofFn` and provide array length
invariants used by packet assembly. This is value level infrastructure for finite computational
models of the kind discussed in [KitaevShenVyalyi2002].

## Main statements

* `gather_eq_map`: gathering agrees with list mapping.
* `collect_toList` and `collect_size`: collection preserves order and adds the expected number
  of entries.
* `tabulate_eq`: full finite tabulation agrees with `Vector.ofFn`.

## References

* [Kitaev, Shen and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Value

/-- Evaluates a function at each index in a list, preserving the index order. -/
def gather {ι α : Type} (f : ι → α) : List ι → List α
  | [] => []
  | i::is => let child := f i; let tail := gather f is; child::tail

/-- Gathering values is equal to mapping the function over the index list. -/
theorem gather_eq_map {ι α : Type} (f : ι → α) (is : List ι) :
    gather f is = is.map f := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [gather,List.map_cons,ih]

/-- Appends the elements of a list to an array by repeated pushes. -/
def collect {α : Type} : List α → Array α → Array α
  | [], acc => acc
  | x::xs, acc => collect xs (acc.push x)

/-- Collecting a list into an array appends that list to the array's list representation. -/
theorem collect_toList {α : Type} (xs : List α) (acc : Array α) :
    (collect xs acc).toList = acc.toList++xs := by
  induction xs generalizing acc with
  | nil => simp [collect]
  | cons x xs ih => simp [collect,ih,List.append_assoc]

/-- The size of a collected array is the initial array size plus the list length. -/
theorem collect_size {α : Type} (xs : List α) (acc : Array α) :
    (collect xs acc).size = acc.size+xs.length := by
  simpa using congrArg List.length (collect_toList xs acc)

/-- Constructs a vector by gathering values over the full finite index list and collecting them
into an array. -/
def tabulate {α : Type} {n : ℕ} (is : List (Fin n))
    (hi : is = List.finRange n) (f : Fin n → α) : Vector α n :=
  let saved := gather f is
  ⟨collect saved (Array.emptyWithCapacity n),by
    simp [saved,collect_size,gather_eq_map,hi]⟩

/-- Tabulation over the full finite index list equals `Vector.ofFn`. -/
theorem tabulate_eq {α : Type} {n : ℕ} (is : List (Fin n))
    (hi : is = List.finRange n) (f : Fin n → α) :
    tabulate is hi f = Vector.ofFn f := by
  apply Vector.toList_inj.mp
  simp [tabulate,collect_toList,gather_eq_map,hi,Vector.toList_ofFn,List.ofFn_eq_map]

/-- The saved tail packet type used for constructing a nonempty vector. -/
abbrev Packet := Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.TailPacket

/-- Prepends a value to a saved packet, increasing its tail length by one. -/
def Packet.prepend {α : Type} {n : ℕ} (p : Packet α n) (x : α) : Packet α (n+1) :=
  Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.TailPacket.prepend p x

/-- Collects the head and tail of a saved packet into a vector. -/
def finish {α : Type} {n : ℕ} (p : Packet α n) : Vector α (n+1) :=
  ⟨collect (p.head::p.rest) (Array.emptyWithCapacity (n+1)),by
    simp [collect_size,p.rest_length]⟩

end Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Value
