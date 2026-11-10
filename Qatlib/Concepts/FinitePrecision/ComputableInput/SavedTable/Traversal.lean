/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Data
import Mathlib.Data.Nat.Size

set_option autoImplicit false
open scoped BigOperators

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable

inductive Event
  | child | check | cons | field | ledgerAdd | reserve | push | slot
  deriving DecidableEq, Repr

abbrev Counts := Event → ℕ

structure Observed (α : Type) where
  arithmetic : Run α
  counts : Counts

def lift {α : Type} (q : Run α) : Observed α := ⟨q,0⟩

structure Generated (α : Type) where
  runs : List (Run α)
  nested : Counts
  checks : ℕ
  items : ℕ

def generate {ι α : Type} (f : ι → Observed α) : List ι → Generated α
  | [] => ⟨[],0,1,0⟩
  | i :: is =>
    let child := f i
    let tail := generate f is
    ⟨child.arithmetic :: tail.runs,child.counts+tail.nested,
      tail.checks+1,tail.items+1⟩

theorem generate_runs {ι α : Type} (f : ι → Observed α) (is : List ι) :
    (generate f is).runs = is.map (fun i => (f i).arithmetic) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [generate,List.map_cons,ih]

theorem generate_nested {ι α : Type} (f : ι → Observed α) (is : List ι)
    (e : Event) :
    (generate f is).nested e = (is.map (fun i => (f i).counts e)).sum := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [generate,ih]

theorem generate_counts {ι α : Type} (f : ι → Observed α) (is : List ι) :
    (generate f is).checks = is.length+1 ∧
    (generate f is).items = is.length := by
  induction is with
  | nil => exact ⟨rfl,rfl⟩
  | cons i is ih => simp [generate,ih.1,ih.2]

structure Projected (α : Type) where
  values : List α
  checks : ℕ
  reads : ℕ

def project {α : Type} : List (Run α) → Projected α
  | [] => ⟨[],1,0⟩
  | q :: qs =>
    let value := q.value
    let tail := project qs
    ⟨value :: tail.values,tail.checks+1,tail.reads+1⟩

theorem project_spec {α : Type} (qs : List (Run α)) :
    (project qs).values = qs.map (fun q => q.value) ∧
    (project qs).checks = qs.length+1 ∧
    (project qs).reads = qs.length := by
  induction qs with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons q qs ih => simp [project,ih.1,ih.2.1,ih.2.2]

structure Summed where
  value : ℕ
  checks : ℕ
  reads : ℕ

def sumField {α : Type} (field : Run α → ℕ) :
    List (Run α) → Summed
  | [] => ⟨0,1,0⟩
  | q :: qs =>
    let x := field q
    let tail := sumField field qs
    ⟨x+tail.value,tail.checks+1,tail.reads+1⟩

theorem sumField_spec {α : Type} (field : Run α → ℕ)
    (qs : List (Run α)) :
    (sumField field qs).value = (qs.map field).sum ∧
    (sumField field qs).checks = qs.length+1 ∧
    (sumField field qs).reads = qs.length := by
  induction qs with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons q qs ih => simp [sumField,ih.1,ih.2.1,ih.2.2]

theorem sumField_bound {α : Type} (field : Run α → ℕ)
    (qs : List (Run α)) (C : ℕ)
    (h : ∀ q ∈ qs, field q ≤ C) :
    (sumField field qs).value ≤ qs.length*C := by
  revert h
  induction qs with
  | nil => intro h; simp [sumField]
  | cons q qs ih =>
    intro h
    have hq : field q ≤ C := h q (by simp)
    have ht : ∀ x ∈ qs, field x ≤ C := by
      intro x hx
      exact h x (by simp [hx])
    calc
      (sumField field (q::qs)).value = field q+(sumField field qs).value := rfl
      _ ≤ C+qs.length*C := Nat.add_le_add hq (ih ht)
      _ = (q::qs).length*C := by simp [Nat.add_mul,Nat.add_comm]

theorem sumField_suffix_bound {α : Type} (field : Run α → ℕ)
    (qs suffix : List (Run α)) (C : ℕ)
    (h : ∀ q ∈ qs, field q ≤ C)
    (hSuffix : ∃ pre, pre++suffix=qs) :
    (sumField field suffix).value ≤ qs.length*C ∧
    (sumField field suffix).value.size ≤ (qs.length*C).size := by
  have hs : (sumField field suffix).value ≤ (sumField field qs).value := by
    rcases hSuffix with ⟨pre,rfl⟩
    rw [(sumField_spec field suffix).1,(sumField_spec field (pre++suffix)).1]
    simp only [List.map_append,List.sum_append]
    omega
  have hsum := hs.trans (sumField_bound field qs C h)
  exact ⟨hsum,Nat.size_le_size hsum⟩

theorem sum_map_indices {ι : Type} [DecidableEq ι] (is : List ι)
    (f : ι → ℕ) (h : is.Nodup) :
    (is.map f).sum = ∑ i ∈ is.toFinset, f i := by
  induction is with
  | nil => simp
  | cons i is ih =>
    have hi := List.nodup_cons.mp h
    simp only [List.map_cons,List.sum_cons,List.toFinset_cons]
    rw [Finset.sum_insert (by simpa using hi.1),ih hi.2]

theorem sum_finRange {n : ℕ} (f : Fin n → ℕ) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  simpa using sum_map_indices (List.finRange n) f (List.nodup_finRange n)

end Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable
