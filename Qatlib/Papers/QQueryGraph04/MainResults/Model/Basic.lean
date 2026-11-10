/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.QQueryGraph04.MainResults.Model

open Finset

variable {α β : Type*}

def IsGood [DecidableEq β] (f : α → ℕ) (g : α → β) (I : Finset α) (j : α) : Prop :=
  (∃ i ∈ I, g j = g i ∧ f j < f i) ∨ (g j ∉ I.image g ∧ ∃ i ∈ I, f j < f i)

def GoodKnown [DecidableEq β] (f : α → ℕ) (g : α → β) (I : Finset α) (j : α) : Prop :=
  ∃ i ∈ I, g j = g i ∧ f j < f i

def GoodUnknown [DecidableEq β] (f : α → ℕ) (g : α → β) (I : Finset α) (j : α) : Prop :=
  g j ∉ I.image g ∧ ∃ i ∈ I, f j < f i

theorem isGood_iff [DecidableEq β] (f : α → ℕ) (g : α → β) (I : Finset α) (j : α) :
    IsGood f g I j ↔ GoodKnown f g I j ∨ GoodUnknown f g I j := Iff.rfl

noncomputable def goodSet [Fintype α] [DecidableEq β] (f : α → ℕ) (g : α → β)
    (I : Finset α) : Finset α := by
  classical
  exact univ.filter fun j => IsGood f g I j

noncomputable def goodCount [Fintype α] [DecidableEq β] (f : α → ℕ) (g : α → β)
    (I : Finset α) : ℕ :=
  (goodSet f g I).card

theorem mem_goodSet [Fintype α] [DecidableEq β] (f : α → ℕ) (g : α → β)
    (I : Finset α) (j : α) : j ∈ goodSet f g I ↔ IsGood f g I j := by
  classical
  simp [goodSet]

theorem goodCount_eq_card_goodSet [Fintype α] [DecidableEq β] (f : α → ℕ) (g : α → β)
    (I : Finset α) : goodCount f g I = (goodSet f g I).card := rfl

def lowCount (f : α → ℕ) (S : Finset α) (ymid : ℕ) : ℕ :=
  (S.filter fun x => f x ≤ ymid).card

theorem lowCount_le_card (f : α → ℕ) (S : Finset α) (ymid : ℕ) :
    lowCount f S ymid ≤ S.card := by
  unfold lowCount
  exact Finset.card_filter_le _ _

theorem lowCount_mono (f : α → ℕ) {S T : Finset α} (h : S ⊆ T) (ymid : ℕ) :
    lowCount f S ymid ≤ lowCount f T ymid := by
  unfold lowCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem mem_low_iff (f : α → ℕ) (S : Finset α) (ymid : ℕ) (x : α) :
    x ∈ S.filter (fun z => f z ≤ ymid) ↔ x ∈ S ∧ f x ≤ ymid := by
  simp

theorem lowCount_insert_erase_of_not_low [DecidableEq α] (f : α → ℕ) (S : Finset α) (ymid : ℕ)
    (i j : α) (hi : i ∈ S) (hj : j ∉ S) (hyj : f j ≤ ymid)
    (hyi : ymid < f i) :
    lowCount f (insert j (S.erase i)) ymid = lowCount f S ymid + 1 := by
  unfold lowCount
  have hfil : (insert j (S.erase i)).filter (fun z => f z ≤ ymid) =
      insert j ((S.erase i).filter fun z => f z ≤ ymid) := by
    rw [Finset.filter_insert]
    simp [hyj]
  rw [hfil]
  have hnot : j ∉ (S.erase i).filter (fun z => f z ≤ ymid) := by
    simp [hj]
  rw [Finset.card_insert_of_notMem hnot]
  have herase : (S.erase i).filter (fun z => f z ≤ ymid) = S.filter (fun z => f z ≤ ymid) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hz1, hz2⟩, hz3⟩
      exact ⟨hz2, hz3⟩
    · rintro ⟨hzS, hzlow⟩
      refine ⟨⟨?_, hzS⟩, hzlow⟩
      rintro rfl
      exact absurd hzlow (not_le.mpr hyi)
  rw [herase]

noncomputable def typeCount [Fintype α] [DecidableEq β] (g : α → β) : ℕ := (univ.image g).card

def dOf (d' e : ℕ) : ℕ := min d' e

def totalDegree {V : Type*} (deg : V → ℕ) (C : Finset V) : ℕ := ∑ i ∈ C, deg i

def DegreeBound {V : Type*} (deg : V → ℕ) (C : Finset V) : Prop :=
  totalDegree deg C ≤ C.card ^ 2

theorem sum_sqrt_totalDegree_le
    {ι V : Type*} [Fintype ι] (deg : V → ℕ) (C : ι → Finset V) (n : ℕ)
    (hbound : ∀ i, DegreeBound deg (C i))
    (hcover : (∑ i, (C i).card) ≤ n) :
    (∑ i, Real.sqrt ((totalDegree deg (C i) : ℝ))) ≤ n := by
  have hterm : ∀ i, Real.sqrt ((totalDegree deg (C i) : ℝ)) ≤ (C i).card := by
    intro i
    have h1 : ((totalDegree deg (C i) : ℝ)) ≤ ((C i).card : ℝ) ^ 2 := by
      exact_mod_cast hbound i
    have h2 : Real.sqrt ((totalDegree deg (C i) : ℝ)) ≤ Real.sqrt (((C i).card : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (Nat.cast_nonneg _)] at h2
  calc (∑ i, Real.sqrt ((totalDegree deg (C i) : ℝ)))
      ≤ ∑ i, ((C i).card : ℝ) := Finset.sum_le_sum fun i _ => hterm i
    _ = ((∑ i, (C i).card : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (n : ℝ) := by exact_mod_cast hcover

noncomputable def searchCost (D t : ℕ) : ℝ := Real.sqrt ((D : ℝ) / (t : ℝ))

noncomputable def matrixConnectivityIterCost (n k : ℕ) : ℝ :=
  Real.sqrt (((n : ℝ) ^ 2) / ((k : ℝ) - 1))

noncomputable def matrixConnectivityCost (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n - 1), Real.sqrt (((n : ℝ) ^ 2) / ((j : ℝ) + 1))

noncomputable def boruvkaIterCost (n m ℓ : ℕ) : ℝ :=
  ((ℓ : ℝ) + 3) * Real.sqrt (((n : ℝ) * (m : ℝ)) / (2 : ℝ) ^ ℓ)

noncomputable def boruvkaCost (M n m : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.range M, boruvkaIterCost n m ℓ

noncomputable def boruvkaError (M : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.range M, (1 : ℝ) / (2 : ℝ) ^ (ℓ + 3)

noncomputable def directedTreeVertexCost (logFactor b d : ℕ) : ℝ :=
  Real.sqrt ((b : ℝ) * (d : ℝ) * (logFactor : ℝ))

noncomputable def directedTreeCost {V : Type*} [Fintype V] (logFactor : ℕ)
    (b d : V → ℕ) : ℝ :=
  ∑ u, directedTreeVertexCost logFactor (b u) (d u)

noncomputable def directedTreeError (n : ℕ) : ℝ := ((2 : ℝ) * n - 1) / (20 * n)

noncomputable def tierFailure (i : ℕ) : ℝ := (2 : ℝ) ^ i / (2 : ℝ) ^ (2 ^ (i + 2))

noncomputable def tierIterCost (n i : ℕ) : ℝ := Real.rpow 2 ((3 : ℝ) * i / 4) * Real.sqrt n

end Qatlib.Papers.QQueryGraph04.MainResults.Model
