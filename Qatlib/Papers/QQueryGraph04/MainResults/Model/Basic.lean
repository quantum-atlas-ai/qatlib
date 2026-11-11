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

/-!
# Combinatorial models and graph query costs

This module defines good candidates for selection by value and type, together with finite counts
and degree bounds. It also records the real-valued search, connectivity, Borůvka, directed-tree,
and tier cost expressions used by the graph-query estimates.

The source paper is [DurrEtAl2006].

## Main statements

* `isGood_iff`: A candidate is good exactly when it satisfies `GoodKnown` or `GoodUnknown`.
* `sum_sqrt_totalDegree_le`: If each set satisfies `DegreeBound` and the sum of its
  cardinalities is at most n, then the sum of square roots of its total degrees is at most n.
* `boruvkaCost`: The sum of `boruvkaIterCost` over the first M phases.

## References

* [Dürr et al., 2006][DurrEtAl2006]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QQueryGraph04.MainResults.Model

open Finset

variable {α β : Type*}

/-- A candidate improves a selected element of its own type, or has an unrepresented type and
improves some selected value. -/
def IsGood [DecidableEq β] (f : α → ℕ) (g : α → β) (I : Finset α) (j : α) : Prop :=
  (∃ i ∈ I, g j = g i ∧ f j < f i) ∨ (g j ∉ I.image g ∧ ∃ i ∈ I, f j < f i)

/-- A candidate has the same type as a selected element and a strictly smaller value. -/
def GoodKnown [DecidableEq β] (f : α → ℕ) (g : α → β) (I : Finset α) (j : α) : Prop :=
  ∃ i ∈ I, g j = g i ∧ f j < f i

/-- A candidate has an unrepresented type and a strictly smaller value than some selected
element. -/
def GoodUnknown [DecidableEq β] (f : α → ℕ) (g : α → β) (I : Finset α) (j : α) : Prop :=
  g j ∉ I.image g ∧ ∃ i ∈ I, f j < f i

/-- A candidate is good exactly when it satisfies `GoodKnown` or `GoodUnknown`. -/
theorem isGood_iff [DecidableEq β] (f : α → ℕ) (g : α → β) (I : Finset α) (j : α) :
    IsGood f g I j ↔ GoodKnown f g I j ∨ GoodUnknown f g I j := Iff.rfl

/-- The finite set of all good candidates relative to the selected set `I`. -/
noncomputable def goodSet [Fintype α] [DecidableEq β] (f : α → ℕ) (g : α → β)
    (I : Finset α) : Finset α := by
  classical
  exact univ.filter fun j => IsGood f g I j

/-- The number of good candidates relative to the selected set `I`. -/
noncomputable def goodCount [Fintype α] [DecidableEq β] (f : α → ℕ) (g : α → β)
    (I : Finset α) : ℕ :=
  (goodSet f g I).card

/-- Membership in `goodSet` is equivalent to the predicate `IsGood`. -/
theorem mem_goodSet [Fintype α] [DecidableEq β] (f : α → ℕ) (g : α → β)
    (I : Finset α) (j : α) : j ∈ goodSet f g I ↔ IsGood f g I j := by
  classical
  simp [goodSet]

/-- The good-candidate count equals the cardinality of `goodSet`. -/
theorem goodCount_eq_card_goodSet [Fintype α] [DecidableEq β] (f : α → ℕ) (g : α → β)
    (I : Finset α) : goodCount f g I = (goodSet f g I).card := rfl

/-- The number of elements of `S` whose value is at most `ymid`. -/
def lowCount (f : α → ℕ) (S : Finset α) (ymid : ℕ) : ℕ :=
  (S.filter fun x => f x ≤ ymid).card

/-- The number of elements below a value threshold is at most the size of the set. -/
theorem lowCount_le_card (f : α → ℕ) (S : Finset α) (ymid : ℕ) :
    lowCount f S ymid ≤ S.card := by
  unfold lowCount
  exact Finset.card_filter_le _ _

/-- The number of elements below a fixed value threshold is monotone under inclusion of finite
sets. -/
theorem lowCount_mono (f : α → ℕ) {S T : Finset α} (h : S ⊆ T) (ymid : ℕ) :
    lowCount f S ymid ≤ lowCount f T ymid := by
  unfold lowCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- Membership in the threshold filter is equivalent to membership in `S` and value at most
`ymid`. -/
theorem mem_low_iff (f : α → ℕ) (S : Finset α) (ymid : ℕ) (x : α) :
    x ∈ S.filter (fun z => f z ≤ ymid) ↔ x ∈ S ∧ f x ≤ ymid := by
  simp

/-- Replacing an element above the threshold by a new element at or below it increases
`lowCount` by one [DurrEtAl2006]. -/
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

/-- The number of distinct types in the image of `g` on the finite ambient type. -/
noncomputable def typeCount [Fintype α] [DecidableEq β] (g : α → β) : ℕ := (univ.image g).card

/-- The minimum of the requested selection size and the number of available types. -/
def dOf (d' e : ℕ) : ℕ := min d' e

/-- The sum of the assigned vertex degrees over a finite set. -/
def totalDegree {V : Type*} (deg : V → ℕ) (C : Finset V) : ℕ := ∑ i ∈ C, deg i

/-- The total degree of a finite vertex set is at most the square of its cardinality. -/
def DegreeBound {V : Type*} (deg : V → ℕ) (C : Finset V) : Prop :=
  totalDegree deg C ≤ C.card ^ 2

/-- If each set satisfies `DegreeBound` and the sum of its cardinalities is at most n, then the
sum of square roots of its total degrees is at most n [DurrEtAl2006]. -/
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

/-- The search cost expression √(D/t), using real division. -/
noncomputable def searchCost (D t : ℕ) : ℝ := Real.sqrt ((D : ℝ) / (t : ℝ))

/-- The matrix-connectivity iteration cost expression √(n²/(k − 1)). -/
noncomputable def matrixConnectivityIterCost (n k : ℕ) : ℝ :=
  Real.sqrt (((n : ℝ) ^ 2) / ((k : ℝ) - 1))

/-- The sum of √(n²/(j + 1)) over j < n − 1. -/
noncomputable def matrixConnectivityCost (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n - 1), Real.sqrt (((n : ℝ) ^ 2) / ((j : ℝ) + 1))

/-- The Borůvka phase cost expression (ℓ + 3)√(nm/2^ℓ). -/
noncomputable def boruvkaIterCost (n m ℓ : ℕ) : ℝ :=
  ((ℓ : ℝ) + 3) * Real.sqrt (((n : ℝ) * (m : ℝ)) / (2 : ℝ) ^ ℓ)

/-- The sum of `boruvkaIterCost` over the first M phases. -/
noncomputable def boruvkaCost (M n m : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.range M, boruvkaIterCost n m ℓ

/-- The sum of the phase error allowances 1/2^(ℓ + 3) over ℓ < M. -/
noncomputable def boruvkaError (M : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.range M, (1 : ℝ) / (2 : ℝ) ^ (ℓ + 3)

/-- The vertex cost expression √(b·d·logFactor) for directed-tree construction. -/
noncomputable def directedTreeVertexCost (logFactor b d : ℕ) : ℝ :=
  Real.sqrt ((b : ℝ) * (d : ℝ) * (logFactor : ℝ))

/-- The sum of the directed-tree vertex cost expressions over all vertices. -/
noncomputable def directedTreeCost {V : Type*} [Fintype V] (logFactor : ℕ)
    (b d : V → ℕ) : ℝ :=
  ∑ u, directedTreeVertexCost logFactor (b u) (d u)

/-- The directed-tree error expression (2n − 1)/(20n). -/
noncomputable def directedTreeError (n : ℕ) : ℝ := ((2 : ℝ) * n - 1) / (20 * n)

/-- The tier failure expression 2ⁱ/2^(2^(i + 2)). -/
noncomputable def tierFailure (i : ℕ) : ℝ := (2 : ℝ) ^ i / (2 : ℝ) ^ (2 ^ (i + 2))

/-- The tier iteration cost expression 2^(3i/4)√n. -/
noncomputable def tierIterCost (n i : ℕ) : ℝ := Real.rpow 2 ((3 : ℝ) * i / 4) * Real.sqrt n

end Qatlib.Papers.QQueryGraph04.MainResults.Model
