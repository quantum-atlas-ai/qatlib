/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic

@[expose] public section


/-! Closed source mathematics; paper algorithm claims retain their separate obligations. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.ShortPathOpt18.MainResults
open Finset

/-- Every site occurs an even number of times in the finite word. The connection to a matrix-product return amplitude requires a separate representation lemma. -/
def EvenFiber {N L : ℕ} (w : Fin L → Fin N) : Prop :=
  ∀ i : Fin N, Even (Fintype.card {j : Fin L // w j = i})

/-- The number of finite words in which every site has even occurrence count. No equality with a matrix moment is included in this definition. -/
def closedWalkCount (N L : ℕ) : ℕ :=
  Fintype.card {w : Fin L → Fin N // EvenFiber w}

/-- The even-occurrence word count divided by `N ^ L`. Identifying this combinatorial quantity with the matrix expectation of `(X / N) ^ L` remains a source bridge obligation. -/
def cubeMoment (N L : ℕ) : ℝ :=
  (closedWalkCount N L : ℝ) / (N : ℝ) ^ L

/-- The product of odd numbers `(L-1)(L-3)…1` for even `L`
(`1` for `L = 0`), the number of pairings of `L` labelled positions. -/
def oddDoubleFactorial (L : ℕ) : ℕ :=
  ∏ k ∈ Finset.range (L / 2), (L - 1 - 2 * k)

/-- The fibers of a walk partition its positions, so their cardinalities sum
to `L`. -/
theorem sum_fiber_card {N L : ℕ} (w : Fin L → Fin N) :
    (∑ i, Fintype.card {j : Fin L // w j = i}) = L := by
  rw [← Fintype.card_sigma]
  rw [Fintype.card_congr (Equiv.sigmaFiberEquiv w), Fintype.card_fin]

/-- If every fiber of a walk is even, its length is even. -/
theorem even_of_evenFiber {N L : ℕ} {w : Fin L → Fin N} (h : EvenFiber w) :
    Even L := by
  rw [← sum_fiber_card w]
  exact Finset.even_sum _ (fun i _ => h i)

/-- For odd word length, the normalized even-occurrence word count is zero because a sum of even fiber cardinalities cannot be odd. No matrix-moment representation is assumed or proved here. -/
theorem source_lemma2_odd_zero (N L : ℕ) (hL : Odd L) : cubeMoment N L = 0 := by
  have hc : closedWalkCount N L = 0 := by
    unfold closedWalkCount
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun x => (Nat.not_even_iff_odd.mpr hL) (even_of_evenFiber x.2)⟩
  simp [cubeMoment, hc]

end Qatlib.Papers.ShortPathOpt18.MainResults
