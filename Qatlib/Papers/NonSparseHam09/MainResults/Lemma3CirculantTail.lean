/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Defs

/-!
# Circulant norm tail proposition and finite probabilities

Defines `lemma3Statement`, an eventual tail bound for the spectral norm of the random sign
circulant matrix. The proved lemmas count Boolean strings and establish the range and boundary
values of the uniform counting probability `probOf`. See [ChildsKothari2010] for the surrounding
analysis.

## Main statements

* `lemma3Statement`: For positive `d`, the proposition that, for every positive `ε` and
  eventually in `M`, the probability of circulant spectral norm at least `4 * d * √(M * log M)`
  is at most `(4 + ε) / M^(2 * d² - 1)`.
* `card_boolVec`: The type of length-`M` Boolean strings has cardinality `2^M`.
* `probOf_le_one`: The uniform counting probability `probOf M E` is at most one.

## References

* [Childs and Kothari, 2010][ChildsKothari2010]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

open Matrix Finset Filter
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

/-- For positive `d`, the proposition that, for every positive `ε` and eventually in `M`, the
probability of circulant spectral norm at least `4 * d * √(M * log M)` is at most `(4 + ε) /
M^(2 * d² - 1)`. -/
def lemma3Statement (d : ℝ) (hd : 0 < d) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in Filter.atTop,
    probOf M (fun b => 4 * d * Real.sqrt ((M : ℝ) * Real.log (M : ℝ))
        ≤ specNorm (circulantMatrix (signVec b)))
      ≤ (4 + ε) / (M : ℝ) ^ (2 * d ^ 2 - 1)

/-- The type of length-`M` Boolean strings has cardinality `2^M` [ChildsKothari2010]. -/
lemma card_boolVec (M : ℕ) : Fintype.card (Fin M → Bool) = 2 ^ M := by
  rw [Fintype.card_fun]
  simp

/-- The uniform counting probability `probOf M E` is nonnegative [ChildsKothari2010]. -/
lemma probOf_nonneg (M : ℕ) (E : (Fin M → Bool) → Prop) : 0 ≤ probOf M E := by
  classical
  unfold probOf
  positivity

/-- The uniform counting probability `probOf M E` is at most one [ChildsKothari2010]. -/
lemma probOf_le_one (M : ℕ) (E : (Fin M → Bool) → Prop) : probOf M E ≤ 1 := by
  classical
  unfold probOf
  have hle : ((Finset.univ.filter (fun b : Fin M → Bool => E b)).card : ℝ) ≤ (2 : ℝ) ^ M := by
    have hc : (Finset.univ.filter (fun b : Fin M → Bool => E b)).card ≤ 2 ^ M := by
      calc (Finset.univ.filter (fun b : Fin M → Bool => E b)).card
          ≤ (Finset.univ : Finset (Fin M → Bool)).card := Finset.card_filter_le _ _
        _ = 2 ^ M := by rw [Finset.card_univ, card_boolVec]
    exact_mod_cast hc
  rw [div_le_one (by positivity)]
  exact hle

/-- The uniform counting probability of the false event is zero [ChildsKothari2010]. -/
lemma probOf_empty (M : ℕ) : probOf M (fun _ => False) = 0 := by
  classical
  unfold probOf
  simp

/-- The uniform counting probability of the true event is one [ChildsKothari2010]. -/
lemma probOf_univ (M : ℕ) : probOf M (fun _ => True) = 1 := by
  classical
  unfold probOf
  simp [Finset.card_univ]

end Qatlib.Papers.NonSparseHam09.MainResults
