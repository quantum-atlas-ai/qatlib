/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

open Matrix Finset Filter
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

def lemma3Statement (d : ℝ) (hd : 0 < d) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in Filter.atTop,
    probOf M (fun b => 4 * d * Real.sqrt ((M : ℝ) * Real.log (M : ℝ))
        ≤ specNorm (circulantMatrix (signVec b)))
      ≤ (4 + ε) / (M : ℝ) ^ (2 * d ^ 2 - 1)

lemma card_boolVec (M : ℕ) : Fintype.card (Fin M → Bool) = 2 ^ M := by
  rw [Fintype.card_fun]
  simp

lemma probOf_nonneg (M : ℕ) (E : (Fin M → Bool) → Prop) : 0 ≤ probOf M E := by
  classical
  unfold probOf
  positivity

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

lemma probOf_empty (M : ℕ) : probOf M (fun _ => False) = 0 := by
  classical
  unfold probOf
  simp

lemma probOf_univ (M : ℕ) : probOf M (fun _ => True) = 1 := by
  classical
  unfold probOf
  simp [Finset.card_univ]

end Qatlib.Papers.NonSparseHam09.MainResults
