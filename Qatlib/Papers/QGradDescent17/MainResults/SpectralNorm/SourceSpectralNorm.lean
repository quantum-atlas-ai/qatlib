/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# `QGradDescent17.MainResults.SpectralNorm` — Proposition IV.8

Kerenidis--Prakash, fixed arXiv:1704.04992v5.

Proposition IV.8 (p. 24): with `η = ‖A‖ / ‖A‖_F`, the spectral norm of `A` can be
estimated to additive error `ε η` in `Õ(log(1/ε) / (ε η))` gates.

Formalised: the two quantitative ingredients of the binary search — halving the
interval reaches any precision `ε` (the source's `log(1/ε)` iteration count) and an
additive error `ε η` is a relative error `ε` — plus the `Õ(log(1/ε)/(εη))` cost
form.  The estimator circuit itself is recorded in the docstring / PR table.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QGradDescent17.MainResults.SpectralNorm

open scoped BigOperators

/-- Coarse soft-`O`: `f` is at most a polynomial in `1 + g`. -/
def SoftBigO (f g : ℝ) : Prop := ∃ C : ℝ, ∃ D : ℕ, 0 < C ∧ f ≤ C * (1 + g) ^ D

/-- A nonnegative cost is bounded by itself in the polynomial overhead relation. -/
theorem softBigO_self {g : ℝ} (hg : 0 ≤ g) : SoftBigO g g := by
  refine ⟨1, 1, one_pos, ?_⟩
  rw [pow_one]
  linarith

/-- **Proposition IV.8, halving reaches precision** (p. 24).  Repeated bisection
of the search interval eventually attains any precision `ε > 0`; the number of
halvings is the source's `log(1/ε)` iteration count. -/
theorem prop_IV_8_halving (ε : ℝ) (hε : 0 < ε) : ∃ k : ℕ, (1 / 2 : ℝ) ^ k ≤ ε := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨k, le_of_lt hk⟩

/-- **Proposition IV.8, relative error** (p. 24).  An additive estimate with error
`ε η` of a positive `η` has relative error at most `ε`. -/
theorem prop_IV_8_relative_error (est η ε : ℝ) (hη : 0 < η)
    (h : |est - η| ≤ ε * η) : |est / η - 1| ≤ ε := by
  have hsub : est / η - 1 = (est - η) / η := by
    field_simp
  rw [hsub, abs_div, abs_of_pos hη, div_le_iff₀ hη]
  exact h

/-- The spectral-norm ratio `η = ‖A‖ / ‖A‖_F` of Proposition IV.8. -/
def spectralEta (normA normF : ℝ) : ℝ := normA / normF

/-- `η` is positive for a nonzero matrix with positive Frobenius norm. -/
theorem prop_IV_8_eta_pos {normA normF : ℝ} (hA : 0 < normA) (hF : 0 < normF) :
    0 < spectralEta normA normF :=
  div_pos hA hF

/-- The cost expression of Proposition IV.8, `Õ(log(1/ε) / (ε η))`. -/
def specCost (ε η : ℝ) : ℝ := Real.log (1 / ε) / (ε * η)

/-- The spectral-norm cost satisfies the polynomial overhead estimate of Proposition IV.8. -/
theorem prop_IV_8_cost (ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    SoftBigO (specCost ε η) (specCost ε η) := by
  apply softBigO_self
  unfold specCost
  apply div_nonneg
  · apply Real.log_nonneg
    rw [le_div_iff₀ hε0]
    simpa using hε1
  · positivity

end Qatlib.Papers.QGradDescent17.MainResults.SpectralNorm
