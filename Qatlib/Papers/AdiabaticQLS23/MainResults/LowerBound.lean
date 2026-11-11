/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Neumann expansions and conditional query lower bounds

Proves the Neumann-series identities for `adiabaticMatrix c U` and the scalar lower-bound
implications used in the reduction discussed in [CostaEtAl2025]. The inverse expansion requires
the norm of `c • U` to be less than one.

The theorems `query_lower_bound_chain` and `query_lower_bound_chain_scaled` combine assumed
reduction and parameter inequalities to obtain a query lower bound proportional to `κ * log (1 /
ε)`.

## Main statements

* `adiabaticMatrix_inv_eq_paper_series`: Expands the inverse as scalar-weighted powers of `U`.
* `query_lower_bound_chain_scaled`: Combines the supplied reduction inequalities with explicit
  scaling constants.

## References

* [Costa et al., 2025][CostaEtAl2025]
-/

set_option autoImplicit false

namespace Qatlib.Papers.AdiabaticQLS23.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The matrix `1 - (c : ℂ) • U` used in the inverse-series construction. -/
def adiabaticMatrix (c : ℝ) (U : Matrix N N ℂ) : Matrix N N ℂ :=
  1 - (c : ℂ) • U

/-- If `‖(c : ℂ) • U‖ < 1`, the Neumann series multiplied on the right by `adiabaticMatrix c U`
equals the identity. See [CostaEtAl2025]. -/
theorem neumann_series_mul (U : Matrix N N ℂ) (c : ℝ)
    (h : ‖(c : ℂ) • U‖ < 1) :
    (∑' k : ℕ, ((c : ℂ) • U) ^ k) * adiabaticMatrix c U = 1 := by
  unfold adiabaticMatrix
  exact geom_series_mul_neg _ h

/-- If `‖(c : ℂ) • U‖ < 1`, the inverse of `adiabaticMatrix c U` is the sum of the powers of `(c
: ℂ) • U`. -/
theorem adiabaticMatrix_inv_eq_series (U : Matrix N N ℂ) (c : ℝ)
    (h : ‖(c : ℂ) • U‖ < 1) :
    (adiabaticMatrix c U)⁻¹ = ∑' k : ℕ, ((c : ℂ) • U) ^ k :=
  Matrix.inv_eq_left_inv (neumann_series_mul U c h)

/-- The `k`th power of `(c : ℂ) • U` equals `((c : ℂ) ^ k) • U ^ k`. -/
theorem smul_pow (c : ℝ) (U : Matrix N N ℂ) (k : ℕ) :
    ((c : ℂ) • U) ^ k = ((c : ℂ) ^ k) • U ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, pow_succ, smul_mul_smul_comm, pow_succ]

/-- If `‖(c : ℂ) • U‖ < 1`, the inverse of `adiabaticMatrix c U` is `∑' k, ((c : ℂ) ^ k) • U ^
k`. See [CostaEtAl2025]. -/
theorem adiabaticMatrix_inv_eq_paper_series (U : Matrix N N ℂ) (c : ℝ)
    (h : ‖(c : ℂ) • U‖ < 1) :
    (adiabaticMatrix c U)⁻¹ = ∑' k : ℕ, ((c : ℂ) ^ k) • U ^ k := by
  rw [adiabaticMatrix_inv_eq_series U c h]
  simp_rw [smul_pow]

/-- For `0 < ε < 1`, the logarithm `Real.log (1 / ε)` is strictly positive. -/
theorem log_inv_epsilon_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    0 < Real.log (1 / ε) := by
  apply Real.log_pos
  exact (one_lt_div h0).mpr h1

/-- For `0 < ε < 1`, the assumptions `T ≤ q` and `κ ≤ T / Real.log (1 / ε)` imply `κ * Real.log
(1 / ε) ≤ q`. See [CostaEtAl2025]. -/
theorem query_lower_bound_chain {T q : ℕ} {κ ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hreduction : (T : ℝ) ≤ q)
    (hκ : κ ≤ (T : ℝ) / Real.log (1 / ε)) :
    κ * Real.log (1 / ε) ≤ q := by
  have hlog : 0 < Real.log (1 / ε) := log_inv_epsilon_pos hε0 hε1
  calc
    κ * Real.log (1 / ε) ≤ ((T : ℝ) / Real.log (1 / ε)) * Real.log (1 / ε) := by
      gcongr
    _ = (T : ℝ) := by field_simp
    _ ≤ q := hreduction

/-- For `0 < ε < 1`, `c ≥ 0`, and `C > 0`, the assumptions `c * T ≤ q` and `κ ≤ C * T / Real.log
(1 / ε)` imply `(c / C) * κ * Real.log (1 / ε) ≤ q`. See [CostaEtAl2025]. -/
theorem query_lower_bound_chain_scaled {T q κ ε c C : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hc : 0 ≤ c) (hC : 0 < C)
    (hreduction : c*T ≤ q) (hκ : κ ≤ C*T / Real.log (1/ε)) :
    (c/C)*κ*Real.log (1/ε) ≤ q := by
  have hlog := log_inv_epsilon_pos hε0 hε1
  have hκL := (le_div_iff₀ hlog).mp hκ
  calc
    (c/C)*κ*Real.log (1/ε) = (c/C)*(κ*Real.log (1/ε)) := by ring
    _ ≤ (c/C)*(C*T) := mul_le_mul_of_nonneg_left hκL (div_nonneg hc hC.le)
    _ = c*T := by field_simp
    _ ≤ q := hreduction

end

end Qatlib.Papers.AdiabaticQLS23.MainResults
