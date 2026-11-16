/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section


/-! Closed source mathematics; paper algorithm claims retain their separate obligations. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.LinFuncSubset18.MainResults.FourierSampling


/-- **Numeric core of Corollary 4.2** (page 13): if `δ = 1 − r/q` satisfies
`m·δ ≤ c·log n` and `δ ≤ 1/2`, then the Fourier-sampling factor
`(q/r)^m = exp(m·(−log(1−δ)))` is at most `n^{2c}`.

This is the displayed estimate
`(r/q)^{n+O(1)} = (1 − c₁ log n/n)^{c₂n+c₃} ≥ e^{−c log n} = n^{−O(1)}`
read as an upper bound for its reciprocal. -/
theorem geometric_decay_bound {n k : ℕ} (hn : 2 ≤ n) {c δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδh : δ ≤ 1 / 2)
    (hbound : δ * ((n : ℝ) + k) ≤ c * Real.log n) :
    Real.exp (((n : ℝ) + k) * (-Real.log (1 - δ))) ≤ (n : ℝ) ^ (2 * c) := by
  have hpos : (0 : ℝ) < 1 - δ := by linarith
  have hlog : -Real.log (1 - δ) ≤ 2 * δ := by
    have h1 : Real.log ((1 - δ)⁻¹) = -Real.log (1 - δ) := Real.log_inv _
    have h2 : Real.log ((1 - δ)⁻¹) ≤ (1 - δ)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    have h3 : (1 - δ)⁻¹ - 1 = δ / (1 - δ) := by
      field_simp
      ring
    have h4 : δ / (1 - δ) ≤ 2 * δ := by
      rw [div_le_iff₀ hpos]
      nlinarith
    linarith
  have hmul : ((n : ℝ) + k) * (-Real.log (1 - δ)) ≤ ((n : ℝ) + k) * (2 * δ) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have h2 : ((n : ℝ) + k) * (2 * δ) ≤ 2 * (c * Real.log n) := by
    linarith [hbound]
  calc Real.exp (((n : ℝ) + k) * (-Real.log (1 - δ)))
      ≤ Real.exp (2 * (c * Real.log n)) := Real.exp_le_exp.mpr (hmul.trans h2)
    _ = (n : ℝ) ^ (2 * c) := by
      rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (n : ℝ))]
      ring_nf

end Qatlib.Papers.LinFuncSubset18.MainResults.FourierSampling
