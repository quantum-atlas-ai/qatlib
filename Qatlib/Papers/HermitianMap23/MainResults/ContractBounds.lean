/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MatrixExpTrace.ExpPerturbation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # Trace-duality bridge and sample-budget boundary

The scalar lower-bound transfer assumes the spectral estimate explicitly.
It does not compute a tensor-power gap or establish a protocol lower bound.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HermitianMap23.MainResults.ContractBounds

open scoped Matrix.Norms.L2Operator

/-- Trace duality bounds the change of an observable on arbitrary matrix inputs. -/
theorem expectation_err {n : ℕ} (O σ₁ σ₂ : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.trace (O * σ₁) - Matrix.trace (O * σ₂)‖ ≤
      ‖O‖ * Matrix.traceNorm (σ₁ - σ₂) := by
  rw [← Matrix.trace_sub, ← Matrix.mul_sub]
  exact Qatlib.Concepts.MatrixExpTrace.ExpPerturbation.norm_trace_mul_le O (σ₁ - σ₂)

/-- Substitution of a spectral-gap bound is valid for a nonnegative prefactor. -/
theorem spectral_lower (c ε r g t value : ℝ) (hc : 0 ≤ c) (hε : 0 < ε)
    (hgap : g ≤ r ^ 2) (hLB : c * ε⁻¹ * r ^ 2 * t ^ 2 ≤ value) :
    c * ε⁻¹ * g * t ^ 2 ≤ value := by
  apply le_trans _ hLB
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hgap (mul_nonneg hc (inv_nonneg.mpr hε.le)))
    (sq_nonneg t)

/-- The paper's explicit positive prefactor transports any assumed exponential spectral gap. -/
theorem exp_gap_lower (n : ℕ) (ε r t : ℝ) (f : ℝ → ℝ → ℝ)
    (hε : 0 < ε) (ht : 0 < t)
    (hLB : ∀ ε' s : ℝ, 0 < ε' → 0 < s →
      (2 * Real.log 1.8 / Real.pi ^ 2 / 6) * ε'⁻¹ * r ^ 2 * s ^ 2 ≤ f ε' s)
    (hgap : (2 : ℝ) ^ (n : ℝ) ≤ r ^ 2) :
    (2 * Real.log 1.8 / Real.pi ^ 2 / 6) * ε⁻¹ * (2 : ℝ) ^ (n : ℝ) * t ^ 2 ≤
      f ε t := by
  have hlog : 0 < Real.log 1.8 := Real.log_pos (by norm_num)
  apply spectral_lower _ ε r _ t (f ε t) (by positivity) hε hgap (hLB ε t hε ht)

/-- A strictly positive number of copies cannot obey a budget proportional to zero time squared. -/
theorem zero_time_bound (C ε H : ℝ) :
    ¬ ∃ K : ℕ, 0 < K ∧ (K : ℝ) ≤ C * ε⁻¹ * H ^ 2 * (0 : ℝ) ^ 2 := by
  rintro ⟨K, hK, hb⟩
  have hp : (0 : ℝ) < K := by exact_mod_cast hK
  norm_num at hb
  linarith

end Qatlib.Papers.HermitianMap23.MainResults.ContractBounds
