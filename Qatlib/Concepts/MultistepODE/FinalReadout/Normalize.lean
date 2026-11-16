/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring

@[expose] public section


/-! # Actual vector normalization error

For the finite ODE readout model. Absolute ODE error must be measured relative
to the nonzero target norm. This normed-space result does not assert a
trace-distance or postselection theorem for a quantum linear solver.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MultistepODE.FinalReadout.Normalize
open NormedSpace
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Normalizing two nonzero actual vectors costs at most twice their relative error. -/
theorem relativeBound {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖normalize x - normalize y‖ ≤ 2 * ‖x-y‖ / ‖x‖ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hid : normalize x - normalize y =
      ‖x‖⁻¹ • (x-y) + ‖x‖⁻¹ • ((‖y‖-‖x‖) • normalize y) := by
    simp only [sub_smul, norm_smul_normalize, smul_sub, smul_smul,
      inv_mul_cancel₀ hxpos.ne', one_smul]
    change ‖x‖⁻¹ • x - normalize y = _
    abel
  rw [hid]
  calc
    _ ≤ ‖‖x‖⁻¹ • (x-y)‖ + ‖‖x‖⁻¹ • ((‖y‖-‖x‖) • normalize y)‖ := norm_add_le _ _
    _ = ‖x‖⁻¹ * ‖x-y‖ + ‖x‖⁻¹ * |‖y‖-‖x‖| := by
      simp [norm_smul, Real.norm_eq_abs, norm_normalize hy]
    _ ≤ ‖x‖⁻¹ * ‖x-y‖ + ‖x‖⁻¹ * ‖x-y‖ := by
      gcongr
      simpa [norm_sub_rev] using abs_norm_sub_norm_le y x
    _ = 2 * ‖x-y‖ / ‖x‖ := by ring

/-- A strictly smaller absolute error guarantees a nonzero approximation and a valid bound. -/
theorem errorBound {x y : V} {eta : ℝ} (herr : ‖y-x‖ ≤ eta) (hsmall : eta < ‖x‖) :
    y ≠ 0 ∧ ‖normalize x - normalize y‖ ≤ 2 * eta / ‖x‖ := by
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt ((norm_nonneg _).trans herr) hsmall
  have hy : y ≠ 0 := by
    intro hy
    simp [hy] at herr
    linarith
  refine ⟨hy, (relativeBound (norm_pos_iff.mp hxpos) hy).trans ?_⟩
  gcongr
  simpa [norm_sub_rev] using herr

end Qatlib.Concepts.MultistepODE.FinalReadout.Normalize
