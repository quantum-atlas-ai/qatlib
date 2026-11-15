/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.TrotterError19.GroupedError.TrotterCommutatorStepsContracts

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TrotterFormula.TrotterCommutatorContracts Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Qatlib.Concepts.TrotterFormula.GeneralOrder

namespace Qatlib.Papers.TrotterError19.GroupedError
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The selected rounded step count is positive and makes the scalar Trotter error budget at
most the positive tolerance. -/
theorem trotter_selected_scalar_budget (α t ε : ℝ) (p : ℕ) (hα : 0 ≤ α)
    (hε : 0 < ε) (hp : 1 ≤ p) :
    let r := max 1 (Nat.ceil ((α*|t|^(p+1)/(((p+1).factorial : ℝ)*ε))^((1 : ℝ)/p)))
    0 < r ∧ α*|t|^(p+1)/(((p+1).factorial : ℝ)*(r : ℝ)^p) ≤ ε := by
  (try dsimp only)
  let a := α*|t|^(p+1)/(((p+1).factorial : ℝ)*ε)
  let r := max 1 (Nat.ceil (a^((1 : ℝ)/p)))
  have hpR : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  have hf : (0 : ℝ) < (p+1).factorial := by exact_mod_cast Nat.factorial_pos (p+1)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hr : 0 < r := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hceil : a^((1 : ℝ)/p) ≤ (r : ℝ) := (Nat.le_ceil _).trans (by
    have hc : Nat.ceil (a^((1 : ℝ)/p)) ≤ r := le_max_right _ _
    exact_mod_cast hc)
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg ha _) hceil hpR.le
  rw [← Real.rpow_mul ha, div_mul_cancel₀ _ hpR.ne', Real.rpow_one, Real.rpow_natCast] at hpow
  have hnum := (div_le_iff₀ (mul_pos hf hε)).mp hpow
  refine ⟨hr, ?_⟩
  apply (div_le_iff₀ (mul_pos hf (pow_pos hrR p))).mpr
  convert! hnum using 1
  ring

/-- The commutator scaling estimate implies the selected step approximation bound and the exact
product word length. -/
theorem trotterCommutatorScalingSteps_of_scaling (hscaling : TrotterCommutatorScaling) :
    TrotterCommutatorScalingSteps := by
  intro I _ _ xs H p hp hxs hH hc t ε hε
  (try dsimp only)
  let α := pfCommAlphaSelf xs (p+1)
  have hα : 0 ≤ α := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hb := trotter_selected_scalar_budget α t ε p hα hε hp
  have hs := hscaling I xs H p _ hp hb.1 hxs hH hc t
  exact ⟨hb.1, hs.2.2.trans hb.2, hs.2.1⟩

end Qatlib.Papers.TrotterError19.GroupedError
