/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductNodes
public import Qatlib.Foundations.PureStateMath.Qubit

@[expose] public section


set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Papers.HamLCUSim12.FullSimulation
open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Papers.HamLCUSim12.Multiproduct

/-- Concrete positive integer nodes satisfy the legacy k=1 node equation. -/
theorem inverse_nodes (q : Fin 2) :
    ((q.val + 1 : ℕ) : ℝ) = mNode 1 (Real.exp ((Real.log 2 / 2) * 2)) q := by
  have he : Real.exp ((Real.log 2 / 2) * 2) = (2 : ℝ) := by
    rw [show (Real.log 2 / 2) * 2 = Real.log 2 by ring,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [he]
  fin_cases q <;> norm_num [mNode]

/-- With S constantly zero all powers at the positive integer nodes are zero. -/
theorem zero_integrator_power (q : Fin 2) (μ : ℝ) :
    ((fun _ : ℝ => (0 : Matrix (Fin 1) (Fin 1) ℂ))
      (μ / ((q.val + 1 : ℕ) : ℝ))) ^ (q.val + 1) = 0 := by
  simp

/-- The literal Lemma 10 integrator premise permits E=0, whose inverse defect is one. -/
theorem zero_inverse_defect :
    Real.sqrt (∑ x : Fin 1,
      ‖(((1 : Matrix (Fin 1) (Fin 1) ℂ) - 0 * 0) *ᵥ
        (fun _ : Fin 1 => (1 : ℂ))) x‖ ^ 2) = 1 := by
  simp

/-- Hence the zero-step error bound is false for this permitted arbitrary integrator. -/
theorem zero_inverse_refuted :
    ¬ Real.sqrt (∑ x : Fin 1,
      ‖(((1 : Matrix (Fin 1) (Fin 1) ℂ) - 0 * 0) *ᵥ
        (fun _ : Fin 1 => (1 : ℂ))) x‖ ^ 2) ≤ (0 : ℝ) ^ (4 * 1 + 2) := by
  rw [zero_inverse_defect]
  norm_num

end Qatlib.Papers.HamLCUSim12.FullSimulation
