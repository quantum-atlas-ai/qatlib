/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.PartialSwapEvolution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped BigOperators ComplexOrder Kronecker Matrix.Norms.L2Operator

namespace Qatlib.Papers.QuantumSVM13.CopyStep

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

variable {D : ℕ}

noncomputable def commutator (K ρ : Operator D) : Operator D := K * ρ - ρ * K

theorem kernel_swap_exact (K ρ : Operator D) (hK : IsDensityOperator K) (θ : ℝ) :
    partialSwapOutput K θ ρ =
      ((Real.cos θ) ^ 2 : ℂ) • ρ +
      ((Real.sin θ) ^ 2 : ℂ) • (Matrix.trace ρ • K) -
      (Complex.I * (Real.sin θ : ℂ) * (Real.cos θ : ℂ)) • commutator K ρ := by
  rw [partial_swap_actual_output_formula]
  rw [hK.2, one_smul]
  simp only [commutator]

theorem kernel_swap_quadratic_error (K ρ : Operator D) (hK : IsDensityOperator K) (θ : ℝ) :
    ‖partialSwapOutput K θ ρ - (ρ - (Complex.I * (θ : ℂ)) • commutator K ρ)‖ ≤
      θ ^ 2 * (‖Matrix.trace ρ‖ * ‖K‖ + ‖ρ‖ + 4 * ‖K‖ * ‖ρ‖) := by
  have h := (partial_swap_trig_and_quadratic_error.2 K hK ρ θ)
  simpa only [commutator] using h

theorem kernel_swap_quadratic_error_six (K ρ : Operator D) (hK : IsDensityOperator K)
    (θ : ℝ) (hKnorm : ‖K‖ ≤ 1) (hρnorm : ‖ρ‖ ≤ 1) (htr : ‖Matrix.trace ρ‖ ≤ 1) :
    ‖partialSwapOutput K θ ρ - (ρ - (Complex.I * (θ : ℂ)) • commutator K ρ)‖ ≤
      6 * θ ^ 2 := by
  have h := kernel_swap_quadratic_error K ρ hK θ
  have hK0 : (0 : ℝ) ≤ ‖K‖ := norm_nonneg _
  have hρ0 : (0 : ℝ) ≤ ‖ρ‖ := norm_nonneg _
  have hθ : (0 : ℝ) ≤ θ ^ 2 := sq_nonneg θ
  have hinside : ‖Matrix.trace ρ‖ * ‖K‖ + ‖ρ‖ + 4 * ‖K‖ * ‖ρ‖ ≤ 6 := by
    nlinarith [htr, hKnorm, hρnorm, hK0, hρ0, mul_nonneg hK0 hρ0,
      mul_le_mul htr hKnorm hK0 (by norm_num : (0 : ℝ) ≤ 1)]
  calc ‖partialSwapOutput K θ ρ - (ρ - (Complex.I * (θ : ℂ)) • commutator K ρ)‖
      ≤ θ ^ 2 * (‖Matrix.trace ρ‖ * ‖K‖ + ‖ρ‖ + 4 * ‖K‖ * ‖ρ‖) := h
    _ ≤ θ ^ 2 * 6 := by exact mul_le_mul_of_nonneg_left hinside hθ
    _ = 6 * θ ^ 2 := by ring

end Qatlib.Papers.QuantumSVM13.CopyStep
