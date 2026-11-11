/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.QuantumMixingSourceBoundsDefs

/-!
# Rate rescaling for KMS forms and matrix flows

This module proves how real rescaling of a generator changes its KMS Dirichlet form and lower
gap bound. For positive scale factors, the gap predicate rescales by the same factor.

For `matrixFlow`, generator rescaling is equivalent to rescaling time, and inverse time
rescaling recovers the original flow. The matrix-exponential and open-system context is
described in [BreuerPetruccione2007].

## Main statements

* `dirichlet_rate`: Real generator scaling multiplies the KMS Dirichlet form by that scalar.
* `gap_rate_iff`: Positive scaling gives an equivalence of rescaled gap predicates.
* `matrixFlow_inverse_clock`: Inverse clock scaling compensates a nonzero generator scaling.
* `simulation_action_rate`: Generator norm times absolute time transforms by the same clock
  rescaling.

## References

* [Breuer and Petruccione, 2007][BreuerPetruccione2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.DirichletForm.KmsDirichlet

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The KMS inner product commutes with real scalar multiplication in its second argument. -/
theorem kmsInner_smul_right {D : ℕ} (ρ X Y : Operator D) (a : ℝ) :
    kmsInner ρ X (a • Y) = a • kmsInner ρ X Y := by
  simp only [kmsInner, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]

/-- Multiplying the generator by a real scalar multiplies its KMS Dirichlet form by that scalar. -/
theorem dirichlet_rate {D : ℕ} (ρ : Operator D) (L : Operator D →ₗ[ℂ] Operator D)
    (a : ℝ) (O : Operator D) :
    kmsDirichlet ρ (a • L) O = a * kmsDirichlet ρ L O := by
  simp only [kmsDirichlet, LinearMap.smul_apply, ← smul_neg, kmsInner_smul_right,
    Complex.smul_re, smul_eq_mul]

/-- For a positive real scale factor, a rescaled KMS gap lower bound holds for the rescaled
generator if and only if the original bound holds for the original generator. -/
theorem gap_rate_iff {D : ℕ} (ρ : Operator D) (L : Operator D →ₗ[ℂ] Operator D)
    (a r : ℝ) (ha : 0 < a) :
    KmsGapAtLeast ρ (a • L) (a * r) ↔ KmsGapAtLeast ρ L r := by
  constructor
  · intro h O
    have hh := h O
    rw [dirichlet_rate] at hh
    nlinarith
  · intro h O
    rw [dirichlet_rate]
    have hh := mul_le_mul_of_nonneg_left (h O) ha.le
    simpa only [mul_assoc] using hh

/-- Scaling a matrix generator by a real scalar is equivalent to multiplying the flow time by
that scalar. -/
theorem matrixFlow_rate {I : Type*} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (a t : ℝ) : matrixFlow (a • L) t = matrixFlow L (a * t) := by
  simp only [matrixFlow, smul_smul, mul_comm a t]

/-- For a nonzero real scale factor, dividing time by that factor cancels the corresponding
generator scaling. -/
theorem matrixFlow_inverse_clock {I : Type*} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (a t : ℝ) (ha : a ≠ 0) :
    matrixFlow (a • L) (t / a) = matrixFlow L t := by
  rw [matrixFlow_rate, mul_div_cancel₀ _ ha]

/-- The generator operator norm times absolute time is preserved when a real scale factor is
moved from the generator to time. -/
theorem simulation_action_rate {I : Type*} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (a t : ℝ) : ‖a • L‖ * |t| = ‖L‖ * |a * t| := by
  rw [norm_smul, Real.norm_eq_abs, abs_mul]
  ring

/-- The matrix flow at time zero is the identity matrix. -/
theorem matrixFlow_zero {I : Type*} [Fintype I] [DecidableEq I] (L : Matrix I I ℂ) :
    matrixFlow L 0 = 1 := by simp [matrixFlow]

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
