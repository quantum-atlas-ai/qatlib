/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.QuantumMixingSourceBoundsDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.DirichletForm.KmsDirichlet

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open Matrix
open scoped Matrix.Norms.L2Operator

theorem kmsInner_smul_right {D : ℕ} (ρ X Y : Operator D) (a : ℝ) :
    kmsInner ρ X (a • Y) = a • kmsInner ρ X Y := by
  simp only [kmsInner, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]

theorem dirichlet_rate {D : ℕ} (ρ : Operator D) (L : Operator D →ₗ[ℂ] Operator D)
    (a : ℝ) (O : Operator D) :
    kmsDirichlet ρ (a • L) O = a * kmsDirichlet ρ L O := by
  simp only [kmsDirichlet, LinearMap.smul_apply, ← smul_neg, kmsInner_smul_right,
    Complex.smul_re, smul_eq_mul]

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

theorem matrixFlow_rate {I : Type*} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (a t : ℝ) : matrixFlow (a • L) t = matrixFlow L (a * t) := by
  simp only [matrixFlow, smul_smul, mul_comm a t]

theorem matrixFlow_inverse_clock {I : Type*} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (a t : ℝ) (ha : a ≠ 0) :
    matrixFlow (a • L) (t / a) = matrixFlow L t := by
  rw [matrixFlow_rate, mul_div_cancel₀ _ ha]

theorem simulation_action_rate {I : Type*} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (a t : ℝ) : ‖a • L‖ * |t| = ‖L‖ * |a * t| := by
  rw [norm_smul, Real.norm_eq_abs, abs_mul]
  ring

theorem matrixFlow_zero {I : Type*} [Fintype I] [DecidableEq I] (L : Matrix I I ℂ) :
    matrixFlow L 0 = 1 := by simp [matrixFlow]

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
