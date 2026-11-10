/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatProdVerify04.MainResults

open scoped ComplexOrder ComplexInnerProductSpace

def diagonalBranches {H : Type*} [AddCommGroup H] [Module ℂ H] (φ ψ : H) : H × H :=
  ((Real.sqrt 2)⁻¹ • φ, (Real.sqrt 2)⁻¹ • ψ)

def hadamardFirstQubit {H : Type*} [AddCommGroup H] [Module ℂ H] (a b : H) : H × H :=
  ((Real.sqrt 2)⁻¹ • (a + b), (Real.sqrt 2)⁻¹ • (a - b))

theorem hadamard_test_reflects {H : Type*} [AddCommGroup H] [Module ℂ H]
    (φ ψ : H) :
    hadamardFirstQubit ((Real.sqrt 2)⁻¹ • φ) ((Real.sqrt 2)⁻¹ • ψ)
      = ((2 : ℝ)⁻¹ • (φ + ψ), (2 : ℝ)⁻¹ • (φ - ψ)) := by
  have hsq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv]
    congr 1
    exact Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp only [hadamardFirstQubit, smul_add, smul_sub, smul_smul, hsq]

theorem hadamard_test_probability {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (φ ψ : H) (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1) :
    ‖(hadamardFirstQubit ((Real.sqrt 2)⁻¹ • φ) ((Real.sqrt 2)⁻¹ • ψ)).2‖ ^ 2
      = (1 / 2) * (1 - (⟪φ, ψ⟫).re) := by
  rw [hadamard_test_reflects]
  have hnorm : ‖(2 : ℝ)⁻¹‖ = (1 / 2 : ℝ) := by
    rw [norm_inv]
    norm_num
  have hsq : ‖φ - ψ‖ ^ 2 = 2 - 2 * (⟪φ, ψ⟫).re := by
    rw [norm_sub_sq (𝕜 := ℂ), hφ, hψ]
    simp only [RCLike.re_to_complex]
    ring
  rw [norm_smul, hnorm]
  calc ((1 / 2 : ℝ) * ‖φ - ψ‖) ^ 2
      = (1 / 4 : ℝ) * ‖φ - ψ‖ ^ 2 := by ring
    _ = (1 / 4 : ℝ) * (2 - 2 * (⟪φ, ψ⟫).re) := by rw [hsq]
    _ = (1 / 2) * (1 - (⟪φ, ψ⟫).re) := by ring

theorem hadamard_test_probability_bounds {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (φ ψ : H) (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1) :
    0 ≤ (1 / 2) * (1 - (⟪φ, ψ⟫).re) ∧ (1 / 2) * (1 - (⟪φ, ψ⟫).re) ≤ 1 := by
  have hcauchy : ‖⟪φ, ψ⟫‖ ≤ 1 := by
    have h := norm_inner_le_norm (𝕜 := ℂ) φ ψ
    rw [hφ, hψ, mul_one] at h
    exact h
  have hre : |(⟪φ, ψ⟫).re| ≤ 1 := (Complex.abs_re_le_norm _).trans hcauchy
  have hge : -1 ≤ (⟪φ, ψ⟫).re := (abs_le.mp hre).1
  have hle : (⟪φ, ψ⟫).re ≤ 1 := (abs_le.mp hre).2
  constructor <;> linarith

end Qatlib.Papers.MatProdVerify04.MainResults
