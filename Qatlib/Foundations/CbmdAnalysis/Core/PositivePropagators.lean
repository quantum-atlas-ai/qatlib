/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.BesselMixture
import Mathlib.Analysis.Matrix.PosDef
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix Unitary
open scoped Matrix.Norms.L2Operator ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem wavePropagator_diagonal (v : n → ℂ) (t : ℂ) :
    wavePropagator (diagonal v) t = diagonal (fun i => wavePropagator (v i) t) := by
  unfold wavePropagator
  simp_rw [← diagonal_smul, diagonal_pow]
  simp_rw [← diagonal_smul]
  let D := (Matrix.diagonalLinearMap n ℂ ℂ).toContinuousLinearMap
  have hs : Summable (fun k : ℕ => (((2 * k).factorial : ℂ)⁻¹) • (-(t ^ 2) • v) ^ k) := by
    apply Pi.summable.mpr
    intro i
    exact wave_series_summable (v i) t
  have h := D.map_tsum hs
  change diagonal (∑' k : ℕ, (((2 * k).factorial : ℂ)⁻¹) • (-(t ^ 2) • v) ^ k) =
    ∑' k : ℕ, diagonal ((((2 * k).factorial : ℂ)⁻¹) • (-(t ^ 2) • v) ^ k) at h
  calc
    _ = diagonal (∑' k : ℕ, (((2 * k).factorial : ℂ)⁻¹) • (-(t ^ 2) • v) ^ k) := by
      exact h.symm
    _ = _ := by
      congr 1
      ext i
      exact Pi.tsum_apply hs

private theorem wavePropagator_conj (A : Matrix n n ℂ)
    (U : unitary (Matrix n n ℂ)) (t : ℂ) :
    wavePropagator (conjStarAlgAut ℂ _ U A) t =
      conjStarAlgAut ℂ _ U (wavePropagator A t) := by
  let e := conjStarAlgAut ℂ (Matrix n n ℂ) U
  let L := e.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv
  have h :=
      L.map_tsum (L := SummationFilter.unconditional ℕ)
      (f := fun k : ℕ => (((2 * k).factorial : ℂ)⁻¹) • (-(t ^ 2) • A) ^ k)
  simpa [L, e, wavePropagator, map_smul, map_pow] using! h.symm

theorem wavePropagator_spectral (A : Matrix n n ℂ) (hA : A.IsHermitian) (t : ℂ) :
    wavePropagator A t = conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (diagonal (fun i => wavePropagator (hA.eigenvalues i : ℂ) t)) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [wavePropagator_conj, wavePropagator_diagonal]
  rfl

theorem wavePropagator_posSemidef_norm_le_one (A : Matrix n n ℂ) (hA : A.PosSemidef) (t : ℝ) :
    ‖wavePropagator A (t : ℂ)‖ ≤ 1 := by
  rw [wavePropagator_spectral A hA.isHermitian, conjStarAlgAut_apply,
    ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  exact wavePropagator_scalar_nonneg_norm_le_one _ t (hA.eigenvalues_nonneg i)

theorem besselPropagator_posSemidef_norm_le_one (A : Matrix n n ℂ) (hA : A.PosSemidef) (t : ℝ) :
    ‖besselPropagator A (t : ℂ)‖ ≤ 1 := by
  rw [besselPropagator_wave_mixture, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos Real.pi_pos]
  have hb : ‖∫ θ in (0 : ℝ)..Real.pi,
      wavePropagator A ((t : ℂ) * (Real.sin θ : ℂ))‖ ≤ Real.pi := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := Real.pi) (C := 1)
      (f := fun θ => wavePropagator A ((t : ℂ) * (Real.sin θ : ℂ)))
      (fun θ _ => by

        rw [← Complex.ofReal_mul]
        exact wavePropagator_posSemidef_norm_le_one A hA (t * Real.sin θ))
    simpa [abs_of_pos Real.pi_pos] using! h
  calc
    Real.pi⁻¹ * _ ≤ Real.pi⁻¹ * Real.pi :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr Real.pi_pos.le)
    _ = 1 := inv_mul_cancel₀ Real.pi_ne_zero

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
