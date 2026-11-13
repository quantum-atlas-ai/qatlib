/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic
import Qatlib.Concepts.ImaginaryFlow.GroundLimit.SpectralDamping

/-!
# Finite transcorrelated matrix evolution

This module defines finite complex operators, states, and the exact transcorrelated matrix `tc H
g`. It proves exponential similarity and a Hermitian spectral expansion of the evolved state,
then derives the normalized limit for a strictly isolated lowest eigenvalue with nonzero initial
coefficient. See [McArdleTew2020].

## Main statements

* `actual_tc_exp`: Similarity identity for the imaginary-time propagator.
* `actualState_spectral`: Spectral expansion in transformed eigenvector components.
* `actual_normalized_limit`: Normalized convergence at a simple lowest eigenvalue.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option autoImplicit false

open Matrix NormedSpace Filter
open scoped Classical Topology

namespace Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime

/-- Square complex matrices indexed by `Fin d`. -/
abbrev Op (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
/-- The complex Euclidean state space of dimension `d`. -/
abbrev State (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- The transcorrelated matrix `exp (-g) * H * exp g`. -/
noncomputable def tc {d : ℕ} (H g : Op d) : Op d := exp (-g) * H * exp g

/-- Every finite complex matrix exponential is a unit. -/
theorem actual_exp_isUnit {d : ℕ} (g : Op d) : IsUnit (exp g) := Matrix.isUnit_exp g

/-- The exponentials of `g` and `-g` are mutual inverses in both multiplication orders. -/
theorem actual_exp_inverse {d : ℕ} (g : Op d) :
    exp (-g) * exp g = 1 ∧ exp g * exp (-g) = 1 := by
  have hd := (Matrix.isUnit_iff_isUnit_det (exp g)).mp (Matrix.isUnit_exp g)
  rw [Matrix.exp_neg]
  exact ⟨Matrix.nonsing_inv_mul _ hd, Matrix.mul_nonsing_inv _ hd⟩

/-- The imaginary-time exponential of `tc H g` is the conjugate of the exponential of `H` by
`exp g`. See [McArdleTew2020]. -/
theorem actual_tc_exp {d : ℕ} (H g : Op d) (t : ℝ) :
    exp ((-t) • tc H g) = exp (-g) * exp ((-t) • H) * exp g := by
  have h := Matrix.exp_conj' (exp g) ((-t) • H) (Matrix.isUnit_exp g)
  rw [← Matrix.exp_neg] at h
  simpa only [tc, Matrix.mul_smul, Matrix.smul_mul] using h

/-- The unitary matrix of eigenvectors supplied by the Hermitian spectral decomposition. -/
noncomputable def eigenU {d : ℕ} {H : Op d} (hH : H.IsHermitian) : Op d :=
  hH.eigenvectorUnitary

/-- The imaginary-time exponential of a Hermitian matrix is diagonalized by its eigenvector
unitary, with entries `Real.exp (-energy * t)`. -/
theorem actual_hermitian_exp {d : ℕ} (H : Op d) (hH : H.IsHermitian) (t : ℝ) :
    exp ((-t) • H) = eigenU hH *
      Matrix.diagonal (fun i => (Real.exp (-hH.eigenvalues i * t) : ℂ)) * (eigenU hH).conjTranspose := by
  let U := Unitary.toUnits hH.eigenvectorUnitary
  have hs : (-t) • H = (U : Op d) *
      diagonal (fun i => ((-t * hH.eigenvalues i : ℝ) : ℂ)) * (↑U⁻¹ : Op d) := by
    have hd : H = (U : Op d) * diagonal (fun i => (hH.eigenvalues i : ℂ)) * (↑U⁻¹ : Op d) :=
      hH.spectral_theorem
    conv_lhs => rw [hd]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
    apply congrArg (fun D : Op d => (U : Op d) * D * (↑U⁻¹ : Op d))
    apply congrArg (diagonal : (Fin d → ℂ) → Op d)
    funext i
    simp only [Pi.smul_apply, Complex.real_smul, Complex.ofReal_mul]
  rw [hs, Matrix.exp_units_conj, Matrix.exp_diagonal]
  change (U : Op d) * diagonal (NormedSpace.exp _) * (↑U⁻¹ : Op d) = _
  have hdiag : diagonal (NormedSpace.exp (fun i : Fin d => ((-t * hH.eigenvalues i : ℝ) : ℂ))) =
      diagonal (fun i : Fin d => (Real.exp (-hH.eigenvalues i * t) : ℂ)) := by
    congr 1
    funext i
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp]
    congr 2
    ring
  rw [hdiag]
  rfl

/-- The coefficients of `exp g` applied to the initial state in the Hermitian eigenvector basis. -/
noncomputable def coefficients {d : ℕ} (g : Op d) {H : Op d} (hH : H.IsHermitian)
    (φ : State d) : Fin d → ℂ := (eigenU hH).conjTranspose *ᵥ (exp g *ᵥ φ.ofLp)

/-- The coefficient-weighted transformed eigenvector associated with index `i`. -/
noncomputable def rightComponent {d : ℕ} (g : Op d) {H : Op d} (hH : H.IsHermitian)
    (φ : State d) (i : Fin d) : State d :=
  WithLp.toLp 2 (coefficients g hH φ i • ((exp (-g) * eigenU hH)ᵀ i))

/-- The state obtained by applying the exact transcorrelated imaginary-time matrix exponential
to `φ`. -/
noncomputable def actualState {d : ℕ} (H g : Op d) (φ : State d) (t : ℝ) : State d :=
  WithLp.toLp 2 (exp ((-t) • tc H g) *ᵥ φ.ofLp)

/-- The exact evolved state is the sum of transformed eigenvector components weighted by their
imaginary-time exponential factors. -/
theorem actualState_spectral {d : ℕ} (H g : Op d) (hH : H.IsHermitian)
    (φ : State d) (t : ℝ) :
    actualState H g φ t = ∑ i : Fin d,
      Real.exp (-hH.eigenvalues i * t) • rightComponent g hH φ i := by
  have hm : exp ((-t) • tc H g) = (exp (-g) * eigenU hH) *
      diagonal (fun i => (Real.exp (-hH.eigenvalues i * t) : ℂ)) *
      ((eigenU hH).conjTranspose * exp g) := by
    rw [actual_tc_exp, actual_hermitian_exp H hH t]
    simp only [Matrix.mul_assoc]
  apply WithLp.ofLp_injective
  simp only [actualState, WithLp.ofLp_toLp, WithLp.ofLp_sum,
    WithLp.ofLp_smul, rightComponent]
  rw [hm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec φ.ofLp (eigenU hH).conjTranspose (exp g)]
  change (exp (-g) * eigenU hH) *ᵥ
      (diagonal (fun i => (Real.exp (-hH.eigenvalues i * t) : ℂ)) *ᵥ coefficients g hH φ) = _
  have hdv : (diagonal (fun i => (Real.exp (-hH.eigenvalues i * t) : ℂ)) *ᵥ coefficients g hH φ) =
      (fun i => (Real.exp (-hH.eigenvalues i * t) : ℂ) * coefficients g hH φ i) := by
    ext i
    exact Matrix.mulVec_diagonal _ _ i
  rw [hdv]
  ext j
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply,
    Pi.smul_apply, Complex.real_smul, smul_eq_mul, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The matrix-defined evolved state equals the existing abstract spectral imaginary-time state
with unit scalar coefficients. -/
theorem actualState_eq_existing_spectral {d : ℕ} (H g : Op d) (hH : H.IsHermitian)
    (φ : State d) (t : ℝ) : actualState H g φ t =
    Qatlib.Concepts.ImaginaryFlow.GroundLimit.imaginaryTimeState
      hH.eigenvalues (fun _ => 1) (rightComponent g hH φ) t := by
  rw [actualState_spectral H g hH φ t]
  simp only [Qatlib.Concepts.ImaginaryFlow.GroundLimit.imaginaryTimeState, mul_one]

/-- Every column of the transformed eigenvector matrix `exp (-g) * eigenU hH` is nonzero. -/
theorem rightColumn_ne_zero {d : ℕ} (g : Op d) {H : Op d} (hH : H.IsHermitian) (i : Fin d) :
    (exp (-g) * eigenU hH)ᵀ i ≠ 0 := by
  have hU : (eigenU hH).conjTranspose * eigenU hH = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.property
  have hleft : ((eigenU hH).conjTranspose * exp g) * (exp (-g) * eigenU hH) = 1 := by
    calc
      _ = (eigenU hH).conjTranspose * (exp g * exp (-g)) * eigenU hH := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [(actual_exp_inverse g).2]; simpa using hU
  intro hz
  have h := congrArg (fun A : Op d => A i i) hleft
  have hcol (j : Fin d) : (exp (-g) * eigenU hH) j i = 0 := congrFun hz j
  simp only [Matrix.mul_apply, hcol, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq] at h
  exact zero_ne_one h

/-- A nonzero spectral coefficient gives a nonzero transformed eigenvector component. -/
theorem rightComponent_ne_zero {d : ℕ} (g : Op d) {H : Op d} (hH : H.IsHermitian)
    (φ : State d) (i : Fin d) (hc : coefficients g hH φ i ≠ 0) :
    rightComponent g hH φ i ≠ 0 := by
  intro hz
  have hraw : coefficients g hH φ i • (exp (-g) * eigenU hH)ᵀ i = 0 :=
    congrArg WithLp.ofLp hz
  exact (smul_ne_zero hc (rightColumn_ne_zero g hH i)) hraw

/-- The transformed eigenvector matrix intertwines `tc H g` with the diagonal matrix of
eigenvalues of `H`. -/
theorem actual_right_basis {d : ℕ} (H g : Op d) (hH : H.IsHermitian) :
    tc H g * (exp (-g) * eigenU hH) = (exp (-g) * eigenU hH) *
      diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
  have hU : (eigenU hH).conjTranspose * eigenU hH = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.property
  have hHU : H * eigenU hH = eigenU hH * diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
    have hs : H = eigenU hH * diagonal (fun i => (hH.eigenvalues i : ℂ)) *
        (eigenU hH).conjTranspose := hH.spectral_theorem
    calc
      _ = (eigenU hH * diagonal (fun i => (hH.eigenvalues i : ℂ)) *
          (eigenU hH).conjTranspose) * eigenU hH := congrArg (fun A : Op d => A * eigenU hH) hs
      _ = _ := by simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
  calc
    _ = exp (-g) * (H * eigenU hH) := by
      simp only [tc, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (exp g) (exp (-g)) (eigenU hH), (actual_exp_inverse g).2]
      simp
    _ = exp (-g) * (eigenU hH * diagonal (fun i => (hH.eigenvalues i : ℂ))) := by rw [hHU]
    _ = _ := (Matrix.mul_assoc _ _ _).symm

/-- Each transformed eigenvector column satisfies the eigenvalue equation for `tc H g`. -/
theorem actual_right_column_eigen {d : ℕ} (H g : Op d) (hH : H.IsHermitian) (i : Fin d) :
    tc H g *ᵥ (exp (-g) * eigenU hH)ᵀ i =
      hH.eigenvalues i • (exp (-g) * eigenU hH)ᵀ i := by
  ext j
  have h := congrArg (fun M : Op d => M j i) (actual_right_basis H g hH)
  try dsimp only at h
  rw [Matrix.mul_diagonal] at h
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Pi.smul_apply, Complex.real_smul, mul_comm] using h

/-- Each coefficient-weighted right component satisfies the eigenvalue equation for the
transcorrelated operator. -/
theorem rightComponent_eigen {d : ℕ} (H g : Op d) (hH : H.IsHermitian)
    (φ : State d) (i : Fin d) :
    Matrix.toEuclideanLin (tc H g) (rightComponent g hH φ i) =
      hH.eigenvalues i • rightComponent g hH φ i := by
  apply WithLp.ofLp_injective
  change tc H g *ᵥ (coefficients g hH φ i • (exp (-g) * eigenU hH)ᵀ i) =
    hH.eigenvalues i • (coefficients g hH φ i • (exp (-g) * eigenU hH)ᵀ i)
  rw [Matrix.mulVec_smul, actual_right_column_eigen H g hH i]
  exact smul_comm _ _ _

/-- With a strictly isolated lowest eigenvalue and nonzero initial coefficient there, the
normalized evolved state converges to the normalized corresponding right component. See
[McArdleTew2020]. -/
theorem actual_normalized_limit {d : ℕ} (H g : Op d) (hH : H.IsHermitian)
    (φ : State d) (i0 : Fin d)
    (hgap : ∀ i : Fin d, i ≠ i0 → hH.eigenvalues i0 < hH.eigenvalues i)
    (hoverlap : coefficients g hH φ i0 ≠ 0) :
    Tendsto (fun t : ℝ => (‖actualState H g φ t‖)⁻¹ • actualState H g φ t)
      atTop (𝓝 ((‖rightComponent g hH φ i0‖)⁻¹ • rightComponent g hH φ i0)) := by
  have h := Qatlib.Concepts.ImaginaryFlow.GroundLimit.imaginaryTimeState_normalizedLimit
    hH.eigenvalues (fun _ => 1) (rightComponent g hH φ) i0 hgap
    (rightComponent_ne_zero g hH φ i0 hoverlap) one_ne_zero
  simpa only [← actualState_eq_existing_spectral H g hH φ, one_smul] using h

end Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime
