/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-!
# Cayley approximation of Hermitian evolution

This module defines `cayleyShift` and the rational evolution step `cayleyStep`. For Hermitian
matrices it proves invertibility of the shift, unitarity of the step, and compatibility with
unitary conjugation.

Scalar phase estimates and diagonalization give a cubic operator norm error bound for Hermitian
contractions. The spectral matrix analysis background is treated in [Bhatia1997].

## Main statements

* `cayleyStep_unitary`: the Cayley step of a Hermitian matrix is unitary.
* `cayleyStep_evolution_error`: the error is at most `|w| ^ 3 / 12` under the stated bounds.
* `cayleyShift_inv_norm_le`: the inverse shift has operator norm at most one.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option autoImplicit false

open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

namespace Qatlib.Concepts.InteractionEvo.CayleyTransform
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The shifted matrix `1 + (i w / 2) M` used in the Cayley approximation. -/
noncomputable def cayleyShift (M : Matrix I I ℂ) (w : ℝ) : Matrix I I ℂ :=
  1 + (Complex.I * ((w / 2 : ℝ) : ℂ)) • M

/-- The rational evolution approximation `(1 - (i w / 2) M) * (1 + (i w / 2) M)⁻¹`. -/
noncomputable def cayleyStep (M : Matrix I I ℂ) (w : ℝ) : Matrix I I ℂ :=
  (2 • (1 : Matrix I I ℂ) - cayleyShift M w) * (cayleyShift M w)⁻¹

omit [Fintype I] in

/-- For Hermitian `M`, the adjoint of its Cayley shift equals twice the identity minus the
shift. -/
theorem cayleyShift_adjoint (M : Matrix I I ℂ) (hM : M.IsHermitian) (w : ℝ) :
    (cayleyShift M w)ᴴ = 2 • (1 : Matrix I I ℂ) - cayleyShift M w := by
  simp only [cayleyShift, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, hM.eq]
  simp only [RCLike.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
  simp only [two_smul]
  module

/-- The adjoint of the Cayley shift times the shift equals `1 + (w / 2)² • (Mᴴ * M)` for
Hermitian `M`. -/
theorem cayleyShift_adjoint_mul (M : Matrix I I ℂ) (hM : M.IsHermitian) (w : ℝ) :
    (cayleyShift M w)ᴴ * cayleyShift M w =
      1 + ((w / 2) ^ 2 : ℝ) • (Mᴴ * M) := by
  rw [cayleyShift_adjoint M hM w, hM.eq]
  simp only [cayleyShift, two_smul, sub_mul, add_mul, mul_add, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The Cayley shift of a Hermitian matrix is invertible for every real step size. -/
theorem cayleyShift_isUnit (M : Matrix I I ℂ) (hM : M.IsHermitian) (w : ℝ) :
    IsUnit (cayleyShift M w) := by
  have hp : ((cayleyShift M w)ᴴ * cayleyShift M w).PosDef := by
    rw [cayleyShift_adjoint_mul M hM w]
    exact Matrix.PosDef.one.add_posSemidef
      ((Matrix.posSemidef_conjTranspose_mul_self M).smul (sq_nonneg (w / 2)))
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit
  rw [Matrix.det_mul] at hd
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_right hd)

/-- The Cayley step of a Hermitian matrix is unitary for every real step size. -/
theorem cayleyStep_unitary (M : Matrix I I ℂ) (hM : M.IsHermitian) (w : ℝ) :
    cayleyStep M w ∈ Matrix.unitaryGroup I ℂ := by
  let S := cayleyShift M w
  have hS : IsUnit S := cayleyShift_isUnit M hM w
  have hr : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS)
  have hl : (S⁻¹)ᴴ * Sᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hr, Matrix.conjTranspose_one]
  have hc : S * Sᴴ = Sᴴ * S := by
    rw [cayleyShift_adjoint M hM w]
    simp only [two_smul]
    noncomm_ring
  have he : cayleyStep M w = Sᴴ * S⁻¹ := by
    rw [cayleyStep, cayleyShift_adjoint M hM w]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, he,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    _ = (S⁻¹)ᴴ * (S * Sᴴ) * S⁻¹ := by noncomm_ring
    _ = (S⁻¹)ᴴ * (Sᴴ * S) * S⁻¹ := by rw [hc]
    _ = ((S⁻¹)ᴴ * Sᴴ) * (S * S⁻¹) := by noncomm_ring
    _ = 1 := by rw [hl, hr, one_mul]

/-- Unitary conjugation does not increase the operator norm of a matrix. -/
theorem cayley_conjugate_norm_le (U X : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) : ‖U * X * Uᴴ‖ ≤ ‖X‖ := by
  have hn : ‖U‖ ≤ 1 := l2_norm_unitary_le_one hU
  have hn' : ‖Uᴴ‖ ≤ 1 := by rwa [Matrix.l2_opNorm_conjTranspose]
  calc
    _ ≤ ‖U‖ * ‖X‖ * ‖Uᴴ‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖X‖ * 1 := by gcongr
    _ = _ := by ring

/-- Matrix inversion commutes with conjugation by a unitary matrix. -/
theorem cayley_conjugate_inv (U X : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    (U * X * Uᴴ)⁻¹ = U * X⁻¹ * Uᴴ := by
  have hr : U * Uᴴ = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] using! hU
  have hl : Uᴴ * U = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using! hU
  have hu : U⁻¹ = Uᴴ := by
    calc
      _ = U⁻¹ * (U * Uᴴ) := by rw [hr, mul_one]
      _ = Uᴴ := by rw [← mul_assoc, Matrix.nonsing_inv_mul _
        (Matrix.isUnit_det_of_right_inverse hr), one_mul]
  have hv : (Uᴴ)⁻¹ = U := by
    calc
      _ = (Uᴴ)⁻¹ * (Uᴴ * U) := by rw [hl, mul_one]
      _ = U := by rw [← mul_assoc, Matrix.nonsing_inv_mul _
        (Matrix.isUnit_det_of_right_inverse hl), one_mul]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hu, hv]
  noncomm_ring

/-- The scalar Cayley quotient `(1 - i x) / (1 + i x)` equals the phase exponential with angle
`-2 arctan x`. -/
theorem cayley_scalar_phase (x : ℝ) :
    ((1 : ℂ) - Complex.I * (x : ℂ)) / (1 + Complex.I * (x : ℂ)) =
      Complex.exp (((-2 * Real.arctan x : ℝ) : ℂ) * Complex.I) := by
  let t := Real.arctan x
  have hcos : Real.cos t ≠ 0 := (Real.cos_arctan_pos x).ne'
  have hsin : Real.sin t = x * Real.cos t := by
    have ht : Real.sin t / Real.cos t = x := by
      simpa only [← Real.tan_eq_sin_div_cos] using! Real.tan_arctan x
    exact (div_eq_iff hcos).mp ht
  have hden : (1 : ℂ) + Complex.I * (x : ℂ) ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    norm_num at h
  have hphase : Complex.exp (((-2 * t : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-t : ℝ) : ℂ) * Complex.I) / Complex.exp ((t : ℂ) * Complex.I) := by
    rw [← Complex.exp_sub]
    congr 1
    push_cast
    ring
  have hcross : ((1 : ℂ) - Complex.I * (x : ℂ)) * Complex.exp ((t : ℂ) * Complex.I) =
      Complex.exp (((-t : ℝ) : ℂ) * Complex.I) * (1 + Complex.I * (x : ℂ)) := by
    rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg,
      hsin]
    push_cast
    ring
  rw [hphase]
  exact (div_eq_div_iff hden (Complex.exp_ne_zero _)).2 hcross

/-- The scalar Cayley quotient with half-step `x / 2` differs from `exp(-i x)` by at most `|x|³
/ 12`. -/
theorem cayley_scalar_error (x : ℝ) :
    ‖((1 : ℂ) - Complex.I * (x / 2 : ℝ)) / (1 + Complex.I * (x / 2 : ℝ)) -
      Complex.exp (((-x : ℝ) : ℂ) * Complex.I)‖ ≤ |x| ^ 3 / 12 := by
  rw [cayley_scalar_phase]
  have he := norm_exp_mul_I_sub_le (-2 * Real.arctan (x / 2)) (-x)
  have hr := rational_cayley_derived_arctan_remainder (x / 2)
  calc
    _ ≤ |-2 * Real.arctan (x / 2) - -x| := he
    _ = 2 * |Real.arctan (x / 2) - x / 2| := by
      rw [show -2 * Real.arctan (x / 2) - -x =
        -2 * (Real.arctan (x / 2) - x / 2) by ring, abs_mul]
      norm_num
    _ ≤ 2 * (|x / 2| ^ 3 / 3) := mul_le_mul_of_nonneg_left hr (by norm_num)
    _ = _ := by rw [abs_div]; norm_num; ring

/-- The Cayley step commutes with conjugation by a unitary matrix. -/
theorem cayleyStep_conjugate (U : Matrix.unitaryGroup I ℂ) (M : Matrix I I ℂ) (w : ℝ) :
    cayleyStep ((U : Matrix I I ℂ) * M * (U : Matrix I I ℂ)ᴴ) w =
      (U : Matrix I I ℂ) * cayleyStep M w * (U : Matrix I I ℂ)ᴴ := by
  let f := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U
  have hs : cayleyShift (f M) w = f (cayleyShift M w) := by
    simp only [cayleyShift, map_add, map_one, map_smul]
  change cayleyStep (f M) w = f (cayleyStep M w)
  rw [cayleyStep, hs, cayleyStep, map_mul, map_sub, two_smul, map_add, map_one]
  congr 1
  exact cayley_conjugate_inv _ _ U.property

/-- Hamiltonian evolution commutes with conjugation by a unitary matrix. -/
theorem cayley_evolution_conjugate (U : Matrix.unitaryGroup I ℂ)
    (M : Matrix I I ℂ) (w : ℝ) :
    HamiltonianEvolution ((U : Matrix I I ℂ) * M * (U : Matrix I I ℂ)ᴴ) w =
      (U : Matrix I I ℂ) * HamiltonianEvolution M w * (U : Matrix I I ℂ)ᴴ := by
  have hu : (U : Matrix I I ℂ)⁻¹ = (U : Matrix I I ℂ)ᴴ := by
    have hr : (U : Matrix I I ℂ) * (U : Matrix I I ℂ)ᴴ = 1 := by
      simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] using! U.property
    calc
      _ = (U : Matrix I I ℂ)⁻¹ *
          ((U : Matrix I I ℂ) * (U : Matrix I I ℂ)ᴴ) := by rw [hr, mul_one]
      _ = _ := by rw [← mul_assoc, Matrix.nonsing_inv_mul _
        (Matrix.isUnit_det_of_right_inverse hr), one_mul]
  simp only [HamiltonianEvolution]
  rw [← smul_mul_assoc, ← mul_smul_comm, ← hu]
  exact Matrix.exp_conj _ _ (Unitary.isUnit_coe (U := U))

/-- The inverse of a diagonal matrix with nonzero entries is the diagonal matrix of entrywise
inverses. -/
theorem cayley_diagonal_inv (d : I → ℂ) (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
  have hr : Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [hd]
  calc
    _ = (Matrix.diagonal d)⁻¹ *
        (Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹)) := by rw [hr, mul_one]
    _ = _ := by rw [← mul_assoc, Matrix.nonsing_inv_mul _
      (Matrix.isUnit_det_of_right_inverse hr), one_mul]

/-- The Cayley step of a real diagonal matrix is diagonal with the scalar Cayley quotients as
entries. -/
theorem cayleyStep_diagonal (d : I → ℝ) (w : ℝ) :
    cayleyStep (Matrix.diagonal (fun i => (d i : ℂ))) w =
      Matrix.diagonal (fun i => (1 - Complex.I * ((w * d i / 2 : ℝ) : ℂ)) /
        (1 + Complex.I * ((w * d i / 2 : ℝ) : ℂ))) := by
  have hs : cayleyShift (Matrix.diagonal (fun i => (d i : ℂ))) w =
      Matrix.diagonal (fun i => 1 + Complex.I * ((w * d i / 2 : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [cayleyShift]; ring
    · simp [cayleyShift, Matrix.diagonal, h]
  have hn : ∀ i, (1 : ℂ) + Complex.I * ((w * d i / 2 : ℝ) : ℂ) ≠ 0 := by
    intro i he
    have h := congrArg Complex.re he
    norm_num at h
  rw [cayleyStep, hs, cayley_diagonal_inv _ hn]
  have ht : 2 • (1 : Matrix I I ℂ) -
      Matrix.diagonal (fun i => 1 + Complex.I * ((w * d i / 2 : ℝ) : ℂ)) =
      Matrix.diagonal (fun i => 1 - Complex.I * ((w * d i / 2 : ℝ) : ℂ)) := by
    rw [two_smul]
    ext i j
    by_cases h : i = j
    · subst j; simp
    · simp [Matrix.diagonal, h]
  rw [ht, Matrix.diagonal_mul_diagonal]
  rfl

/-- Evolution under a real diagonal Hamiltonian is diagonal with entries `exp(-i w d i)`. -/
theorem cayley_evolution_diagonal (d : I → ℝ) (w : ℝ) :
    HamiltonianEvolution (Matrix.diagonal (fun i => (d i : ℂ))) w =
      Matrix.diagonal (fun i => Complex.exp (((-(w * d i) : ℝ) : ℂ) * Complex.I)) := by
  unfold HamiltonianEvolution
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext i
  rw [← Complex.exp_eq_exp_ℂ]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- Every eigenvalue of a Hermitian contraction has absolute value at most one. -/
theorem cayley_eigenvalue_le (M : Matrix I I ℂ) (hM : M.IsHermitian)
    (hnorm : ‖M‖ ≤ 1) (i : I) : |hM.eigenvalues i| ≤ 1 := by
  have he := hM.conjStarAlgAut_star_eigenvectorUnitary
  have hn := (cayley_conjugate_norm_le
    (↑(star hM.eigenvectorUnitary) : Matrix I I ℂ) M
    (star hM.eigenvectorUnitary).property).trans hnorm
  change ‖Unitary.conjStarAlgAut ℂ _ (star hM.eigenvectorUnitary) M‖ ≤ 1 at hn
  rw [he, Matrix.l2_opNorm_diagonal] at hn
  have hp := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp hn i
  simpa only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal,
    Complex.norm_real, Real.norm_eq_abs] using! hp

/-- For a Hermitian contraction and `|w| ≤ 1`, the Cayley evolution error is at most `|w|³ / 12`
in operator norm. -/
theorem cayleyStep_evolution_error (M : Matrix I I ℂ) (hM : M.IsHermitian) (hnorm : ‖M‖ ≤ 1)
    {w : ℝ} (_hw : |w| ≤ 1) :
    ‖cayleyStep M w - HamiltonianEvolution M w‖ ≤ |w| ^ 3 / 12 := by
  let U := hM.eigenvectorUnitary
  let d := hM.eigenvalues
  have hs : M = (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) *
      (U : Matrix I I ℂ)ᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_apply, RCLike.ofReal_eq_complex_ofReal] using! hM.spectral_theorem
  rw [hs, cayleyStep_conjugate, cayley_evolution_conjugate,
    ← sub_mul, ← mul_sub]
  apply (cayley_conjugate_norm_le _ _ U.property).trans
  rw [cayleyStep_diagonal, cayley_evolution_diagonal, Matrix.diagonal_sub,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hi : |d i| ≤ 1 := cayley_eigenvalue_le M hM hnorm i
  calc
    _ ≤ |w * d i| ^ 3 / 12 := cayley_scalar_error (w * d i)
    _ ≤ |w| ^ 3 / 12 := by rw [abs_mul]; gcongr; nlinarith [abs_nonneg w]

/-- The inverse Cayley shift of a Hermitian matrix has operator norm at most one for every real
step size. -/
theorem cayleyShift_inv_norm_le (M : Matrix I I ℂ) (hM : M.IsHermitian) (w : ℝ) :
    ‖(cayleyShift M w)⁻¹‖ ≤ 1 := by
  let U := hM.eigenvectorUnitary
  let d := hM.eigenvalues
  have hs : M = (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) *
      (U : Matrix I I ℂ)ᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_apply, RCLike.ofReal_eq_complex_ofReal] using! hM.spectral_theorem
  let f := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U
  have hf : cayleyShift (f (Matrix.diagonal (fun i => (d i : ℂ)))) w =
      f (cayleyShift (Matrix.diagonal (fun i => (d i : ℂ))) w) := by
    simp only [cayleyShift, map_add, map_one, map_smul]
  rw [hs]
  change ‖(cayleyShift (f (Matrix.diagonal (fun i => (d i : ℂ)))) w)⁻¹‖ ≤ 1
  rw [hf]
  change ‖((U : Matrix I I ℂ) * cayleyShift (Matrix.diagonal (fun i => (d i : ℂ))) w *
    (U : Matrix I I ℂ)ᴴ)⁻¹‖ ≤ 1
  rw [cayley_conjugate_inv _ _ U.property]
  apply (cayley_conjugate_norm_le _ _ U.property).trans
  have hd : cayleyShift (Matrix.diagonal (fun i => (d i : ℂ))) w =
      Matrix.diagonal (fun i => 1 + Complex.I * ((w * d i / 2 : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [cayleyShift]; ring
    · simp [cayleyShift, Matrix.diagonal, h]
  have hn : ∀ i, (1 : ℂ) + Complex.I * ((w * d i / 2 : ℝ) : ℂ) ≠ 0 := by
    intro i he
    have h := congrArg Complex.re he
    norm_num at h
  rw [hd, cayley_diagonal_inv _ hn, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  have he : 1 ≤ ‖(1 : ℂ) + Complex.I * ((w * d i / 2 : ℝ) : ℂ)‖ := by
    simpa using! Complex.abs_re_le_norm ((1 : ℂ) + Complex.I * ((w * d i / 2 : ℝ) : ℂ))
  simpa only [norm_inv] using! inv_le_one_of_one_le₀ he

end Qatlib.Concepts.InteractionEvo.CayleyTransform
