/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Spectral tools for finite unitary walks

This module constructs orthonormal eigenbases for finite unitary matrices and develops Parseval
and resolvent norm identities. Spectral gap weights and real-eigenvector rotation estimates
support the quantitative Grover interpolation argument.

The mathematical background is developed in [Bhatia1997].

## Main statements

* `jw_unitary_orthonormal_eigenbasis`: constructs a unitary matrix of eigenvectors.
* `jw_unitary_gap_weights`: separates fixed and nonfixed spectral mass.
* `jw_real_unitary_normalized_quarter_iteration`: bounds the normalized quarter-turn error.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.GroverInterp

open Matrix
open scoped InnerProductSpace

/-- A finite complex unitary matrix has an orthonormal eigenbasis in Euclidean space with all
eigenvalues of norm one. -/
theorem jw_unitary_euclidean_eigenbasis (m : ℕ) (U : Matrix (Fin m) (Fin m) ℂ)
    (hu : star U * U = 1) :
    ∃ (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (μ : Fin m → ℂ),
      (∀ j, ‖μ j‖ = 1) ∧ ∀ j, U.toEuclideanLin (b j) = μ j • b j := by
  classical
  let f : Module.End ℂ (EuclideanSpace ℂ (Fin m)) := U.toEuclideanLin
  have hf : star f * f = 1 := by
    change U.toEuclideanLin.adjoint * U.toEuclideanLin = 1
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simpa only [Matrix.star_eq_conjTranspose, Matrix.toEuclideanLin,
      Matrix.toLpLin_mul_same, Matrix.toLpLin_one] using!
      congrArg (Matrix.toEuclideanLin) hu
  have hff : f * star f = 1 := by
    have hU : U * star U = 1 := mul_eq_one_comm.mp hu
    change U.toEuclideanLin * U.toEuclideanLin.adjoint = 1
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simpa only [Matrix.star_eq_conjTranspose, Matrix.toEuclideanLin,
      Matrix.toLpLin_mul_same, Matrix.toLpLin_one] using!
      congrArg (Matrix.toEuclideanLin) hU
  let H : Module.End ℂ (EuclideanSpace ℂ (Fin m)) := (1 / 2 : ℂ) • (f + star f)
  let K : Module.End ℂ (EuclideanSpace ℂ (Fin m)) := (-Complex.I / 2) • (f - star f)
  have hH : H.IsSymmetric := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
    change star H = H
    simp [H, star_smul, add_comm]
  have hK : K.IsSymmetric := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
    change star K = K
    simp only [K, star_smul, star_sub, star_star]
    rw [show star (-Complex.I / 2) = Complex.I / 2 by simp]
    rw [← neg_sub f (star f), smul_neg, ← neg_smul]
    rw [neg_smul, neg_div]
    exact (neg_smul _ _).symm
  have hc : Commute f (star f) := by
    show f * star f = star f * f
    rw [hf, hff]
  have hHK : Commute H K :=
    (((Commute.refl f).sub_right hc).add_left
      (hc.symm.sub_right (Commute.refl (star f)))).smul_left (1 / 2 : ℂ)
        |>.smul_right (-Complex.I / 2)
  let ι := {i : ℂ × ℂ // H.eigenspace i.2 ⊓ K.eigenspace i.1 ≠ ⊥}
  let embed : ι → Module.End.Eigenvalues H × Module.End.Eigenvalues K :=
    fun i => (⟨i.1.2, ne_bot_of_le_ne_bot i.2 inf_le_left⟩,
      ⟨i.1.1, ne_bot_of_le_ne_bot i.2 inf_le_right⟩)
  have hembed : Function.Injective embed := by
    intro i j hij
    apply Subtype.ext
    exact Prod.ext (congrArg (fun p => p.2.val) hij) (congrArg (fun p => p.1.val) hij)
  letI : Finite ι := Finite.of_injective embed hembed
  letI : Fintype ι := Fintype.ofFinite ι
  have horth := (hH.orthogonalFamily_eigenspace_inf_eigenspace hK).comp
    (Subtype.coe_injective : Function.Injective (Subtype.val : ι → ℂ × ℂ))
  have hdecomp : DirectSum.IsInternal (fun i : ι => H.eigenspace i.1.2 ⊓ K.eigenspace i.1.1) := by
    apply horth.isInternal_iff.mpr
    rw [iSup_ne_bot_subtype]
    rw [Submodule.orthogonal_eq_bot_iff, iSup_prod, iSup_comm]
    exact hH.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hK hHK
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = m := by simp
  let b := hdecomp.subordinateOrthonormalBasis hn horth
  let χ := fun j => hdecomp.subordinateOrthonormalBasisIndex hn j horth
  let μ := fun j => (χ j).1.2 + Complex.I * (χ j).1.1
  have hparts : H + Complex.I • K = f := by
    have hIK : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
      rw [← mul_div_assoc, mul_neg, Complex.I_mul_I]
      norm_num
    simp only [H, K, smul_smul, hIK]
    module
  have heig (j : Fin m) : f (b j) = μ j • b j := by
    have hj := hdecomp.subordinateOrthonormalBasis_subordinate hn j horth
    have hHj := Module.End.mem_eigenspace_iff.mp hj.1
    have hKj := Module.End.mem_eigenspace_iff.mp hj.2
    rw [← hparts, LinearMap.add_apply]
    change H (b j) + Complex.I • K (b j) = _
    rw [hHj, hKj, smul_smul, ← add_smul]
  refine ⟨b, μ, ?_, heig⟩
  intro j
  have hb : ⟪b j, b j⟫_ℂ = 1 := inner_self_eq_one_of_norm_eq_one (b.orthonormal.norm_eq_one j)
  have hi : star (μ j) * μ j = 1 := by
    have hinner : ⟪f (b j), f (b j)⟫_ℂ = ⟪b j, b j⟫_ℂ := by
      rw [← LinearMap.adjoint_inner_right f (b j) (f (b j))]
      change ⟪b j, (star f * f) (b j)⟫_ℂ = _
      rw [hf]
      rfl
    rw [heig j, inner_smul_left, inner_smul_right, hb, mul_one] at hinner
    exact hinner
  have hnorm := congrArg norm hi
  simp only [norm_mul, norm_star, norm_one] at hnorm
  nlinarith only [hnorm, norm_nonneg (μ j)]

/-- A finite complex unitary matrix has a unitary eigenbasis matrix whose eigenvalues all have
norm one. -/
theorem jw_unitary_orthonormal_eigenbasis (m : ℕ) (U : Matrix (Fin m) (Fin m) ℂ)
    (hu : star U * U = 1) :
    ∃ (B : Matrix (Fin m) (Fin m) ℂ) (μ : Fin m → ℂ),
      star B * B = 1 ∧ B * star B = 1 ∧ (∀ j, ‖μ j‖ = 1) ∧
        ∀ j, U *ᵥ (fun i => B i j) = μ j • (fun i => B i j) := by
  classical
  obtain ⟨b, μ, hμ, hb⟩ := jw_unitary_euclidean_eigenbasis m U hu
  let B := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.toMatrix b.toBasis
  have hB : B ∈ Matrix.unitaryGroup (Fin m) ℂ :=
    (EuclideanSpace.basisFun (Fin m) ℂ).toMatrix_orthonormalBasis_mem_unitary b
  refine ⟨B, μ, Matrix.mem_unitaryGroup_iff'.mp hB,
    Matrix.mem_unitaryGroup_iff.mp hB, hμ, ?_⟩
  intro j
  change U *ᵥ (WithLp.ofLp (b j)) = μ j • WithLp.ofLp (b j)
  exact congrArg WithLp.ofLp (hb j)

/-- The Hermitian self-pairing of a complex vector equals the real sum of its squared coordinate
norms. -/
theorem jw_star_dot_self (m : ℕ) (v : Fin m → ℂ) :
    star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  have he (i : Fin m) : star (v i) * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp only [dotProduct, Pi.star_apply, he, Complex.ofReal_sum]

/-- Multiplication by a unitary matrix preserves the sum of squared coordinate norms. -/
theorem jw_unitary_mulVec_norm_sq (m : ℕ) (B : Matrix (Fin m) (Fin m) ℂ)
    (hu : star B * B = 1) (v : Fin m → ℂ) :
    (∑ i, ‖(B *ᵥ v) i‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← jw_star_dot_self, ← jw_star_dot_self, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  change star v ⬝ᵥ ((star B * B) *ᵥ v) = star v ⬝ᵥ v
  rw [hu, Matrix.one_mulVec]

/-- The sum of squared coefficients in a unitary basis equals the sum of squared coordinate
norms. -/
theorem jw_unitary_basis_parseval (m : ℕ) (B : Matrix (Fin m) (Fin m) ℂ)
    (hB : B * star B = 1) (v : Fin m → ℂ) :
    (∑ j, ‖(star B *ᵥ v) j‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
  apply jw_unitary_mulVec_norm_sq
  simpa using hB

/-- A complex exponential with phase strictly between zero and `2π` is different from one. -/
theorem jw_phase_ne_one (θ : ℝ) (hθ : 0 < θ) (hθtop : θ < 2 * Real.pi) :
    Complex.exp (Complex.I * θ) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hi : θ = (n : ℝ) * (2 * Real.pi) := by
    simpa using congrArg Complex.im hn
  have hnlo : (0 : ℝ) < n := by nlinarith only [hθ, hi, Real.pi_pos]
  have hnhi : (n : ℝ) < 1 := by nlinarith only [hθtop, hi, Real.pi_pos]
  have hnlo' : (0 : ℤ) < n := by exact_mod_cast hnlo
  have hnhi' : n < 1 := by exact_mod_cast hnhi
  omega

/-- Under the spectral phase condition, every fixed vector lies on the line spanned by the
normalized fixed vector `start`. -/
theorem jw_fixed_vector_start_line (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (U : Matrix (Fin m) (Fin m) ℂ) (start v : Fin m → ℂ)
    (hstart : U *ᵥ start = start) (hfixed : U *ᵥ v = v)
    (hsn : (∑ i, ‖start i‖ ^ 2) = 1)
    (hphase : ∀ (ν : ℂ) (w : Fin m → ℂ), U *ᵥ w = ν • w →
      (∑ i, star (w i) * start i) = 0 → w ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ θ ≠ Real.pi ∧
        ν = Complex.exp (Complex.I * θ)) :
    v = (star start ⬝ᵥ v) • start := by
  let c := star start ⬝ᵥ v
  let w := v - c • start
  have hsn' : star start ⬝ᵥ start = 1 := by rw [jw_star_dot_self, hsn]; rfl
  have hwfix : U *ᵥ w = (1 : ℂ) • w := by
    simp only [w, Matrix.mulVec_sub, Matrix.mulVec_smul, hfixed, hstart, one_smul]
  have hworth : (∑ i, star (w i) * start i) = 0 := by
    have hc : star v ⬝ᵥ start = star c := by
      simp only [c, dotProduct, Pi.star_apply, star_sum, star_mul, star_star, mul_comm]
    change star w ⬝ᵥ start = 0
    simp only [w, star_sub, sub_dotProduct, star_smul, smul_dotProduct, hc, hsn']
    simp
  have hwzero : w = 0 := by
    by_contra hw
    obtain ⟨θ, hlo, hhi, _, he⟩ := hphase 1 w hwfix hworth hw
    exact jw_phase_ne_one θ (hε.trans_le hlo) (by linarith only [hhi, hε]) he.symm
  exact sub_eq_zero.mp hwzero

/-- An eigenvector with eigenvalue different from one has zero Hermitian pairing with a fixed
vector of the unitary matrix. -/
theorem jw_eigenvector_start_coefficient_zero (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (start v : Fin m → ℂ) (μ : ℂ)
    (hu : star U * U = 1) (hstart : U *ᵥ start = start)
    (heigen : U *ᵥ v = μ • v) (hμ : μ ≠ 1) : star v ⬝ᵥ start = 0 := by
  have hadj : star U *ᵥ start = start := by
    calc
      _ = star U *ᵥ (U *ᵥ start) := by rw [hstart]
      _ = start := by rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]
  have hrow : star start ᵥ* U = star start := by
    simpa only [Matrix.star_mulVec, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using congrArg star hadj
  have hc : μ * (star start ⬝ᵥ v) = star start ⬝ᵥ v := by
    calc
      _ = star start ⬝ᵥ (U *ᵥ v) := by rw [heigen, dotProduct_smul, smul_eq_mul]
      _ = _ := by rw [Matrix.dotProduct_mulVec, hrow]
  have hc0 : star start ⬝ᵥ v = 0 := by
    have hm : (μ - 1) * (star start ⬝ᵥ v) = 0 := by linear_combination hc
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hμ)
  apply star_eq_zero.mp
  simpa only [dotProduct, Pi.star_apply, star_sum, star_mul, star_star, mul_comm] using hc0

/-- There are an orthonormal eigenbasis and nonnegative fixed and nonfixed weights splitting the
target spectral mass into totals `α^2` and `1 - α^2`. -/
theorem jw_unitary_gap_weights (m : ℕ) (ε α : ℝ) (hε : 0 < ε)
    (U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ)
    (hu : star U * U = 1) (hstart : U *ᵥ start = start)
    (hsn : (∑ i, ‖start i‖ ^ 2) = 1) (hgn : (∑ i, ‖good i‖ ^ 2) = 1)
    (hoverlap : star good ⬝ᵥ start = (α : ℂ))
    (hphase : ∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
      (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ θ ≠ Real.pi ∧
        ν = Complex.exp (Complex.I * θ)) :
    ∃ (B : Matrix (Fin m) (Fin m) ℂ) (μ : Fin m → ℂ) (w s : Fin m → ℝ),
      star B * B = 1 ∧ B * star B = 1 ∧
      (∀ j, ‖μ j‖ = 1) ∧
      (∀ j, U *ᵥ (fun i => B i j) = μ j • (fun i => B i j)) ∧
      (∀ j, 0 ≤ w j) ∧ (∀ j, 0 ≤ s j) ∧
      (∑ j, w j) = 1 - α ^ 2 ∧ (∑ j, s j) = 1 ∧
      (∀ j, μ j = 1 → w j = 0) ∧ (∀ j, μ j ≠ 1 → s j = 0) ∧
      ∀ j, ‖(star B *ᵥ good) j‖ ^ 2 = w j + α ^ 2 * s j := by
  classical
  obtain ⟨B, μ, hB, hB', hμ, heig⟩ := jw_unitary_orthonormal_eigenbasis m U hu
  let c := star B *ᵥ good
  let d := star B *ᵥ start
  let s := fun j => ‖d j‖ ^ 2
  let w := fun j => if μ j = 1 then 0 else ‖c j‖ ^ 2
  have hsumc : (∑ j, ‖c j‖ ^ 2) = 1 := (jw_unitary_basis_parseval m B hB' good).trans hgn
  have hsums : (∑ j, s j) = 1 := (jw_unitary_basis_parseval m B hB' start).trans hsn
  have hd0 (j : Fin m) (hj : μ j ≠ 1) : d j = 0 := by
    exact jw_eigenvector_start_coefficient_zero m U start (fun i => B i j) (μ j)
      hu hstart (heig j) hj
  have hsg : star start ⬝ᵥ good = (α : ℂ) := by
    have h := congrArg star hoverlap
    simpa [dotProduct, star_sum, star_mul, mul_comm] using h
  have hcfix (j : Fin m) (hj : μ j = 1) : c j = (α : ℂ) * d j := by
    have hjfix : U *ᵥ (fun i => B i j) = (fun i => B i j) := by
      simpa only [hj, one_smul] using heig j
    have hline := jw_fixed_vector_start_line m ε hε U start (fun i => B i j)
      hstart hjfix hsn hphase
    have hconj : star (star start ⬝ᵥ (fun i => B i j)) = d j := by
      simp only [d, dotProduct, Matrix.mulVec, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, star_sum, star_mul, star_star, Pi.star_apply, mul_comm]
    change star (fun i => B i j) ⬝ᵥ good = (α : ℂ) * d j
    rw [hline, star_smul, smul_dotProduct, smul_eq_mul, hconj, hsg, mul_comm]
  have hweights (j : Fin m) : ‖c j‖ ^ 2 = w j + α ^ 2 * s j := by
    by_cases hj : μ j = 1
    · simp only [w, hj, if_pos, zero_add, s, hcfix j hj, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, mul_pow, sq_abs]
    · simp only [w, if_neg hj, s, hd0 j hj, norm_zero, zero_pow (by decide : 2 ≠ 0),
        mul_zero, add_zero]
  have hsumw : (∑ j, w j) = 1 - α ^ 2 := by
    have hh := hsumc
    simp only [hweights, Finset.sum_add_distrib, ← Finset.mul_sum, hsums, mul_one] at hh
    linarith only [hh]
  refine ⟨B, μ, w, s, hB, hB', hμ, heig, ?_, ?_, hsumw, hsums, ?_, ?_, hweights⟩
  · intro j
    simp only [w]
    split_ifs <;> positivity
  · intro j
    exact sq_nonneg _
  · intro j hj
    simp only [w, hj, if_pos]
  · intro j hj
    simp only [s, hd0 j hj, norm_zero, zero_pow (by decide : 2 ≠ 0)]

/-- Under the phase-gap hypothesis, a nonfixed eigenvalue with a nonzero eigenvector has real
part in `[-1, cos ε]`. -/
theorem jw_nonfixed_eigenvalue_real_gap (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (U : Matrix (Fin m) (Fin m) ℂ) (start v : Fin m → ℂ) (μ : ℂ)
    (hu : star U * U = 1) (hstart : U *ᵥ start = start)
    (heigen : U *ᵥ v = μ • v) (hμ : μ ≠ 1) (hv : v ≠ 0)
    (hphase : ∀ (ν : ℂ) (w : Fin m → ℂ), U *ᵥ w = ν • w →
      (∑ i, star (w i) * start i) = 0 → w ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ θ ≠ Real.pi ∧
        ν = Complex.exp (Complex.I * θ)) :
    -1 ≤ μ.re ∧ μ.re ≤ Real.cos ε := by
  have ho := jw_eigenvector_start_coefficient_zero m U start v μ hu hstart heigen hμ
  obtain ⟨θ, hlo, hhi, _, he⟩ := hphase μ v heigen ho hv
  have hre : μ.re = Real.cos θ := by simp [he, Complex.exp_re]
  rw [hre]
  refine ⟨Real.neg_one_le_cos θ, ?_⟩
  by_cases hθ : θ ≤ Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hε.le hθ hlo
  · calc
      Real.cos θ = Real.cos (2 * Real.pi - θ) := (Real.cos_two_pi_sub θ).symm
      _ ≤ Real.cos ε := Real.cos_le_cos_of_nonneg_of_le_pi hε.le
        (by linarith only [hθ]) (by linarith only [hhi])

/-- Every column of a matrix satisfying `star B * B = 1` is nonzero. -/
theorem jw_unitary_basis_column_ne_zero (m : ℕ) (B : Matrix (Fin m) (Fin m) ℂ)
    (hB : star B * B = 1) (j : Fin m) : (fun i => B i j) ≠ 0 := by
  intro hj
  have hdiag := congrArg (fun A : Matrix (Fin m) (Fin m) ℂ => A j j) hB
  have hz (i : Fin m) : B i j = 0 := congrFun hj i
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    hz, star_zero, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq] at hdiag
  exact zero_ne_one hdiag

/-- Replacing the real part of every fixed eigenvalue by `-1` puts all eigenbasis values in
`[-1, cos ε]` under the phase-gap hypothesis. -/
theorem jw_unitary_basis_real_gap (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (U B : Matrix (Fin m) (Fin m) ℂ) (start : Fin m → ℂ) (μ : Fin m → ℂ)
    (hu : star U * U = 1) (hB : star B * B = 1) (hstart : U *ᵥ start = start)
    (heigen : ∀ j, U *ᵥ (fun i => B i j) = μ j • (fun i => B i j))
    (hphase : ∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
      (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ θ ≠ Real.pi ∧
        ν = Complex.exp (Complex.I * θ)) :
    ∀ j, -1 ≤ (if μ j = 1 then -1 else (μ j).re) ∧
      (if μ j = 1 then -1 else (μ j).re) ≤ Real.cos ε := by
  intro j
  by_cases hj : μ j = 1
  · simp only [if_pos hj]
    exact ⟨le_refl _, Real.neg_one_le_cos ε⟩
  · simp only [if_neg hj]
    exact jw_nonfixed_eigenvalue_real_gap m ε hε U start (fun i => B i j) (μ j)
      hu hstart (heigen j) hj (jw_unitary_basis_column_ne_zero m B hB j) hphase

/-- The small-overlap phase endpoints form a nonempty positive interval below `ε`, on which the
sine is nonnegative. -/
theorem grover_small_interval_bounds (ε α : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 0 < α) (hsmall : α ≤ ε ^ 2 / 200) :
    let lo := ε * α / Real.sqrt (2 * Real.pi)
    let hi := (13 / 5 : ℝ) * α
    0 < lo ∧ lo ≤ hi ∧ hi < ε ∧
      (∀ β ∈ Set.Icc lo hi, 0 < β ∧ β < ε ∧ 0 ≤ Real.sin β) := by
  let lo := ε * α / Real.sqrt (2 * Real.pi)
  let hi := (13 / 5 : ℝ) * α
  have hs : 1 ≤ Real.sqrt (2 * Real.pi) := by
    have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
    have hnn := Real.sqrt_nonneg (2 * Real.pi)
    nlinarith only [hsq, hnn, Real.pi_gt_three]
  have hlop : 0 < lo := by dsimp [lo]; positivity
  have hloa : lo ≤ ε * α := div_le_self (by positivity) hs
  have he2 : ε ^ 2 ≤ ε := by nlinarith only [hε, hε1]
  have ha1 : α ≤ 1 / 200 := by nlinarith only [hsmall, he2, hε1]
  have hlohi : lo ≤ hi := by dsimp only [hi]; nlinarith only [hloa, hε1, hα]
  have hhie : hi < ε := by dsimp only [hi]; nlinarith only [hsmall, he2, hε]
  refine ⟨hlop, hlohi, hhie, ?_⟩
  intro β hβ
  have hb0 : 0 < β := hlop.trans_le hβ.1
  have hbe : β < ε := hβ.2.trans_lt hhie
  exact ⟨hb0, hbe, Real.sin_nonneg_of_nonneg_of_le_pi hb0.le
    (by linarith only [hbe, hε1, Real.pi_gt_three])⟩

/-- Applying an invertible matrix inverse divides the coefficients in its unitary eigenbasis by
the eigenvalues. -/
theorem jw_eigenbasis_inverse_mulVec (m : ℕ)
    (K B : Matrix (Fin m) (Fin m) ℂ) (eig : Fin m → ℂ)
    (hB : star B * B = 1) (hB' : B * star B = 1) (hK : IsUnit K)
    (he : ∀ j, K *ᵥ (fun i => B i j) = eig j • (fun i => B i j))
    (v : Fin m → ℂ) :
    K⁻¹ *ᵥ v = B *ᵥ (fun j => (star B *ᵥ v) j / eig j) := by
  classical
  have heig (j : Fin m) : eig j ≠ 0 := by
    intro hz
    have hc : (fun i => B i j) = 0 := by
      apply Matrix.mulVec_injective_iff_isUnit.mpr hK
      simpa only [hz, zero_smul, Matrix.mulVec_zero] using he j
    exact jw_unitary_basis_column_ne_zero m B hB j hc
  let D := Matrix.diagonal (fun j => (eig j)⁻¹)
  have hKB : K * B = B * Matrix.diagonal eig := by
    ext i j
    rw [Matrix.mul_diagonal]
    have h := congrFun (he j) i
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.smul_apply,
      smul_eq_mul, mul_comm] using h
  have hD : Matrix.diagonal eig * D = 1 := by
    simp only [D, Matrix.diagonal_mul_diagonal, mul_inv_cancel₀ (heig _)]
    exact Matrix.diagonal_one
  have hKD : K * (B * D) = B := by
    rw [← Matrix.mul_assoc, hKB, Matrix.mul_assoc, hD, Matrix.mul_one]
  have hinv : K⁻¹ * B = B * D := by
    have h := congrArg (fun A => K⁻¹ * A) hKD
    try dsimp only at h
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp hK), Matrix.one_mul] at h
    exact h.symm
  have hv : v = B *ᵥ (star B *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hB', Matrix.one_mulVec]
  calc
    _ = (K⁻¹ * B) *ᵥ (star B *ᵥ v) := by rw [← Matrix.mulVec_mulVec, ← hv]
    _ = B *ᵥ (D *ᵥ (star B *ᵥ v)) := by rw [hinv, ← Matrix.mulVec_mulVec]
    _ = _ := by
      congr 1
      ext j
      simp only [D, Matrix.mulVec_diagonal, div_eq_mul_inv, mul_comm]

/-- The squared norm after applying an inverse equals the sum of squared eigenbasis coefficients
divided by squared eigenvalue norms. -/
theorem jw_eigenbasis_inverse_norm_sq (m : ℕ)
    (K B : Matrix (Fin m) (Fin m) ℂ) (eig : Fin m → ℂ)
    (hB : star B * B = 1) (hB' : B * star B = 1) (hK : IsUnit K)
    (he : ∀ j, K *ᵥ (fun i => B i j) = eig j • (fun i => B i j))
    (v : Fin m → ℂ) :
    (∑ i, ‖(K⁻¹ *ᵥ v) i‖ ^ 2) = ∑ j, ‖(star B *ᵥ v) j‖ ^ 2 / ‖eig j‖ ^ 2 := by
  rw [jw_eigenbasis_inverse_mulVec m K B eig hB hB' hK he v,
    jw_unitary_mulVec_norm_sq m B hB]
  simp only [norm_div, div_pow]

/-- The resolvent vector has squared norm equal to the sum of target spectral weights divided by
`‖μ j - z‖^2`. -/
theorem jw_unitary_eigenbasis_resolvent_norm_sq (m : ℕ)
    (U B : Matrix (Fin m) (Fin m) ℂ) (μ : Fin m → ℂ)
    (hB : star B * B = 1) (hB' : B * star B = 1)
    (hμ : ∀ j, ‖μ j‖ = 1)
    (he : ∀ j, U *ᵥ (fun i => B i j) = μ j • (fun i => B i j))
    (good : Fin m → ℂ) (z : ℂ)
    (hz : IsUnit (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))) :
    (∑ i, ‖((U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)) i‖ ^ 2) =
      ∑ j, ‖(star B *ᵥ good) j‖ ^ 2 / ‖μ j - z‖ ^ 2 := by
  classical
  have hUB : U * B = B * Matrix.diagonal μ := by
    ext i j
    rw [Matrix.mul_diagonal]
    have h := congrFun (he j) i
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.smul_apply,
      smul_eq_mul, mul_comm] using h
  have hBU : star B * U = Matrix.diagonal μ * star B := by
    have hmat : star B * U * B = Matrix.diagonal μ := by
      rw [Matrix.mul_assoc, hUB, ← Matrix.mul_assoc, hB, Matrix.one_mul]
    have h := congrArg (fun A => A * star B) hmat
    simpa only [Matrix.mul_assoc, hB', Matrix.mul_one] using h
  have hcoeff : star B *ᵥ (U *ᵥ good) = Matrix.diagonal μ *ᵥ (star B *ᵥ good) := by
    rw [Matrix.mulVec_mulVec, hBU, ← Matrix.mulVec_mulVec]
  have hAe (j : Fin m) :
      (U - z • (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ (fun i => B i j) =
        (μ j - z) • (fun i => B i j) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, he, ← sub_smul]
  rw [jw_eigenbasis_inverse_norm_sq m (U - z • 1) B (fun j => μ j - z)
    hB hB' hz hAe (U *ᵥ good)]
  simp only [hcoeff, Matrix.mulVec_diagonal, norm_mul, hμ, one_mul]

/-- A unitary matrix has an orthonormal eigenbasis realizing the spectral sum formula for the
squared resolvent-vector norm. -/
theorem jw_unitary_resolvent_norm_sq_exists (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (hu : star U * U = 1)
    (good : Fin m → ℂ) (z : ℂ)
    (hz : IsUnit (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))) :
    ∃ (B : Matrix (Fin m) (Fin m) ℂ) (μ : Fin m → ℂ),
      star B * B = 1 ∧ B * star B = 1 ∧ (∀ j, ‖μ j‖ = 1) ∧
      (∀ j, U *ᵥ (fun i => B i j) = μ j • (fun i => B i j)) ∧
      (∑ i, ‖((U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)) i‖ ^ 2) =
        ∑ j, ‖(star B *ᵥ good) j‖ ^ 2 / ‖μ j - z‖ ^ 2 := by
  obtain ⟨B, μ, hB, hB', hμ, he⟩ := jw_unitary_orthonormal_eigenbasis m U hu
  exact ⟨B, μ, hB, hB', hμ, he,
    jw_unitary_eigenbasis_resolvent_norm_sq m U B μ hB hB' hμ he good z hz⟩

/-- Eigenvectors of a unitary matrix with distinct eigenvalues are orthogonal when the first
eigenvalue has modulus one. -/
theorem jw_unitary_distinct_eigenvectors_orthogonal (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (v w : Fin m → ℂ) (μ ν : ℂ)
    (hu : star U * U = 1) (hμ : star μ * μ = 1)
    (hv : U *ᵥ v = μ • v) (hw : U *ᵥ w = ν • w) (hne : μ ≠ ν) :
    star v ⬝ᵥ w = 0 := by
  have hinner : star (U *ᵥ v) ⬝ᵥ (U *ᵥ w) = star v ⬝ᵥ w := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    change star v ⬝ᵥ ((star U * U) *ᵥ w) = _
    rw [hu, Matrix.one_mulVec]
  have hc : (star μ * ν - 1) * (star v ⬝ᵥ w) = 0 := by
    rw [hv, hw, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul] at hinner
    linear_combination hinner
  have hcoeff : star μ * ν - 1 ≠ 0 := by
    intro hz
    have hμ0 : star μ ≠ 0 := by
      intro hzero
      simp only [hzero, zero_mul] at hμ
      exact zero_ne_one hμ
    have heq : star μ * ν = star μ * μ := (sub_eq_zero.mp hz).trans hμ.symm
    exact hne (mul_left_cancel₀ hμ0 heq).symm
  exact (mul_eq_zero.mp hc).resolve_left hcoeff

/-- An eigenvector of a real unitary matrix with phase in `(0, π)` is orthogonal to its complex
conjugate. -/
theorem jw_real_unitary_eigenvector_conjugate_orthogonal (m : ℕ) (β : ℝ)
    (hβ : 0 < β) (hβπ : β < Real.pi)
    (U : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ)
    (hu : star U * U = 1) (hreal : ∀ i j, (U i j).im = 0)
    (hy : U *ᵥ y = Complex.exp (Complex.I * β) • y) :
    star y ⬝ᵥ star y = 0 := by
  let μ := Complex.exp (Complex.I * β)
  have hμ : star μ * μ = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
    simp [μ, Complex.norm_exp]
  have hconjU (i j : Fin m) : star (U i j) = U i j :=
    Complex.conj_eq_iff_im.mpr (hreal i j)
  have hyconj : U *ᵥ star y = star μ • star y := by
    have h := congrArg star hy
    ext i
    have hi := congrFun h i
    simpa only [Matrix.mulVec, dotProduct, star_sum, star_mul,
      Pi.star_apply, star_smul, Pi.smul_apply, hconjU, mul_comm] using hi
  have him : 0 < μ.im := by
    simpa [μ, Complex.exp_im] using Real.sin_pos_of_pos_of_lt_pi hβ hβπ
  have hne : μ ≠ star μ := by
    intro heq
    have hi := congrArg Complex.im heq
    simp only [Complex.star_def, Complex.conj_im] at hi
    linarith only [hi, him]
  exact jw_unitary_distinct_eigenvectors_orthogonal m U y (star y) μ (star μ)
    hu hμ hy hyconj hne

/-- The real and imaginary parts of such an eigenvector are orthogonal with equal squared norms,
each half the full squared norm. -/
theorem jw_real_unitary_eigenvector_parts (m : ℕ) (β : ℝ)
    (hβ : 0 < β) (hβπ : β < Real.pi)
    (U : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ)
    (hu : star U * U = 1) (hreal : ∀ i j, (U i j).im = 0)
    (hy : U *ᵥ y = Complex.exp (Complex.I * β) • y) :
    (∑ i, (y i).re ^ 2) = (∑ i, (y i).im ^ 2) ∧
      (∑ i, (y i).re * (y i).im) = 0 ∧
      (∑ i, ‖y i‖ ^ 2) = 2 * (∑ i, (y i).im ^ 2) := by
  have ho := jw_real_unitary_eigenvector_conjugate_orthogonal m β hβ hβπ U y hu hreal hy
  have hz : (∑ i, y i * y i) = 0 := by
    have h := congrArg star ho
    simpa only [dotProduct, Pi.star_apply, star_sum, star_mul, star_star, star_zero] using h
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.re_sum, Complex.mul_re, Complex.zero_re] at hre
  simp only [Complex.im_sum, Complex.mul_im, Complex.zero_im] at him
  have hnorm (i : Fin m) : ‖y i‖ ^ 2 = (y i).re ^ 2 + (y i).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have heq : (∑ i, (y i).re ^ 2) = ∑ i, (y i).im ^ 2 := by
    simp only [← pow_two, Finset.sum_sub_distrib] at hre
    exact sub_eq_zero.mp hre
  have horth : (∑ i, (y i).re * (y i).im) = 0 := by
    have ht (i : Fin m) : (y i).re * (y i).im + (y i).im * (y i).re =
        2 * ((y i).re * (y i).im) := by ring
    simp only [ht, ← Finset.mul_sum] at him
    linarith only [him]
  refine ⟨heq, horth, ?_⟩
  simp only [hnorm, Finset.sum_add_distrib, heq]
  ring

/-- A matrix power acts on an eigenvector by the corresponding power of its eigenvalue. -/
theorem jw_matrix_eigenvector_power (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ) (μ : ℂ)
    (hy : U *ᵥ y = μ • y) (t : ℕ) : U ^ t *ᵥ y = μ ^ t • y := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hy, smul_smul,
      pow_succ]

/-- Powers of a real matrix rotate the imaginary part of a phase eigenvector into the stated
sine-cosine combination of its real and imaginary parts. -/
theorem jw_real_matrix_eigenvector_power_imaginary (m : ℕ) (β : ℝ)
    (U : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ)
    (hreal : ∀ i j, (U i j).im = 0)
    (hy : U *ᵥ y = Complex.exp (Complex.I * β) • y) (t : ℕ) :
    U ^ t *ᵥ (fun i => ((y i).im : ℂ)) =
      (Real.sin ((t : ℝ) * β) : ℂ) • (fun i => ((y i).re : ℂ)) +
        (Real.cos ((t : ℝ) * β) : ℂ) • (fun i => ((y i).im : ℂ)) := by
  classical
  let μ := Complex.exp (Complex.I * β)
  have hconjU (i j : Fin m) : star (U i j) = U i j :=
    Complex.conj_eq_iff_im.mpr (hreal i j)
  have hyconj : U *ᵥ star y = star μ • star y := by
    have h := congrArg star hy
    ext i
    have hi := congrFun h i
    simpa only [Matrix.mulVec, dotProduct, star_sum, star_mul,
      Pi.star_apply, star_smul, Pi.smul_apply, hconjU, mul_comm] using hi
  have hp : μ ^ t = Complex.exp (Complex.I * ((t : ℝ) * β)) := by
    dsimp only [μ]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have himvec : (fun i => ((y i).im : ℂ)) = (-Complex.I / 2) • (y - star y) := by
    ext i
    apply Complex.ext
    all_goals simp [Pi.smul_apply, Pi.sub_apply, Pi.star_apply, Complex.mul_re, Complex.mul_im]
    all_goals ring
  rw [himvec, Matrix.mulVec_smul, Matrix.mulVec_sub,
    jw_matrix_eigenvector_power m U y μ hy t,
    jw_matrix_eigenvector_power m U (star y) (star μ) hyconj t, ← star_pow, hp]
  have hcast : (t : ℂ) * (β : ℂ) = (((t : ℝ) * β : ℝ) : ℂ) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
  ext i
  apply Complex.ext <;>
    simp [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.star_apply,
      Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  all_goals rw [hcast]
  all_goals simp only [Complex.cos_ofReal_re, Complex.sin_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_im, zero_mul, zero_add]
  all_goals ring

/-- For orthogonal vectors of equal norm, the distance of the sine-cosine combination from the
first vector is at most the quarter-turn angle error times their norm. -/
theorem jw_quarter_rotation_norm_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u v : E) (τ : ℝ)
    (hn : ‖u‖ = ‖v‖) (ho : ⟪u, v⟫_ℂ = 0) :
    ‖(Real.sin τ : ℂ) • u + (Real.cos τ : ℂ) • v - u‖ ≤
      |Real.pi / 2 - τ| * ‖v‖ := by
  have he : (Real.sin τ : ℂ) • u + (Real.cos τ : ℂ) • v - u =
      ((Real.sin τ - 1 : ℝ) : ℂ) • u + (Real.cos τ : ℂ) • v := by
    push_cast
    module
  rw [he]
  have horth : ⟪((Real.sin τ - 1 : ℝ) : ℂ) • u, (Real.cos τ : ℂ) • v⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_right, ho, mul_zero, mul_zero]
  have hnormsq :
      ‖((Real.sin τ - 1 : ℝ) : ℂ) • u + (Real.cos τ : ℂ) • v‖ ^ 2 =
        ((Real.sin τ - 1) ^ 2 + Real.cos τ ^ 2) * ‖v‖ ^ 2 := by
    rw [pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth,
      norm_smul, norm_smul, hn]
    simp only [Complex.norm_real, Real.norm_eq_abs, ← pow_two, mul_pow, sq_abs]
    ring
  have htrig : (Real.sin τ - 1) ^ 2 + Real.cos τ ^ 2 ≤ (Real.pi / 2 - τ) ^ 2 := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 2 - τ)
    rw [Real.cos_pi_div_two_sub] at hc
    nlinarith only [hc, Real.sin_sq_add_cos_sq τ]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))).mp
  rw [hnormsq, mul_pow, sq_abs]
  exact mul_le_mul_of_nonneg_right htrig (sq_nonneg _)

/-- An iteration angle within `β` below a quarter turn sends the imaginary eigenvector part
within `β` times its norm of the real part. -/
theorem jw_real_unitary_quarter_iteration (m : ℕ) (β : ℝ)
    (hβ : 0 < β) (hβπ : β < Real.pi)
    (U : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ)
    (hu : star U * U = 1) (hreal : ∀ i j, (U i j).im = 0)
    (hy : U *ᵥ y = Complex.exp (Complex.I * β) • y) (t : ℕ)
    (ht : 0 ≤ Real.pi / 2 - (t : ℝ) * β ∧ Real.pi / 2 - (t : ℝ) * β ≤ β) :
    ‖(WithLp.toLp 2 (U ^ t *ᵥ (fun i => ((y i).im : ℂ)) -
        (fun i => ((y i).re : ℂ))) : EuclideanSpace ℂ (Fin m))‖ ≤
      β * ‖(WithLp.toLp 2 (fun i => ((y i).im : ℂ)) : EuclideanSpace ℂ (Fin m))‖ := by
  let u : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun i => ((y i).re : ℂ))
  let v : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun i => ((y i).im : ℂ))
  obtain ⟨hnparts, hoparts, _⟩ := jw_real_unitary_eigenvector_parts m β hβ hβπ U y hu hreal hy
  have hn : ‖u‖ = ‖v‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [u, v, PiLp.norm_sq_eq_of_L2, Complex.norm_real, Real.norm_eq_abs,
      sq_abs] using hnparts
  have ho : ⟪u, v⟫_ℂ = 0 := by
    change (∑ i, ⟪((y i).re : ℂ), ((y i).im : ℂ)⟫_ℂ) = 0
    simp only [RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum]
    rw [show (∑ i, (y i).im * (y i).re) = 0 by
      simpa only [mul_comm] using hoparts]
    rfl
  rw [jw_real_matrix_eigenvector_power_imaginary m β U y hreal hy t]
  change ‖(Real.sin ((t : ℝ) * β) : ℂ) • u +
      (Real.cos ((t : ℝ) * β) : ℂ) • v - u‖ ≤ β * ‖v‖
  have hraw := jw_quarter_rotation_norm_bound u v ((t : ℝ) * β) hn ho
  rw [abs_of_nonneg ht.1] at hraw
  exact hraw.trans (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _))

/-- After normalization by the positive imaginary-part norm, the quarter-turn approximation
error is at most `β`. -/
theorem jw_real_unitary_normalized_quarter_iteration (m : ℕ) (β : ℝ)
    (hβ : 0 < β) (hβπ : β < Real.pi)
    (U : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ)
    (hu : star U * U = 1) (hreal : ∀ i j, (U i j).im = 0)
    (hy : U *ᵥ y = Complex.exp (Complex.I * β) • y) (t : ℕ)
    (ht : 0 ≤ Real.pi / 2 - (t : ℝ) * β ∧ Real.pi / 2 - (t : ℝ) * β ≤ β)
    (hs : 0 < ‖(WithLp.toLp 2 (fun i => ((y i).im : ℂ)) : EuclideanSpace ℂ (Fin m))‖) :
    let s := ‖(WithLp.toLp 2 (fun i => ((y i).im : ℂ)) : EuclideanSpace ℂ (Fin m))‖
    ‖(WithLp.toLp 2 (U ^ t *ᵥ ((s⁻¹ : ℂ) • (fun i => ((y i).im : ℂ))) -
        (s⁻¹ : ℂ) • (fun i => ((y i).re : ℂ))) : EuclideanSpace ℂ (Fin m))‖ ≤ β := by
  let s := ‖(WithLp.toLp 2 (fun i => ((y i).im : ℂ)) : EuclideanSpace ℂ (Fin m))‖
  have hraw := jw_real_unitary_quarter_iteration m β hβ hβπ U y hu hreal hy t ht
  change ‖(WithLp.toLp 2 (U ^ t *ᵥ ((s⁻¹ : ℂ) • (fun i => ((y i).im : ℂ))) -
    (s⁻¹ : ℂ) • (fun i => ((y i).re : ℂ))) : EuclideanSpace ℂ (Fin m))‖ ≤ β
  rw [Matrix.mulVec_smul, ← smul_sub]
  change ‖(s⁻¹ : ℂ) • (WithLp.toLp 2 (U ^ t *ᵥ (fun i => ((y i).im : ℂ)) -
    (fun i => ((y i).re : ℂ))) : EuclideanSpace ℂ (Fin m))‖ ≤ β
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have h := mul_le_mul_of_nonneg_left hraw (by positivity : 0 ≤ s⁻¹)
  change s⁻¹ * _ ≤ s⁻¹ * (β * s) at h
  have hs0 : s ≠ 0 := ne_of_gt hs
  have he : s⁻¹ * (β * s) = β := by field_simp
  exact h.trans_eq he

end Qatlib.Concepts.WalkFind.GroverInterp
