/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralGap11.MainResults.EigenReduction
public import Qatlib.Papers.SpectralGap11.MainResults.Nullity
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Gap amplification on the actual doubled oracle register

The construction follows [BoixoSomma2012SpectralGap], Theorem 1 and Proof 2,
with an extra idle branch in the oracle register.
[Fixed source](https://arxiv.org/abs/1110.2494v3).
The repaired statement ties the input gap to actual eigenpairs of `sum Proj`,
uses the source's lazy compression `gamma=1-lambda/L`, measures the output
gap around zero, and proves equality of the full null-space dimensions.
Its constant `1/2` is uniform in the dimension, projectors, and input gap.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.SpectralGap11.MainResults

open Matrix
open AmplifiedRegister EigenReduction
open scoped BigOperators

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

omit [DecidableEq I] in
/-- The input gap is an actual spectral lower bound on the input matrix;
the spectral interval `[0,L]` is the source normalization for a sum of `L`
orthogonal projectors. No output-matrix conclusion appears in this premise. -/
def InputGap (H : Matrix I I ℂ) (Delta L : ℝ) : Prop :=
  ∀ (lambda : ℝ) (psi : I → ℂ), psi ≠ 0 → H *ᵥ psi = (lambda : ℂ) • psi →
    0 ≤ lambda ∧ lambda ≤ L ∧ (lambda = 0 ∨ Delta ≤ lambda)

/-- The actual Hermitian input has a complete unitary eigenbasis satisfying
the supplied input-gap condition. -/
private theorem canonical_input (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (Delta L : ℝ) (hgap : InputGap H Delta L) :
    ∃ (V : Matrix I I ℂ) (lambda : I → ℝ),
      Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧
      Vᴴ * H * V = Matrix.diagonal (fun j => (lambda j : ℂ)) ∧
      ∀ j, 0 ≤ lambda j ∧ lambda j ≤ L ∧ (lambda j = 0 ∨ Delta ≤ lambda j) := by
  let V : Matrix I I ℂ := hH.eigenvectorUnitary
  refine ⟨V, hH.eigenvalues, ?_, ?_, ?_, ?_⟩
  · exact Unitary.coe_star_mul_self hH.eigenvectorUnitary
  · exact Unitary.coe_mul_star_self hH.eigenvectorUnitary
  · have h := hH.conjStarAlgAut_star_eigenvectorUnitary
    dsimp [V]
    simp only [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] at h
    convert h using 1
  · intro j
    let psi : I → ℂ := (hH.eigenvectorBasis j).ofLp
    have hn : psi ≠ 0 := by
      intro hz
      apply hH.eigenvectorBasis.toBasis.ne_zero j
      ext i
      exact congrFun hz i
    apply hgap (hH.eigenvalues j) psi hn
    change H *ᵥ (hH.eigenvectorBasis j).ofLp =
      (hH.eigenvalues j : ℂ) • (hH.eigenvectorBasis j).ofLp
    funext i
    have hi := congrFun (hH.mulVec_eigenvectorBasis j) i
    simp only [Pi.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ)] at hi
    exact hi

/-- The actual input diagonalization induces the lazy compression cosine. -/
private theorem affine_diagonal (H V : Matrix I I ℂ) (lambda : I → ℝ) (L : ℂ)
    (hV : Vᴴ * V = 1)
    (hdiag : Vᴴ * H * V = Matrix.diagonal (fun j => (lambda j : ℂ))) :
    Vᴴ * (1 - L⁻¹ • H) * V =
      Matrix.diagonal (fun j => 1 - L⁻¹ * (lambda j : ℂ)) := by
  calc
    Vᴴ * (1 - L⁻¹ • H) * V = Vᴴ * V - L⁻¹ • (Vᴴ * H * V) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.sub_mul,
        Matrix.smul_mul]
    _ = 1 - L⁻¹ • Matrix.diagonal (fun j => (lambda j : ℂ)) := by rw [hV, hdiag]
    _ = _ := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]

/-- Every full output eigenvector has the uniform gap, including vectors
whose input compression vanishes. The input basis diagonalizes the actual
compression, rather than a separately postulated output operator. -/
private theorem gap_from_diagonal {R : Type*} [Fintype R] [DecidableEq R]
    (J : Matrix R I ℂ) (U : Matrix R R ℂ) (hJ : Jᴴ * J = 1) (hU : U * U = 1)
    (V : Matrix I I ℂ) (lambda : I → ℝ) (hVV : V * Vᴴ = 1)
    (Delta L delta : ℝ) (hDelta : 0 < Delta) (hL : 0 < L) (hd : 0 ≤ delta)
    (hdsq : delta ^ 2 = Delta * L)
    (hbounds : ∀ j, 0 ≤ lambda j ∧ lambda j ≤ L ∧
      (lambda j = 0 ∨ Delta ≤ lambda j))
    (hdiag : Vᴴ * (Jᴴ * U * J) * V =
      Matrix.diagonal (fun j => 1 - (L : ℂ)⁻¹ * (lambda j : ℂ)))
    (mu : ℝ) (v : R → ℂ) (hv : v ≠ 0) (hmu : mu ≠ 0)
    (heigen : fullPenalty J U (L : ℂ) (delta : ℂ) *ᵥ v = (mu : ℂ) • v) :
    delta / 2 ≤ |mu| := by
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  by_cases hcompress : Jᴴ *ᵥ v = 0
  · obtain hm | hm := complementary_eigenvalue J U (L : ℂ) (delta : ℂ) (mu : ℂ)
      hJ hU hLC v hv hcompress heigen
    · have hmreal : mu = delta := by exact_mod_cast hm
      rw [hmreal, abs_of_nonneg hd]
      linarith
    · have hmreal : mu = L + delta := by exact_mod_cast hm
      rw [hmreal, abs_of_nonneg (by linarith : 0 ≤ L + delta)]
      linarith
  · let z := Vᴴ *ᵥ (Jᴴ *ᵥ v)
    have hz : z ≠ 0 := by
      intro hz0
      apply hcompress
      calc
        Jᴴ *ᵥ v = V *ᵥ z := by
          dsimp [z]
          rw [Matrix.mulVec_mulVec, hVV, Matrix.one_mulVec]
        _ = 0 := by rw [hz0, Matrix.mulVec_zero]
    obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
      by_contra hnone
      apply hz
      funext j
      by_contra hne
      exact hnone ⟨j, hne⟩
    have hc := eigen_coordinate J U (L : ℂ) (delta : ℂ) (mu : ℂ) hJ hU V
      (fun j => 1 - (L : ℂ)⁻¹ * (lambda j : ℂ)) hVV hdiag v heigen j
    have hscalar : (mu : ℂ) ^ 2 - (delta : ℂ) * (mu : ℂ) =
        (L : ℂ) * ((L : ℂ) + (delta : ℂ)) *
          (1 - (1 - (L : ℂ)⁻¹ * (lambda j : ℂ)) ^ 2) :=
      mul_right_cancel₀ hj hc
    have hpoly : mu ^ 2 - delta * mu =
        L * (L + delta) * (1 - (1 - lambda j / L) ^ 2) := by
      apply Complex.ofReal_injective
      push_cast
      convert hscalar using 1
      rw [div_eq_mul_inv]
      ring
    obtain ⟨hl0, hlL, hlcase⟩ := hbounds j
    rcases hlcase with hlzero | hlgap
    · rw [hlzero] at hpoly
      simp only [zero_div, sub_zero, one_pow, sub_self, mul_zero] at hpoly
      have hmprod : mu * (mu - delta) = 0 := by nlinarith only [hpoly]
      have hmreal : mu = delta := sub_eq_zero.1 ((mul_eq_zero.1 hmprod).resolve_left hmu)
      rw [hmreal, abs_of_nonneg hd]
      linarith
    · have hlpos : 0 < lambda j := lt_of_lt_of_le hDelta hlgap
      have hdsmall : delta ^ 2 ≤ lambda j * L := by nlinarith
      have hg := GapReduction.characteristic_gap (lambda j) L delta mu hL hlpos hlL
        hd hdsmall hpoly
      have hs := Real.sq_sqrt (mul_pos hlpos hL).le
      have hsn := Real.sqrt_nonneg (lambda j * L)
      have hdroot : delta ≤ Real.sqrt (lambda j * L) := by
        nlinarith only [hdsmall, hs, hsn, hd]
      linarith

/-- Source Theorem 1 on the actual repaired register: the lifted ground
state is annihilated, every nonzero eigenvalue has a uniform square-root
gap around zero, and the entire input nullity is preserved. -/
theorem doubled_register_gap_and_nullity (Proj : K → Matrix I I ℂ)
    (hproj : ∀ k, Proj k * Proj k = Proj k)
    (hHerm : ∀ k, (Proj k).IsHermitian) (hK : 0 < Fintype.card K)
    (psi : I → ℂ) (hground : ∀ k, Proj k *ᵥ psi = 0)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : InputGap (∑ k, Proj k) Delta (Fintype.card K : ℝ)) :
    let delta := Real.sqrt (Delta * Fintype.card K)
    doubledHamiltonian Proj (delta : ℂ) *ᵥ
        (uniformEmbed (K := K × Bool) (ancAmplitude (K := K)) *ᵥ psi) = 0 ∧
      (∀ (mu : ℝ) (v : I × (K × Bool) → ℂ), v ≠ 0 →
        doubledHamiltonian Proj (delta : ℂ) *ᵥ v = (mu : ℂ) • v → mu ≠ 0 → delta / 2 ≤ |mu|) ∧
      Module.finrank ℂ (LinearMap.ker (doubledHamiltonian Proj (delta : ℂ)).mulVecLin) =
        Module.finrank ℂ (LinearMap.ker (∑ k, Proj k).mulVecLin) := by
  let L : ℝ := Fintype.card K
  let delta := Real.sqrt (Delta * L)
  have hL : 0 < L := by
    dsimp [L]
    exact_mod_cast hK
  have hd : 0 < delta := Real.sqrt_pos.2 (mul_pos hDelta hL)
  have hdsq : delta ^ 2 = Delta * L := Real.sq_sqrt (mul_pos hDelta hL).le
  have hdC : (delta : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hLdC : (Fintype.card K : ℂ) + (delta : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < L + delta by linarith))
  refine ⟨ground_amplified_zero Proj hK psi hground _, ?_,
    doubled_kernel_finrank_eq Proj hproj hHerm hK (delta : ℂ) hdC hLdC⟩
  intro mu v hv heigen hmu
  have hH : (∑ k, Proj k).IsHermitian := by
    change (∑ k, Proj k)ᴴ = ∑ k, Proj k
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl (fun k _ => (hHerm k).eq)
  obtain ⟨V, lambda, hVH, hVV, hdiagH, hbounds⟩ :=
    canonical_input (∑ k, Proj k) hH Delta L hgap
  let J := uniformEmbed (I := I) (K := K × Bool) (ancAmplitude (K := K))
  have hdiagA : Vᴴ * (Jᴴ * lazyOracle Proj * J) * V =
      Matrix.diagonal (fun j => 1 - (L : ℂ)⁻¹ * (lambda j : ℂ)) := by
    have hcomp : Jᴴ * lazyOracle Proj * J =
        1 - (Fintype.card K : ℂ)⁻¹ • ∑ k, Proj k := lazy_compression Proj hK
    rw [hcomp]
    exact affine_diagonal (∑ k, Proj k) V lambda _ hVH hdiagH
  exact gap_from_diagonal J (lazyOracle Proj) (lazyEmbed_isometry hK)
    (lazyOracle_sq Proj hproj) V lambda hVV Delta L delta hDelta hL hd.le hdsq
    hbounds hdiagA mu v hv hmu heigen

end

end Qatlib.Papers.SpectralGap11.MainResults
