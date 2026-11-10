/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma2Stat
import Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma1Sear
import Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma2AttemptAuxiliary
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MnrsAmplify
open scoped Real BigOperators
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

private theorem mnrs_sqrt_numeric : (7/10 : ℝ) ≤ 1/Real.sqrt 2 ∧
    Real.sqrt (1/6) ≤ (41/100 : ℝ) := by
  constructor
  · apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
    apply (sq_le_sq₀ (by positivity) (by norm_num : (0 : ℝ) ≤ 1)).mp
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [h]
  · have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/6)
    nlinarith only [h, Real.sqrt_nonneg (1/6)]

private theorem mnrs2_sqrt_two_div_two : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  field_simp
  nlinarith only [hsq]

private theorem mnrs2_one_div_sqrt_two_le : 1 / Real.sqrt 2 ≤ 99 / 140 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hA : (99 / 140 * Real.sqrt 2) ^ 2 = 2 * (99 / 140) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  have h1 : (1 : ℝ) ^ 2 ≤ (99 / 140 * Real.sqrt 2) ^ 2 := by
    rw [hA]; norm_num
  have h3 : (0 : ℝ) ≤ 99 / 140 * Real.sqrt 2 := by positivity
  exact (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
    ((sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) h3).mp h1)

private theorem mnrs2_sin_window (a : ℝ) (ha : a ∈ Set.Icc (π / 4) (3 * π / 4)) :
    1 / Real.sqrt 2 ≤ Real.sin a := by
  have hs : Real.sin (π / 4) ≤ Real.sin a := by
    by_cases h : a ≤ π / 2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h ha.1
    · have h' := Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos] : -(π / 2) ≤ π / 4)
        (by linarith : π - a ≤ π / 2) (by linarith [ha.2] : π / 4 ≤ π - a)
      simpa only [Real.sin_pi_sub] using h'
  rw [Real.sin_pi_div_four] at hs
  rwa [mnrs2_sqrt_two_div_two] at hs

private theorem mnrs2_unmarked_norm_le (Mr : Submodule ℂ W) (ψ : W) :
    ‖ψ - markProj Mr ψ‖ ≤ ‖ψ‖ := by
  set y : W := markProj Mr ψ with hydef
  set z : W := ψ - y with hzdef
  have hy : y ∈ Mr := by rw [hydef]; exact (Mr.orthogonalProjection ψ).property
  have hz : z ∈ Mrᗮ := by
    rw [hzdef, hydef, mnrs_mark_projection_eq]
    exact Submodule.sub_starProjection_mem_orthogonal ψ
  have hyz : inner ℂ y z = 0 := (Mr.mem_orthogonal _).mp hz _ hy
  have hzy : inner ℂ z y = 0 := by rw [← inner_conj_symm, hyz, map_zero]
  have hsplit : ψ = y + z := by rw [hzdef]; abel
  have hsq : ‖ψ‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
    have he : inner ℂ ψ ψ = inner ℂ y y + inner ℂ z z := by
      rw [hsplit, inner_add_add_self, hyz, hzy]
      ring
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K] at he
    exact_mod_cast he
  have h1 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have h2 : (0 : ℝ) ≤ ‖y‖ ^ 2 := sq_nonneg _
  have h3 : ‖z‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by linarith
  exact (sq_le_sq₀ h1 (norm_nonneg ψ)).mp h3

private theorem mnrs2_normalize_sub (a b : W) (hc : 2 / 3 ≤ ‖b‖) :
    ‖NormedSpace.normalize a - NormedSpace.normalize b‖ ≤ 3 * ‖a - b‖ := by
  have hbn : 0 ≤ ‖b‖ := norm_nonneg b
  have hkey : ‖b‖ • (NormedSpace.normalize a - NormedSpace.normalize b) =
      (‖b‖ - ‖a‖) • NormedSpace.normalize a + (a - b) := by
    have e2 : ‖b‖ • NormedSpace.normalize b = b := NormedSpace.norm_smul_normalize b
    have e3 : ‖a‖ • NormedSpace.normalize a = a := NormedSpace.norm_smul_normalize a
    calc ‖b‖ • (NormedSpace.normalize a - NormedSpace.normalize b)
        = ‖b‖ • NormedSpace.normalize a - ‖b‖ • NormedSpace.normalize b := smul_sub _ _ _
      _ = ‖b‖ • NormedSpace.normalize a - b := by rw [e2]
      _ = (‖b‖ - ‖a‖) • NormedSpace.normalize a +
            (‖a‖ • NormedSpace.normalize a - b) := by
          rw [sub_smul]; abel
      _ = (‖b‖ - ‖a‖) • NormedSpace.normalize a + (a - b) := by rw [e3]
  have hα : ‖NormedSpace.normalize a‖ ≤ 1 := by
    rcases eq_or_ne a 0 with ha | ha
    · rw [ha]; simp
    · rw [NormedSpace.norm_normalize ha]
  have h1 : ‖b‖ * ‖NormedSpace.normalize a - NormedSpace.normalize b‖
      = ‖(‖b‖ - ‖a‖) • NormedSpace.normalize a + (a - b)‖ := by
    rw [← hkey, norm_smul, Real.norm_eq_abs, abs_of_nonneg hbn]
  have h2 : ‖(‖b‖ - ‖a‖) • NormedSpace.normalize a + (a - b)‖
      ≤ |‖b‖ - ‖a‖| * 1 + ‖a - b‖ := by
    have h2a : ‖(‖b‖ - ‖a‖) • NormedSpace.normalize a + (a - b)‖
        ≤ ‖(‖b‖ - ‖a‖) • NormedSpace.normalize a‖ + ‖a - b‖ := norm_add_le _ _
    have h2b : ‖(‖b‖ - ‖a‖) • NormedSpace.normalize a‖
        = |‖b‖ - ‖a‖| * ‖NormedSpace.normalize a‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    have h2c : |‖b‖ - ‖a‖| * ‖NormedSpace.normalize a‖ ≤ |‖b‖ - ‖a‖| * 1 :=
      mul_le_mul_of_nonneg_left hα (abs_nonneg _)
    rw [h2b] at h2a
    linarith
  have h4 : |‖b‖ - ‖a‖| ≤ ‖a - b‖ := by
    rw [← norm_sub_rev]
    exact abs_norm_sub_norm_le b a
  have hd : ‖NormedSpace.normalize a - NormedSpace.normalize b‖ ≥ 0 := norm_nonneg _
  have h5 : ‖b‖ * ‖NormedSpace.normalize a - NormedSpace.normalize b‖ ≤ 2 * ‖a - b‖ := by
    rw [h1]
    have h6 : |‖b‖ - ‖a‖| * ‖NormedSpace.normalize a‖ ≤ ‖a - b‖ := by
      nlinarith [hα, h4, abs_nonneg (‖b‖ - ‖a‖), norm_nonneg a, norm_nonneg b]
    linarith
  nlinarith [h5, hc, hd, hbn, norm_nonneg (a - b)]

private theorem mnrs2_ofReal_eq (r : ℝ) : (RCLike.ofReal r : ℂ) = Complex.ofReal r := rfl

private theorem mnrs2_step_decomp
    (Mr Rs : Submodule ℂ W) (unmarkRefl : W ≃ₗᵢ[ℂ] W)
    (hMneg : ∀ z ∈ Mr, unmarkRefl z = -z)
    (hMid : ∀ z ∈ Mrᗮ, unmarkRefl z = z)
    (x₀ : W) (hx₀ : ‖x₀‖ = 1) (γ : ℝ) (hγ0 : 0 < γ)
    (R : ℕ → W ≃ₗᵢ[ℂ] W) (t : ℕ)
    (hclose : ∀ z ∈ Rs, markProj Mr z ∈ Rs)
    (hRRs : ∀ i, 1 ≤ i → i ≤ t → ∀ z ∈ Rs, R i z ∈ Rs)
    (hfix : ∀ i, 1 ≤ i → i ≤ t →
      R i (raaState unmarkRefl R x₀ (i - 1)) = raaState unmarkRefl R x₀ (i - 1))
    (hbound : ∀ i, 1 ≤ i → i ≤ t → ∀ ψ ∈ Rs,
      ψ ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ (i - 1)})ᗮ →
      ‖R i ψ + ψ - (2 : ℂ) • (lineProj (raaState unmarkRefl R x₀ (i - 1)) ψ)‖
        ≤ betaAt γ i * ‖ψ‖)
    (j : ℕ) (hjt : j + 1 ≤ t)
    (hφRs : raaState unmarkRefl R x₀ j ∈ Rs)
    (hϕ : Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ≤ π / 3) :
    ∃ ω : W,
      raaState unmarkRefl R x₀ (j + 1) =
        (Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) : ℂ) •
          (NormedSpace.normalize (markProj Mr (raaState unmarkRefl R x₀ j))) +
        (Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) : ℂ) •
          (NormedSpace.normalize (raaState unmarkRefl R x₀ j -
            markProj Mr (raaState unmarkRefl R x₀ j))) +
        ω ∧
      ‖ω‖ ≤ betaAt γ (j + 1) *
        |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)| ∧
      |‖markProj Mr (raaState unmarkRefl R x₀ (j + 1))‖ -
        Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)| ≤ ‖ω‖ := by
  let y := markProj Mr (raaState unmarkRefl R x₀ j)
  let z := raaState unmarkRefl R x₀ j - y
  let μ := NormedSpace.normalize y
  let ν := NormedSpace.normalize z
  let ϕ := Real.arcsin ‖y‖
  have hϕle : ϕ ≤ π / 3 := hϕ
  have hϕnn : 0 ≤ ϕ := Real.arcsin_nonneg.mpr (norm_nonneg y)
  have hφn : ‖raaState unmarkRefl R x₀ j‖ = 1 := by rw [mnrs_raa_state_norm, hx₀]
  have hyM : y ∈ Mr := (Mr.orthogonalProjection (raaState unmarkRefl R x₀ j)).property
  have hzM : z ∈ Mrᗮ := Submodule.sub_starProjection_mem_orthogonal _
  have hyRs : y ∈ Rs := hclose _ hφRs
  have hzRs : z ∈ Rs := Rs.sub_mem hφRs hyRs
  have hsy1 : ‖y‖ ≤ 1 := by
    have h := Submodule.norm_starProjection_apply_le Mr (raaState unmarkRefl R x₀ j)
    exact h.trans_eq hφn
  have hsinϕ : Real.sin ϕ = ‖y‖ := Real.sin_arcsin (by linarith [norm_nonneg y]) hsy1
  have hyz0 : inner ℂ y z = 0 := (Mr.mem_orthogonal z).mp hzM y hyM
  have hzy0 : inner ℂ z y = 0 := by rw [← inner_conj_symm, hyz0, map_zero]
  have hsplit : raaState unmarkRefl R x₀ j = y + z := (add_sub_cancel y _).symm
  have hnormsq : ‖y‖ ^ 2 + ‖z‖ ^ 2 = 1 := by
    have he : inner ℂ (raaState unmarkRefl R x₀ j) (raaState unmarkRefl R x₀ j) =
        inner ℂ y y + inner ℂ z z := by
      rw [hsplit, inner_add_add_self, hyz0, hzy0]
      ring
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K] at he
    have he' : ‖raaState unmarkRefl R x₀ j‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by exact_mod_cast he
    rw [hφn] at he'
    linarith [he']
  have hcosϕ : Real.cos ϕ = ‖z‖ := by
    have h1 : (1 : ℝ) - ‖y‖ ^ 2 = ‖z‖ ^ 2 := by linarith [hnormsq]
    show Real.cos (Real.arcsin ‖y‖) = ‖z‖
    rw [Real.cos_arcsin, h1, Real.sqrt_sq (norm_nonneg z)]
  have hμM : μ ∈ Mr := by
    simpa only [μ, NormedSpace.normalize, Complex.coe_smul] using
      Mr.smul_mem ((‖y‖⁻¹ : ℝ) : ℂ) hyM
  have hνM : ν ∈ Mrᗮ := by
    simpa only [ν, NormedSpace.normalize, Complex.coe_smul] using
      Mrᗮ.smul_mem ((‖z‖⁻¹ : ℝ) : ℂ) hzM
  have hμRs : μ ∈ Rs := by
    simpa only [μ, NormedSpace.normalize, Complex.coe_smul] using
      Rs.smul_mem ((‖y‖⁻¹ : ℝ) : ℂ) hyRs
  have hνRs : ν ∈ Rs := by
    simpa only [ν, NormedSpace.normalize, Complex.coe_smul] using
      Rs.smul_mem ((‖z‖⁻¹ : ℝ) : ℂ) hzRs
  have hμν : inner ℂ μ ν = 0 := (Mr.mem_orthogonal ν).mp hνM μ hμM
  have hνμ : inner ℂ ν μ = 0 := by rw [← inner_conj_symm, hμν, map_zero]
  have hμn : ‖μ‖ ≤ 1 := by
    rcases eq_or_ne y 0 with hy0 | hy0
    · have h0 : μ = 0 := by
        show NormedSpace.normalize y = 0
        rw [hy0]
        simp [NormedSpace.normalize]
      rw [h0, norm_zero]
      norm_num
    · rw [NormedSpace.norm_normalize hy0]
  have hνn : ‖ν‖ ≤ 1 := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · have h0 : ν = 0 := by
        show NormedSpace.normalize z = 0
        rw [hz0]
        simp [NormedSpace.normalize]
      rw [h0, norm_zero]
      norm_num
    · rw [NormedSpace.norm_normalize hz0]
  have hμ2 : Real.sin ϕ * ‖μ‖ ^ 2 = Real.sin ϕ := by
    rcases eq_or_ne y 0 with hy0 | hy0
    · have hs0 : Real.sin ϕ = 0 := by rw [hsinϕ, hy0, norm_zero]
      rw [hs0, zero_mul]
    · rw [NormedSpace.norm_normalize hy0]
      simp
  have hν2 : Real.cos ϕ * ‖ν‖ ^ 2 = Real.cos ϕ := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · have hc0 : Real.cos ϕ = 0 := by rw [hcosϕ, hz0, norm_zero]
      rw [hc0, zero_mul]
    · rw [NormedSpace.norm_normalize hz0]
      simp
  have hdecomp : raaState unmarkRefl R x₀ j = (Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν := by
    have hy' : (‖y‖ : ℂ) • μ = y := by
      rw [Complex.coe_smul]
      exact NormedSpace.norm_smul_normalize y
    have hz' : (‖z‖ : ℂ) • ν = z := by
      rw [Complex.coe_smul]
      exact NormedSpace.norm_smul_normalize z
    rw [hsinϕ, hcosϕ, hy', hz']
    exact hsplit
  have hUφ : unmarkRefl (raaState unmarkRefl R x₀ j) =
      -(Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν := by
    rw [hdecomp, map_add, map_smul, map_smul, hMneg μ hμM, hMid ν hνM, smul_neg, ← neg_smul]
  let φp := (Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν
  have hφpRs : φp ∈ Rs := Rs.sub_mem (Rs.smul_mem _ hμRs) (Rs.smul_mem _ hνRs)
  have hUdecomp : unmarkRefl (raaState unmarkRefl R x₀ j) =
      (Real.cos (2 * ϕ) : ℂ) • raaState unmarkRefl R x₀ j - (Real.sin (2 * ϕ) : ℂ) • φp := by
    have hc3 : Real.cos (2 * ϕ) * Real.sin ϕ - Real.sin (2 * ϕ) * Real.cos ϕ =
        -Real.sin ϕ := by
      have h1 : Real.sin (2 * ϕ - ϕ) = Real.sin ϕ := by congr 1; ring
      rw [Real.sin_sub] at h1
      linarith [h1]
    have hc4 : Real.cos (2 * ϕ) * Real.cos ϕ + Real.sin (2 * ϕ) * Real.sin ϕ =
        Real.cos ϕ := by
      have h1 : Real.cos (2 * ϕ - ϕ) = Real.cos ϕ := by congr 1; ring
      rwa [Real.cos_sub] at h1
    rw [hUφ, hdecomp]
    show -(Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν =
      (Real.cos (2 * ϕ) : ℂ) • ((Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν) -
        (Real.sin (2 * ϕ) : ℂ) • ((Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν)
    have hvec : (Real.cos (2 * ϕ) : ℂ) • ((Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν) -
        (Real.sin (2 * ϕ) : ℂ) • ((Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν) =
        ((Real.cos (2 * ϕ) * Real.sin ϕ - Real.sin (2 * ϕ) * Real.cos ϕ : ℝ) : ℂ) • μ +
          ((Real.cos (2 * ϕ) * Real.cos ϕ + Real.sin (2 * ϕ) * Real.sin ϕ : ℝ) : ℂ) • ν := by
      push_cast
      module
    rw [hvec, hc3, hc4, Complex.ofReal_neg, neg_smul]
  have hideal : (Real.cos (2 * ϕ) : ℂ) • raaState unmarkRefl R x₀ j +
        (Real.sin (2 * ϕ) : ℂ) • φp =
      (Real.sin (3 * ϕ) : ℂ) • μ + (Real.cos (3 * ϕ) : ℂ) • ν := by
    have hc1 : Real.cos (2 * ϕ) * Real.sin ϕ + Real.sin (2 * ϕ) * Real.cos ϕ =
        Real.sin (3 * ϕ) := by
      have h1 : Real.sin (2 * ϕ + ϕ) = Real.sin (3 * ϕ) := by congr 1; ring
      rw [Real.sin_add] at h1
      linarith [h1]
    have hc2 : Real.cos (2 * ϕ) * Real.cos ϕ - Real.sin (2 * ϕ) * Real.sin ϕ =
        Real.cos (3 * ϕ) := by
      have h1 : Real.cos (2 * ϕ + ϕ) = Real.cos (3 * ϕ) := by congr 1; ring
      rwa [Real.cos_add] at h1
    rw [hdecomp]
    show (Real.cos (2 * ϕ) : ℂ) • ((Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν) +
      (Real.sin (2 * ϕ) : ℂ) • ((Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν) =
      (Real.sin (3 * ϕ) : ℂ) • μ + (Real.cos (3 * ϕ) : ℂ) • ν
    have hvec : (Real.cos (2 * ϕ) : ℂ) • ((Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν) +
      (Real.sin (2 * ϕ) : ℂ) • ((Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν) =
        ((Real.cos (2 * ϕ) * Real.sin ϕ + Real.sin (2 * ϕ) * Real.cos ϕ : ℝ) : ℂ) • μ +
          ((Real.cos (2 * ϕ) * Real.cos ϕ - Real.sin (2 * ϕ) * Real.sin ϕ : ℝ) : ℂ) • ν := by
      push_cast
      module
    rw [hvec, hc1, hc2]
  have hφporth0 : φp ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ j})ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hcomp : inner ℂ φp (raaState unmarkRefl R x₀ j) =
        ((Real.cos ϕ * Real.sin ϕ * ‖μ‖ ^ 2 - Real.sin ϕ * Real.cos ϕ * ‖ν‖ ^ 2 : ℝ) : ℂ) := by
      rw [hdecomp]
      show inner ℂ ((Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν)
          ((Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν) = _
      simp only [inner_sub_left, inner_add_right, inner_smul_left, inner_smul_right,
        hμν, hνμ, inner_self_eq_norm_sq_to_K, Complex.conj_ofReal, mnrs2_ofReal_eq]
      push_cast
      ring
    rw [hcomp]
    have hzero : Real.cos ϕ * Real.sin ϕ * ‖μ‖ ^ 2 - Real.sin ϕ * Real.cos ϕ * ‖ν‖ ^ 2 = 0 := by
      linear_combination Real.cos ϕ * hμ2 - Real.sin ϕ * hν2
    exact_mod_cast hzero
  have hφpnorm : ‖φp‖ ≤ 1 := by
    have hcomp : inner ℂ φp φp =
        ((Real.cos ϕ ^ 2 * ‖μ‖ ^ 2 + Real.sin ϕ ^ 2 * ‖ν‖ ^ 2 : ℝ) : ℂ) := by
      show inner ℂ ((Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν)
          ((Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν) = _
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        hμν, hνμ, Complex.conj_ofReal, mul_zero, add_zero, zero_add, sub_zero, mnrs2_ofReal_eq]
      simp only [inner_self_eq_norm_sq_to_K, mnrs2_ofReal_eq]
      push_cast
      ring
    have hsq1 : ‖φp‖ ^ 2 = Real.cos ϕ ^ 2 * ‖μ‖ ^ 2 + Real.sin ϕ ^ 2 * ‖ν‖ ^ 2 := by
      have h1 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) φp
      rw [hcomp] at h1
      simp only [mnrs2_ofReal_eq] at h1
      have h2 : (↑‖φp‖ : ℂ) ^ 2 = ↑(‖φp‖ ^ 2) := by simp
      rw [h2] at h1
      exact (Complex.ofReal_inj.mp h1).symm
    have hsqle : ‖φp‖ ^ 2 ≤ 1 := by
      have hμ2' : ‖μ‖ ^ 2 ≤ 1 := by nlinarith [hμn, norm_nonneg μ]
      have hν2' : ‖ν‖ ^ 2 ≤ 1 := by nlinarith [hνn, norm_nonneg ν]
      have hc := Real.sin_sq_add_cos_sq ϕ
      nlinarith [hsq1, mul_le_mul_of_nonneg_left hμ2' (sq_nonneg (Real.cos ϕ)),
        mul_le_mul_of_nonneg_left hν2' (sq_nonneg (Real.sin ϕ)), hc]
    exact (sq_le_sq₀ (norm_nonneg φp) zero_le_one).mp (by simpa using hsqle)
  have hfixj : R (j + 1) (raaState unmarkRefl R x₀ j) = raaState unmarkRefl R x₀ j := by
    have h := hfix (j + 1) (Nat.le_add_left 1 j) hjt
    rwa [Nat.add_sub_cancel] at h
  have hboundj : ‖R (j + 1) φp + φp‖ ≤ betaAt γ (j + 1) * ‖φp‖ := by
    have hφporth : φp ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ (j + 1 - 1)})ᗮ := by
      rw [Nat.add_sub_cancel]
      exact hφporth0
    have h := hbound (j + 1) (Nat.le_add_left 1 j) hjt φp hφpRs hφporth
    rw [Nat.add_sub_cancel] at h
    have hlp : lineProj (raaState unmarkRefl R x₀ j) φp = 0 := by
      rw [mnrs_line_projection_eq]
      exact (Submodule.starProjection_apply_eq_zero_iff _).mpr hφporth0
    rw [hlp, smul_zero, sub_zero] at h
    exact h
  let ω := -(Real.sin (2 * ϕ) : ℂ) • (R (j + 1) φp + φp)
  have hωnorm : ‖ω‖ ≤ betaAt γ (j + 1) * |Real.sin (2 * ϕ)| := by
    have hβnn : 0 ≤ betaAt γ (j + 1) := by
      unfold betaAt
      positivity
    have h1 : ‖ω‖ = |Real.sin (2 * ϕ)| * ‖R (j + 1) φp + φp‖ := by
      show ‖-(Real.sin (2 * ϕ) : ℂ) • (R (j + 1) φp + φp)‖ =
          |Real.sin (2 * ϕ)| * ‖R (j + 1) φp + φp‖
      rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    rw [h1]
    calc |Real.sin (2 * ϕ)| * ‖R (j + 1) φp + φp‖
        ≤ |Real.sin (2 * ϕ)| * (betaAt γ (j + 1) * ‖φp‖) :=
          mul_le_mul_of_nonneg_left hboundj (abs_nonneg _)
      _ ≤ |Real.sin (2 * ϕ)| * (betaAt γ (j + 1) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hφpnorm hβnn) (abs_nonneg _)
      _ = betaAt γ (j + 1) * |Real.sin (2 * ϕ)| := by ring
  have hstate : raaState unmarkRefl R x₀ (j + 1) =
      (Real.sin (3 * ϕ) : ℂ) • μ + (Real.cos (3 * ϕ) : ℂ) • ν + ω := by
    have h1 : raaState unmarkRefl R x₀ (j + 1) =
        R (j + 1) (unmarkRefl (raaState unmarkRefl R x₀ j)) := rfl
    rw [h1, hUdecomp, map_sub, map_smul, map_smul, hfixj]
    show (Real.cos (2 * ϕ) : ℂ) • raaState unmarkRefl R x₀ j -
        (Real.sin (2 * ϕ) : ℂ) • R (j + 1) φp =
      (Real.sin (3 * ϕ) : ℂ) • μ + (Real.cos (3 * ϕ) : ℂ) • ν + ω
    have h2 : (Real.cos (2 * ϕ) : ℂ) • raaState unmarkRefl R x₀ j -
        (Real.sin (2 * ϕ) : ℂ) • R (j + 1) φp =
        (Real.cos (2 * ϕ) : ℂ) • raaState unmarkRefl R x₀ j + (Real.sin (2 * ϕ) : ℂ) • φp +
          ω := by
      show (Real.cos (2 * ϕ) : ℂ) • raaState unmarkRefl R x₀ j -
          (Real.sin (2 * ϕ) : ℂ) • R (j + 1) φp =
        (Real.cos (2 * ϕ) : ℂ) • raaState unmarkRefl R x₀ j + (Real.sin (2 * ϕ) : ℂ) • φp +
          (-(Real.sin (2 * ϕ) : ℂ) • (R (j + 1) φp + φp))
      module
    rw [h2, hideal]
  have hproj : markProj Mr (raaState unmarkRefl R x₀ (j + 1)) =
      (Real.sin (3 * ϕ) : ℂ) • μ + markProj Mr ω := by
    have hμfix : markProj Mr μ = μ := by
      rw [mnrs_mark_projection_eq]
      exact (Submodule.starProjection_eq_self_iff).mpr hμM
    have hν0 : markProj Mr ν = 0 := by
      rw [mnrs_mark_projection_eq]
      exact (Submodule.starProjection_apply_eq_zero_iff _).mpr hνM
    rw [hstate, map_add, map_add, map_smul, map_smul, hμfix, hν0, smul_zero, add_zero]
  have hs3nn : 0 ≤ Real.sin (3 * ϕ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hϕnn]
    · linarith [hϕle, Real.pi_pos]
  have hμ3 : Real.sin (3 * ϕ) * ‖μ‖ = Real.sin (3 * ϕ) := by
    rcases eq_or_ne y 0 with hy0 | hy0
    · have hs0 : Real.sin ϕ = 0 := by rw [hsinϕ, hy0, norm_zero]
      have h3 : Real.sin (3 * ϕ) = 0 := by
        rw [Real.sin_three_mul, hs0]
        simp
      rw [h3, zero_mul]
    · rw [NormedSpace.norm_normalize hy0, mul_one]
  have hmain : |‖markProj Mr (raaState unmarkRefl R x₀ (j + 1))‖ - Real.sin (3 * ϕ)| ≤
      ‖ω‖ := by
    have h1 : ‖(Real.sin (3 * ϕ) : ℂ) • μ‖ = Real.sin (3 * ϕ) * ‖μ‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs3nn]
    have h2 := abs_norm_sub_norm_le ((Real.sin (3 * ϕ) : ℂ) • μ + markProj Mr ω)
      ((Real.sin (3 * ϕ) : ℂ) • μ)
    rw [h1, add_sub_cancel_left] at h2
    rw [hproj]
    calc |‖(Real.sin (3 * ϕ) : ℂ) • μ + markProj Mr ω‖ - Real.sin (3 * ϕ)|
        = |‖(Real.sin (3 * ϕ) : ℂ) • μ + markProj Mr ω‖ - Real.sin (3 * ϕ) * ‖μ‖| := by
          rw [hμ3]
      _ ≤ ‖markProj Mr ω‖ := h2
      _ ≤ ‖ω‖ := Submodule.norm_starProjection_apply_le Mr ω
  exact ⟨ω, hstate, hωnorm, hmain⟩

private theorem mnrs2_env
    (Mr Rs : Submodule ℂ W) (unmarkRefl : W ≃ₗᵢ[ℂ] W)
    (hMneg : ∀ z ∈ Mr, unmarkRefl z = -z)
    (hMid : ∀ z ∈ Mrᗮ, unmarkRefl z = z)
    (x₀ : W) (hx₀ : ‖x₀‖ = 1) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (t : ℕ) (ht1 : 1 ≤ t) (R : ℕ → W ≃ₗᵢ[ℂ] W)
    (hxRs : x₀ ∈ Rs)
    (hclose : ∀ z ∈ Rs, markProj Mr z ∈ Rs)
    (hRRs : ∀ i, 1 ≤ i → i ≤ t → ∀ z ∈ Rs, R i z ∈ Rs)
    (hfix : ∀ i, 1 ≤ i → i ≤ t →
      R i (raaState unmarkRefl R x₀ (i - 1)) = raaState unmarkRefl R x₀ (i - 1))
    (hbound : ∀ i, 1 ≤ i → i ≤ t → ∀ ψ ∈ Rs,
      ψ ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ (i - 1)})ᗮ →
      ‖R i ψ + ψ - (2 : ℂ) • (lineProj (raaState unmarkRefl R x₀ (i - 1)) ψ)‖
        ≤ betaAt γ i * ‖ψ‖)
    (hwin : (3 : ℝ) ^ t * Real.arcsin ‖markProj Mr x₀‖ ∈ Set.Icc (π / 4) (3 * π / 4)) :
    ∀ j, j + 1 ≤ t →
      raaState unmarkRefl R x₀ j ∈ Rs ∧
      |‖markProj Mr (raaState unmarkRefl R x₀ j)‖ -
        Real.sin ((3 : ℝ) ^ j * Real.arcsin ‖markProj Mr x₀‖)| ≤
        γ * ((3 : ℝ) ^ j * Real.arcsin ‖markProj Mr x₀‖) * (1 / 8) *
          ∑ l ∈ Finset.Icc 1 j, (1 : ℝ) / (l : ℝ) ^ 2 := by
  have h0 : raaState unmarkRefl R x₀ 0 = x₀ := by simp [raaState, raaUnitary]
  have hs0nn : 0 ≤ ‖markProj Mr x₀‖ := norm_nonneg _
  have hs0le : ‖markProj Mr x₀‖ ≤ 1 := by
    have h := Submodule.norm_starProjection_apply_le Mr x₀
    exact h.trans_eq hx₀
  have hπ : Real.pi ≤ 63 / 20 := by
    rw [show (63 : ℝ) / 20 = 3.15 from by norm_num]
    exact Real.pi_lt_d2.le
  have hK : (18 : ℝ) / (4 * Real.pi ^ 3) ≤ 3 / 20 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi ^ 3)]
    have hπ3 : (30 : ℝ) ≤ Real.pi ^ 3 := by
      have h1 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3.14) Real.pi_gt_d2.le 3
      nlinarith [h1]
    nlinarith [hπ3]
  have hKnn : (0 : ℝ) ≤ 18 / (4 * Real.pi ^ 3) := by positivity
  have hβ : ∀ i : ℕ, betaAt γ i = (18 / (4 * Real.pi ^ 3)) * γ * ((i : ℝ) ^ 2)⁻¹ := by
    intro i
    unfold betaAt
    rw [div_eq_mul_inv]
  set A0 := Real.arcsin ‖markProj Mr x₀‖ with hA0def
  set σ : ℕ → ℝ := fun n => ∑ l ∈ Finset.Icc 1 n, (1 : ℝ) / (l : ℝ) ^ 2 with hσdef
  set e : ℕ → ℝ := fun i =>
    |‖markProj Mr (raaState unmarkRefl R x₀ i)‖ - Real.sin ((3 : ℝ) ^ i * A0)| with hedef
  have hσeq : ∀ n, σ n = ∑ l ∈ Finset.Icc 1 n, (1 : ℝ) / (l : ℝ) ^ 2 := fun n => by rw [hσdef]
  have heeq : ∀ i, e i =
      |‖markProj Mr (raaState unmarkRefl R x₀ i)‖ - Real.sin ((3 : ℝ) ^ i * A0)| :=
    fun i => by rw [hedef]
  have hwin'' : (3 : ℝ) ^ t * A0 ∈ Set.Icc (π / 4) (3 * π / 4) := by
    rw [hA0def]
    exact hwin
  have hA0nn : 0 ≤ A0 := by
    rw [hA0def]
    exact Real.arcsin_nonneg.mpr hs0nn
  have hσ0 : σ 0 = 0 := by
    rw [hσeq]
    simp
  have hσsucc : ∀ n, σ (n + 1) = σ n + 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    rw [hσeq (n + 1), hσeq n, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one]
  have hσle : ∀ n, σ n ≤ 2 := fun n => by
    rw [hσeq n]
    exact mnrs_sum_inv_sq_le_two n
  have hσnn : ∀ n, 0 ≤ σ n := fun n => by
    rw [hσeq n]
    exact Finset.sum_nonneg (fun l _ => by positivity)
  have hbarnn : ∀ i, 0 ≤ (3 : ℝ) ^ i * A0 :=
    fun i => mul_nonneg (pow_nonneg (by norm_num) _) hA0nn
  have hbarmono : ∀ {a b : ℕ}, a ≤ b → (3 : ℝ) ^ a * A0 ≤ (3 : ℝ) ^ b * A0 :=
    fun hab => mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hab) hA0nn
  have hbarsucc : ∀ i, (3 : ℝ) ^ (i + 1) * A0 = 3 * ((3 : ℝ) ^ i * A0) := by
    intro i
    rw [pow_succ]
    ring
  have ht11 : t - 1 + 1 = t := by omega
  have hbarteq : (3 : ℝ) ^ t * A0 = 3 * ((3 : ℝ) ^ (t - 1) * A0) := by
    have h := hbarsucc (t - 1)
    rwa [ht11] at h
  have hbart1le : (3 : ℝ) ^ (t - 1) * A0 ≤ π / 4 := by
    have h := hwin''.2
    linarith [hbarteq, h, Real.pi_pos]
  have he0 : e 0 = 0 := by
    rw [heeq 0, h0, pow_zero, one_mul, hA0def,
      Real.sin_arcsin (by linarith [hs0nn]) hs0le, sub_self, abs_zero]
  have hP : ∀ j, j + 1 ≤ t →
      (raaState unmarkRefl R x₀ j ∈ Rs) ∧
      e j ≤ γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * σ j := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨by rw [h0]; exact hxRs, ?_⟩
      rw [he0, hσ0]
      simp
    | succ j ih =>
      intro hj
      obtain ⟨hRsj, hej⟩ := ih (by omega)
      have hbarjle : (3 : ℝ) ^ j * A0 ≤ π / 12 := by
        have h1 := hbarmono (show j + 1 ≤ t - 1 by omega)
        rw [hbarsucc j] at h1
        linarith [hbart1le, Real.pi_pos]
      have hŝnn : 0 ≤ Real.sin ((3 : ℝ) ^ j * A0) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (hbarnn j)
          (by linarith [hbarjle, Real.pi_pos])
      have hŝ : Real.sin ((3 : ℝ) ^ j * A0) ≤ 21 / 80 := by
        have h1 := Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [hbarnn j, Real.pi_pos] : -(π / 2) ≤ (3 : ℝ) ^ j * A0)
          (by linarith [Real.pi_pos] : π / 12 ≤ π / 2) hbarjle
        have h2 := Real.sin_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 12)
        linarith [h1, h2, hπ]
      have hejnn : 0 ≤ e j := abs_nonneg _
      have hsjnn : 0 ≤ ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ := norm_nonneg _
      have hsjle : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ≤ 1 := by
        have h := Submodule.norm_starProjection_apply_le Mr (raaState unmarkRefl R x₀ j)
        have hn : ‖raaState unmarkRefl R x₀ j‖ = 1 := by rw [mnrs_raa_state_norm, hx₀]
        exact h.trans_eq hn
      have hsinϕj : Real.sin (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) =
          ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ :=
        Real.sin_arcsin (by linarith [hsjnn]) hsjle
      have hsje : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ≤
          Real.sin ((3 : ℝ) ^ j * A0) + e j := by
        have h : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ - Real.sin ((3 : ℝ) ^ j * A0) ≤
              e j := le_abs_self _
        linarith [h]
      have hej2 : e j ≤ γ * ((3 : ℝ) ^ j * A0) / 4 := by
        calc e j ≤ γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * σ j := hej
          _ ≤ γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * 2 :=
              mul_le_mul_of_nonneg_left (hσle j)
                (mul_nonneg (mul_nonneg hγ0.le (hbarnn j)) (by norm_num))
          _ = γ * ((3 : ℝ) ^ j * A0) / 4 := by ring
      have hej3 : e j ≤ 21 / 320 := by
        have h1 : γ * ((3 : ℝ) ^ j * A0) ≤ 1 * (π / 12) :=
          mul_le_mul hγ1 hbarjle (hbarnn j) zero_le_one
        have h2 : (1 : ℝ) * (π / 12) / 4 ≤ 21 / 320 := by linarith [hπ]
        calc e j ≤ γ * ((3 : ℝ) ^ j * A0) / 4 := hej2
          _ ≤ 1 * (π / 12) / 4 := by gcongr
          _ ≤ 21 / 320 := h2
      have hsj : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ≤ 21 / 64 := by
        linarith [hsje, hŝ, hej3]
      have hsjsq : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 ≤ 3 / 4 := by
        have h1 : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 ≤ (21 / 64 : ℝ) ^ 2 :=
            (sq_le_sq₀ hsjnn (by norm_num)).mpr hsj
        nlinarith [h1]
      have hϕjle : Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ≤ π / 3 :=
        mnrs_arcsin_le_pi_div_three hsjnn hsjsq
      have hTj : |3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 +
          ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ * Real.sin ((3 : ℝ) ^ j * A0) +
          Real.sin ((3 : ℝ) ^ j * A0) ^ 2)| ≤ 3 := by
        have hTnn : 0 ≤ ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 +
            ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ * Real.sin ((3 : ℝ) ^ j * A0) +
            Real.sin ((3 : ℝ) ^ j * A0) ^ 2 :=
          add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hsjnn hŝnn)) (sq_nonneg _)
        have hTle : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 +
            ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ * Real.sin ((3 : ℝ) ^ j * A0) +
            Real.sin ((3 : ℝ) ^ j * A0) ^ 2 ≤ 3 / 2 := by
          have h1 : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 ≤ (21 / 64 : ℝ) ^ 2 :=
              (sq_le_sq₀ hsjnn (by norm_num)).mpr hsj
          have h2 : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ *
              Real.sin ((3 : ℝ) ^ j * A0) ≤ (21 / 64 : ℝ) * (21 / 80) :=
              mul_le_mul hsj hŝ hŝnn (by norm_num : (0 : ℝ) ≤ 21 / 64)
          have h3 : Real.sin ((3 : ℝ) ^ j * A0) ^ 2 ≤ (21 / 80 : ℝ) ^ 2 :=
              (sq_le_sq₀ hŝnn (by norm_num)).mpr hŝ
          nlinarith [h1, h2, h3]
        rw [abs_le]
        constructor <;> linarith [hTnn, hTle]
      obtain ⟨hstep, hRsj1⟩ := mnrs_raa_step Mr Rs unmarkRefl hMneg hMid x₀ hx₀ γ hγ0 R t
        hclose hRRs hfix hbound j (by omega) hRsj hϕjle
      have h2ϕnn : 0 ≤ Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · have h1 := Real.arcsin_nonneg.mpr hsjnn
          linarith [h1]
        · linarith [hϕjle, Real.pi_pos]
      have hsin2 : |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)| ≤
          2 * (((3 : ℝ) ^ j * A0) + e j) := by
        rw [abs_of_nonneg h2ϕnn, Real.sin_two_mul]
        have hc1 := Real.cos_le_one (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)
        have hsc : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ *
            Real.cos (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) ≤
            ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ := by
          have h := mul_le_mul_of_nonneg_left hc1 hsjnn
          simpa using h
        have hsgbar : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ≤
            (3 : ℝ) ^ j * A0 + e j := by
          have h1 := Real.sin_le (hbarnn j)
          linarith [hsje, h1]
        rw [hsinϕj]
        linarith [hsc, hsgbar, hsjnn]
      have hrec : e (j + 1) ≤
          2 * betaAt γ (j + 1) * (((3 : ℝ) ^ j * A0) + e j) + 3 * e j := by
        have hsplit : e (j + 1) ≤ |‖markProj Mr (raaState unmarkRefl R x₀ (j + 1))‖ -
            Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)| +
            |Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) -
              Real.sin ((3 : ℝ) ^ (j + 1) * A0)| := by
          rw [heeq (j + 1)]
          have h2 : ‖markProj Mr (raaState unmarkRefl R x₀ (j + 1))‖ -
              Real.sin ((3 : ℝ) ^ (j + 1) * A0) =
              (‖markProj Mr (raaState unmarkRefl R x₀ (j + 1))‖ -
                Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)) +
              (Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) -
                Real.sin ((3 : ℝ) ^ (j + 1) * A0)) := by ring
          rw [h2]
          exact abs_add_le _ _
        have hfac : |Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) -
            Real.sin ((3 : ℝ) ^ (j + 1) * A0)| =
            e j * |3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 +
              ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ * Real.sin ((3 : ℝ) ^ j * A0) +
              Real.sin ((3 : ℝ) ^ j * A0) ^ 2)| := by
          rw [hbarsucc j]
          have h := mnrs_sin_three_sub
            (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) ((3 : ℝ) ^ j * A0)
          rw [hsinϕj] at h
          rw [h, abs_mul, heeq j]
        calc e (j + 1) ≤ _ := hsplit
          _ = |‖markProj Mr (raaState unmarkRefl R x₀ (j + 1))‖ -
                Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)| +
              e j * |3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 +
                ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ * Real.sin ((3 : ℝ) ^ j * A0) +
                Real.sin ((3 : ℝ) ^ j * A0) ^ 2)| := by rw [hfac]
          _ ≤ betaAt γ (j + 1) *
                |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)| +
              e j * 3 := add_le_add hstep (mul_le_mul_of_nonneg_left hTj hejnn)
          _ ≤ 2 * betaAt γ (j + 1) * (((3 : ℝ) ^ j * A0) + e j) + 3 * e j := by
              have hβnn : 0 ≤ betaAt γ (j + 1) := by
                rw [hβ (j + 1)]
                exact mul_nonneg (mul_nonneg hKnn hγ0.le) (inv_nonneg.mpr (sq_nonneg _))
              have h1 := mul_le_mul_of_nonneg_left hsin2 hβnn
              nlinarith [h1]
      have hkey : 2 * (18 / (4 * Real.pi ^ 3)) +
          (18 / (4 * Real.pi ^ 3)) * γ * σ j / 4 ≤ 3 / 8 := by
        have hKγ : (18 / (4 * Real.pi ^ 3)) * γ ≤ 18 / (4 * Real.pi ^ 3) := by
          calc (18 / (4 * Real.pi ^ 3)) * γ ≤ (18 / (4 * Real.pi ^ 3)) * 1 :=
                mul_le_mul_of_nonneg_left hγ1 hKnn
            _ = 18 / (4 * Real.pi ^ 3) := mul_one _
        have hKγσ : (18 / (4 * Real.pi ^ 3)) * γ * σ j ≤ (18 / (4 * Real.pi ^ 3)) * 2 := by
          calc (18 / (4 * Real.pi ^ 3)) * γ * σ j ≤ (18 / (4 * Real.pi ^ 3)) * σ j :=
                mul_le_mul_of_nonneg_right hKγ (hσnn j)
            _ ≤ (18 / (4 * Real.pi ^ 3)) * 2 :=
                mul_le_mul_of_nonneg_left (hσle j) hKnn
        linarith [hK, hKγσ]
      have hβj1 : betaAt γ (j + 1) =
          (18 / (4 * Real.pi ^ 3)) * γ * (((j : ℝ) + 1) ^ 2)⁻¹ := by
        rw [hβ (j + 1)]
        simp only [Nat.cast_add, Nat.cast_one]
      have hest : 2 * betaAt γ (j + 1) * (((3 : ℝ) ^ j * A0) + e j) + 3 * e j ≤
          γ * ((3 : ℝ) ^ (j + 1) * A0) * (1 / 8) * σ (j + 1) := by
        rw [hβj1, hbarsucc j, hσsucc j, one_div]
        have hq : (0 : ℝ) < ((j : ℝ) + 1) ^ 2 := by positivity
        have hstep1 : 2 * ((18 / (4 * Real.pi ^ 3)) * γ * (((j : ℝ) + 1) ^ 2)⁻¹) *
              (((3 : ℝ) ^ j * A0) + e j) + 3 * e j ≤
              2 * ((18 / (4 * Real.pi ^ 3)) * γ * (((j : ℝ) + 1) ^ 2)⁻¹) *
              (((3 : ℝ) ^ j * A0) + γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * σ j) +
              3 * (γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * σ j) := by
          have hXnn : (0 : ℝ) ≤
              2 * ((18 / (4 * Real.pi ^ 3)) * γ * (((j : ℝ) + 1) ^ 2)⁻¹) :=
              mul_nonneg (by norm_num)
                (mul_nonneg (mul_nonneg hKnn hγ0.le) (inv_nonneg.mpr (sq_nonneg _)))
          have hXR : (3 : ℝ) ^ j * A0 + e j ≤
              (3 : ℝ) ^ j * A0 + γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * σ j := by
              linarith only [hej]
          exact add_le_add
            (mul_le_mul_of_nonneg_left hXR hXnn)
            (mul_le_mul_of_nonneg_left hej (by norm_num : (0 : ℝ) ≤ 3))
        have hstep2 : 2 * ((18 / (4 * Real.pi ^ 3)) * γ * (((j : ℝ) + 1) ^ 2)⁻¹) *
              (((3 : ℝ) ^ j * A0) + γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * σ j) +
              3 * (γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * σ j) =
              γ * ((3 : ℝ) ^ j * A0) * ((2 * (18 / (4 * Real.pi ^ 3)) +
                (18 / (4 * Real.pi ^ 3)) * γ * σ j / 4) * (((j : ℝ) + 1) ^ 2)⁻¹ +
                (3 / 8) * σ j) := by
            ring
        have hstep3 : γ * ((3 : ℝ) ^ j * A0) * ((2 * (18 / (4 * Real.pi ^ 3)) +
              (18 / (4 * Real.pi ^ 3)) * γ * σ j / 4) * (((j : ℝ) + 1) ^ 2)⁻¹ +
              (3 / 8) * σ j) ≤
              γ * ((3 : ℝ) ^ j * A0) * ((3 / 8) * (((j : ℝ) + 1) ^ 2)⁻¹ + (3 / 8) * σ j) := by
          have hmulinv := mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr hq.le)
          have hinner : (2 * (18 / (4 * Real.pi ^ 3)) +
              (18 / (4 * Real.pi ^ 3)) * γ * σ j / 4) * (((j : ℝ) + 1) ^ 2)⁻¹ +
              (3 / 8) * σ j ≤
              (3 / 8) * (((j : ℝ) + 1) ^ 2)⁻¹ + (3 / 8) * σ j := by
              linarith only [hmulinv]
          exact mul_le_mul_of_nonneg_left hinner (mul_nonneg hγ0.le (hbarnn j))
        have hstep4 : γ * ((3 : ℝ) ^ j * A0) *
              ((3 / 8) * (((j : ℝ) + 1) ^ 2)⁻¹ + (3 / 8) * σ j) =
              γ * (3 * ((3 : ℝ) ^ j * A0)) * (1 / 8) * (σ j + (((j : ℝ) + 1) ^ 2)⁻¹) := by
            ring
        calc 2 * ((18 / (4 * Real.pi ^ 3)) * γ * (((j : ℝ) + 1) ^ 2)⁻¹) *
              (((3 : ℝ) ^ j * A0) + e j) + 3 * e j ≤ _ := hstep1
          _ = _ := hstep2
          _ ≤ _ := hstep3
          _ = γ * (3 * ((3 : ℝ) ^ j * A0)) * (1 / 8) * (σ j + (((j : ℝ) + 1) ^ 2)⁻¹) :=
              hstep4
          _ = γ * (3 * ((3 : ℝ) ^ j * A0)) * 8⁻¹ * (σ j + 1 / ((j : ℝ) + 1) ^ 2) := by
              ring
      exact ⟨hRsj1, hrec.trans hest⟩
  intro j hj
  exact hP j hj

private theorem mnrs2_delta_chain
    (Mr Rs : Submodule ℂ W) (unmarkRefl : W ≃ₗᵢ[ℂ] W)
    (hMneg : ∀ z ∈ Mr, unmarkRefl z = -z)
    (hMid : ∀ z ∈ Mrᗮ, unmarkRefl z = z)
    (x₀ : W) (hx₀ : ‖x₀‖ = 1) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 40)
    (t : ℕ) (ht1 : 1 ≤ t) (R : ℕ → W ≃ₗᵢ[ℂ] W)
    (hxRs : x₀ ∈ Rs)
    (hclose : ∀ z ∈ Rs, markProj Mr z ∈ Rs)
    (hRRs : ∀ i, 1 ≤ i → i ≤ t → ∀ z ∈ Rs, R i z ∈ Rs)
    (hfix : ∀ i, 1 ≤ i → i ≤ t →
      R i (raaState unmarkRefl R x₀ (i - 1)) = raaState unmarkRefl R x₀ (i - 1))
    (hbound : ∀ i, 1 ≤ i → i ≤ t → ∀ ψ ∈ Rs,
      ψ ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ (i - 1)})ᗮ →
      ‖R i ψ + ψ - (2 : ℂ) • (lineProj (raaState unmarkRefl R x₀ (i - 1)) ψ)‖
        ≤ betaAt γ i * ‖ψ‖)
    (hwin : (3 : ℝ) ^ t * Real.arcsin ‖markProj Mr x₀‖ ∈ Set.Icc (π / 4) (3 * π / 4)) :
    ‖attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1) - x₀‖ ≤ π / 8 + (3 / 2) * γ := by
  have henv := mnrs2_env Mr Rs unmarkRefl hMneg hMid x₀ hx₀ γ hγ0
    (hγ1.trans (by norm_num)) t ht1 R hxRs hclose hRRs hfix hbound hwin
  have h0 : raaState unmarkRefl R x₀ 0 = x₀ := by simp [raaState, raaUnitary]
  have hs0nn : 0 ≤ ‖markProj Mr x₀‖ := norm_nonneg _
  have hs0le : ‖markProj Mr x₀‖ ≤ 1 := by
    have h := Submodule.norm_starProjection_apply_le Mr x₀
    exact h.trans_eq hx₀
  have hπ : Real.pi ≤ 63 / 20 := by
    rw [show (63 : ℝ) / 20 = 3.15 from by norm_num]
    exact Real.pi_lt_d2.le
  have hπge : (3.14 : ℝ) ≤ Real.pi := Real.pi_gt_d2.le
  have hA0nn : 0 ≤ Real.arcsin ‖markProj Mr x₀‖ := Real.arcsin_nonneg.mpr hs0nn
  have hπ2A0 : Real.arcsin ‖markProj Mr x₀‖ ≤ π / 2 := (Real.arcsin_mem_Icc _).2
  have hbarnn : ∀ i, 0 ≤ (3 : ℝ) ^ i * Real.arcsin ‖markProj Mr x₀‖ :=
    fun i => mul_nonneg (pow_nonneg (by norm_num) _) hA0nn
  have hbarmono : ∀ {a b : ℕ}, a ≤ b → (3 : ℝ) ^ a * Real.arcsin ‖markProj Mr x₀‖ ≤
      (3 : ℝ) ^ b * Real.arcsin ‖markProj Mr x₀‖ :=
    fun hab => mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hab) hA0nn
  have hbarsucc : ∀ i, (3 : ℝ) ^ (i + 1) * Real.arcsin ‖markProj Mr x₀‖ =
      3 * ((3 : ℝ) ^ i * Real.arcsin ‖markProj Mr x₀‖) := by
    intro i
    rw [pow_succ]
    ring
  have ht11 : t - 1 + 1 = t := by omega
  have hbarteq : (3 : ℝ) ^ t * Real.arcsin ‖markProj Mr x₀‖ =
      3 * ((3 : ℝ) ^ (t - 1) * Real.arcsin ‖markProj Mr x₀‖) := by
    have h := hbarsucc (t - 1)
    rwa [ht11] at h
  have hbart1le : (3 : ℝ) ^ (t - 1) * Real.arcsin ‖markProj Mr x₀‖ ≤ π / 4 := by
    have h := hwin.2
    linarith [hbarteq, h, Real.pi_pos]
  have hφAx : ∀ i, raaState unmarkRefl R x₀ i = raaUnitary unmarkRefl R i x₀ := fun i => rfl

  have hznorm : ∀ j, ‖raaState unmarkRefl R x₀ j - markProj Mr (raaState unmarkRefl R x₀ j)‖ =
      Real.cos (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) := by
    intro j
    set y : W := markProj Mr (raaState unmarkRefl R x₀ j) with hydef
    set z : W := raaState unmarkRefl R x₀ j - y with hzdef2
    have hyM : y ∈ Mr := by rw [hydef]; exact (Mr.orthogonalProjection _).property
    have hzM : z ∈ Mrᗮ := by
      rw [hzdef2, hydef, mnrs_mark_projection_eq]
      exact Submodule.sub_starProjection_mem_orthogonal _
    have hyz : inner ℂ y z = 0 := (Mr.mem_orthogonal _).mp hzM _ hyM
    have hzy : inner ℂ z y = 0 := by rw [← inner_conj_symm, hyz, map_zero]
    have hsplit : raaState unmarkRefl R x₀ j = y + z := by rw [hzdef2]; abel
    have hn : ‖raaState unmarkRefl R x₀ j‖ = 1 := by rw [mnrs_raa_state_norm, hx₀]
    have hsq : ‖y‖ ^ 2 + ‖z‖ ^ 2 = 1 := by
      have he : inner ℂ (raaState unmarkRefl R x₀ j) (raaState unmarkRefl R x₀ j) =
          inner ℂ y y + inner ℂ z z := by
        rw [hsplit, inner_add_add_self, hyz, hzy]
        ring
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
        inner_self_eq_norm_sq_to_K] at he
      have he' : ‖raaState unmarkRefl R x₀ j‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
        exact_mod_cast he
      rw [hn] at he'
      linarith [he']
    have h1 : (1 : ℝ) - ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [← hydef]
      linarith [hsq]
    rw [hzdef2, Real.cos_arcsin, h1, Real.sqrt_sq (norm_nonneg z)]

  have hsmall : ∀ j, j ≤ t - 1 → ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ≤ 18 / 25 := by
    intro j hj
    obtain ⟨-, hej⟩ := henv j (by omega)
    have hbarjle : (3 : ℝ) ^ j * Real.arcsin ‖markProj Mr x₀‖ ≤ π/4 := (hbarmono hj).trans hbart1le
    have hsinbar : Real.sin ((3 : ℝ) ^ j * Real.arcsin ‖markProj Mr x₀‖) ≤ 99 / 140 := by
      have h2 : Real.sin ((3 : ℝ) ^ j * Real.arcsin ‖markProj Mr x₀‖) ≤ 1 / Real.sqrt 2 := by
        have h3 := Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [Real.pi_pos, hbarnn j] :
            -(π / 2) ≤ (3 : ℝ) ^ j * Real.arcsin ‖markProj Mr x₀‖)
          (by linarith [Real.pi_pos] : π / 4 ≤ π / 2) hbarjle
        rwa [Real.sin_pi_div_four, mnrs2_sqrt_two_div_two] at h3
      exact h2.trans mnrs2_one_div_sqrt_two_le
    have hσ2 : (∑ l ∈ Finset.Icc 1 j, (1 : ℝ) / (l : ℝ) ^ 2) ≤ 2 := mnrs_sum_inv_sq_le_two j
    have hγX : γ * ((3 : ℝ) ^ j * Real.arcsin ‖markProj Mr x₀‖) * (1 / 8) ≤
        γ * (π / 4) * (1 / 8) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbarjle hγ0.le) (by norm_num)
    have hX : γ * ((3 : ℝ) ^ j * Real.arcsin ‖markProj Mr x₀‖) * (1 / 8) *
        (∑ l ∈ Finset.Icc 1 j, (1 : ℝ) / (l : ℝ) ^ 2) ≤ 63 / 12800 := by
      have hX2 : γ * ((3 : ℝ) ^ j * Real.arcsin ‖markProj Mr x₀‖) * (1 / 8) *
          (∑ l ∈ Finset.Icc 1 j, (1 : ℝ) / (l : ℝ) ^ 2) ≤
          γ * ((3 : ℝ) ^ j * Real.arcsin ‖markProj Mr x₀‖) * (1 / 8) * 2 :=
        mul_le_mul_of_nonneg_left hσ2
          (mul_nonneg (mul_nonneg hγ0.le (hbarnn j)) (by norm_num))
      have hX3 : γ * ((3 : ℝ) ^ j * Real.arcsin ‖markProj Mr x₀‖) * (1 / 8) * 2 ≤
          γ * (π / 4) * (1 / 8) * 2 :=
        mul_le_mul_of_nonneg_right hγX (by norm_num : (0 : ℝ) ≤ 2)
      have h3 : γ * (π / 4) * (1 / 8) * 2 ≤ 63 / 12800 := by nlinarith [hγ1, hπ]
      linarith
    have hle : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ≤
        Real.sin ((3 : ℝ) ^ j * Real.arcsin ‖markProj Mr x₀‖) +
        |‖markProj Mr (raaState unmarkRefl R x₀ j)‖ -
          Real.sin ((3 : ℝ) ^ j * Real.arcsin ‖markProj Mr x₀‖)| := by
      have h := le_abs_self (‖markProj Mr (raaState unmarkRefl R x₀ j)‖ -
        Real.sin ((3 : ℝ) ^ j * Real.arcsin ‖markProj Mr x₀‖))
      linarith
    have hfin : (99 / 140 : ℝ) + 63 / 12800 ≤ 18 / 25 := by norm_num
    linarith [hle, hej.trans hX, hsinbar, hfin]
  have hcosge : ∀ j, j ≤ t - 1 → 2 / 3 ≤
      ‖raaState unmarkRefl R x₀ j - markProj Mr (raaState unmarkRefl R x₀ j)‖ := by
    intro j hj
    have hsj := hsmall j hj
    have hsnn : 0 ≤ ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ := norm_nonneg _
    have h1 : (2 / 3 : ℝ) ^ 2 ≤ 1 - ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 := by
      nlinarith [hsj, hsnn]
    have h2 : (2 / 3 : ℝ) ^ 2 ≤
        (Real.sqrt (1 - ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt (by nlinarith [hsj, hsnn] : (0 : ℝ) ≤
        1 - ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2)]
      exact h1
    have h3 : 2 / 3 ≤ Real.sqrt (1 - ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2) :=
      (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp h2
    rw [hznorm j, Real.cos_arcsin]
    exact h3

  have hc0 : ‖NormedSpace.normalize (x₀ - markProj Mr x₀) - x₀‖ ≤
      Real.arcsin ‖markProj Mr x₀‖ := by
    rcases eq_or_ne (x₀ - markProj Mr x₀) 0 with hz0 | hz0
    · have hx0 : x₀ = markProj Mr x₀ := sub_eq_zero.mp hz0
      have hs0 : ‖markProj Mr x₀‖ = 1 := by rw [← hx0, hx₀]
      have hν0 : NormedSpace.normalize (x₀ - markProj Mr x₀) = 0 := by
        rw [hz0]; exact NormedSpace.normalize_zero_eq_zero
      rw [hν0, zero_sub, norm_neg, hx₀, hs0, Real.arcsin_one]
      linarith [hπge]
    · set y0 : W := markProj Mr x₀ with hy0def
      set z0 : W := x₀ - y0 with hz0def
      have hyM : y0 ∈ Mr := by rw [hy0def]; exact (Mr.orthogonalProjection x₀).property
      have hz0M : z0 ∈ Mrᗮ := by
        rw [hz0def, hy0def, mnrs_mark_projection_eq]
        exact Submodule.sub_starProjection_mem_orthogonal x₀
      have hyz : inner ℂ y0 z0 = 0 := (Mr.mem_orthogonal _).mp hz0M _ hyM
      have hzy : inner ℂ z0 y0 = 0 := by rw [← inner_conj_symm, hyz, map_zero]
      have hsplit : x₀ = y0 + z0 := by rw [hz0def]; abel
      have hz0norm : ‖z0‖ = Real.cos (Real.arcsin ‖y0‖) := by
        have h := hznorm 0
        rw [h0, ← hy0def, ← hz0def] at h
        exact h
      have hν0M : NormedSpace.normalize z0 ∈ Mrᗮ := by
        simpa only [NormedSpace.normalize, Complex.coe_smul] using
          Mrᗮ.smul_mem ((‖z0‖⁻¹ : ℝ) : ℂ) hz0M
      have hν0n : ‖NormedSpace.normalize z0‖ = 1 := NormedSpace.norm_normalize hz0
      have hcrosse : inner ℂ (NormedSpace.normalize z0) y0 = 0 := by
        have h := (Mr.mem_orthogonal _).mp hν0M _ hyM
        rw [← inner_conj_symm, h, map_zero]
      have hz0e : ((‖z0‖ : ℝ) : ℂ) • NormedSpace.normalize z0 = z0 :=
        (Complex.coe_smul _ _).symm.trans (NormedSpace.norm_smul_normalize z0)
      have hstep1 : inner ℂ (NormedSpace.normalize z0)
          (((‖z0‖ : ℝ) : ℂ) • NormedSpace.normalize z0) = ((‖z0‖ : ℝ) : ℂ) := by
        rw [inner_smul_right, inner_self_eq_one_of_norm_eq_one hν0n, mul_one]
      have hizz : inner ℂ (NormedSpace.normalize z0) z0 = ((‖z0‖ : ℝ) : ℂ) :=
        (congrArg (inner ℂ (NormedSpace.normalize z0)) hz0e).symm.trans hstep1
      have hinner : inner ℂ (NormedSpace.normalize z0) x₀ =
          ((Real.cos (Real.arcsin ‖y0‖) : ℝ) : ℂ) := by
        rw [hsplit, inner_add_right, hcrosse, zero_add, hizz, hz0norm]
      have hxν : inner ℂ x₀ (NormedSpace.normalize z0) =
          ((Real.cos (Real.arcsin ‖y0‖) : ℝ) : ℂ) := by
        rw [← inner_conj_symm, hinner, Complex.conj_ofReal]
      have hd : inner ℂ (NormedSpace.normalize z0 - x₀)
          (NormedSpace.normalize z0 - x₀) =
          ((2 - 2 * Real.cos (Real.arcsin ‖y0‖) : ℝ) : ℂ) := by
        rw [inner_sub_left, inner_sub_right, inner_sub_right,
          inner_self_eq_one_of_norm_eq_one hν0n, inner_self_eq_one_of_norm_eq_one hx₀,
          hinner, hxν]
        push_cast
        ring
      have hd2 : ‖NormedSpace.normalize z0 - x₀‖ ^ 2 =
          2 - 2 * Real.cos (Real.arcsin ‖y0‖) := by
        have h1 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (NormedSpace.normalize z0 - x₀)
        rw [hd] at h1
        simp only [mnrs2_ofReal_eq] at h1
        have h2 : ((‖NormedSpace.normalize z0 - x₀‖ : ℂ) ^ 2) =
            ((‖NormedSpace.normalize z0 - x₀‖ ^ 2 : ℝ) : ℂ) := by simp
        rw [h2] at h1
        exact (Complex.ofReal_inj.mp h1).symm
      have hy0nn : 0 ≤ Real.arcsin ‖y0‖ := hA0nn
      have hπ2y0 : Real.arcsin ‖y0‖ ≤ π / 2 := hπ2A0
      have heq : Real.cos (Real.arcsin ‖y0‖) =
          1 - 2 * (Real.sin (Real.arcsin ‖y0‖ / 2)) ^ 2 := by
        have key : ∀ θ : ℝ, Real.cos θ = 1 - 2 * (Real.sin (θ / 2)) ^ 2 := by
          intro θ
          have h := Real.sin_sq_add_cos_sq (θ / 2)
          have h2 : Real.cos (2 * (θ / 2)) = 1 - 2 * (Real.sin (θ / 2)) ^ 2 := by
            rw [Real.cos_two_mul]
            nlinarith [h]
          conv_lhs => rw [show θ = 2 * (θ / 2) from by ring]
          exact h2
        exact key (Real.arcsin ‖y0‖)
      have hsin2nn : 0 ≤ 2 * Real.sin (Real.arcsin ‖y0‖ / 2) := by
        refine mul_nonneg (by norm_num) ?_
        exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hy0nn])
          (by linarith [Real.pi_pos, hπ2y0])
      have hsq : ‖NormedSpace.normalize z0 - x₀‖ =
          2 * Real.sin (Real.arcsin ‖y0‖ / 2) := by
        apply (sq_eq_sq₀ (norm_nonneg _) hsin2nn).mp
        nlinarith [hd2, heq]
      rw [hsq]
      have hsinle : Real.sin (Real.arcsin ‖y0‖ / 2) ≤ Real.arcsin ‖y0‖ / 2 :=
        Real.sin_le (by linarith [hy0nn])
      linarith

  have hb : ∀ k, k + 1 ≤ t - 1 →
      ‖NormedSpace.normalize (raaState unmarkRefl R x₀ (k + 1) -
          markProj Mr (raaState unmarkRefl R x₀ (k + 1))) -
        NormedSpace.normalize (raaState unmarkRefl R x₀ k -
          markProj Mr (raaState unmarkRefl R x₀ k))‖ ≤
      13 * betaAt γ (k + 1) * ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖) := by
    intro k hk
    have hkT : k + 1 + 1 ≤ t := by omega
    obtain ⟨hφkRs, hek⟩ := henv k (by omega)
    obtain ⟨hφk1Rs, hek1⟩ := henv (k + 1) hkT
    have hbarjle : (3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖ ≤ π / 12 := by
      have h1 := hbarmono (show k + 1 ≤ t - 1 by omega)
      rw [hbarsucc k] at h1
      linarith [hbart1le, Real.pi_pos]
    have hsinbar : Real.sin ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖) ≤
        (3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖ := Real.sin_le (hbarnn k)
    have hσ2 : (∑ l ∈ Finset.Icc 1 k, (1 : ℝ) / (l : ℝ) ^ 2) ≤ 2 := mnrs_sum_inv_sq_le_two k
    have hγX : γ * ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖) ≤ (1 / 40) * (63 / 240) := by
      have h2 : (3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖ ≤ 63 / 240 :=
        hbarjle.trans (by linarith [hπ])
      nlinarith [hγ1, h2, hγ0.le, hbarnn k]
    have heb : |‖markProj Mr (raaState unmarkRefl R x₀ k)‖ -
        Real.sin ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖)| ≤
        γ * ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖) / 4 := by
      refine hek.trans ?_
      have hX : γ * ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖) * (1 / 8) *
          (∑ l ∈ Finset.Icc 1 k, (1 : ℝ) / (l : ℝ) ^ 2) ≤
          γ * ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖) * (1 / 8) * 2 := by
        refine mul_le_mul_of_nonneg_left hσ2 ?_
        exact mul_nonneg (mul_nonneg hγ0.le (hbarnn k)) (by norm_num)
      exact hX.trans (le_of_eq (by ring))
    have hsk : ‖markProj Mr (raaState unmarkRefl R x₀ k)‖ ≤ 1 / 2 := by
      have h1 := heb
      have h2 : Real.sin ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖) ≤ 63 / 240 :=
        hsinbar.trans (hbarjle.trans (by linarith [hπ]))
      have h3 : γ * ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖) / 4 ≤ 63 / 38400 := by
        nlinarith [hγX, hγ0.le]
      have hfin : (63 / 240 : ℝ) + 63 / 38400 ≤ 1 / 2 := by norm_num
      have h4 : ‖markProj Mr (raaState unmarkRefl R x₀ k)‖ ≤
          Real.sin ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖) +
          |‖markProj Mr (raaState unmarkRefl R x₀ k)‖ -
            Real.sin ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖)| := by
        have h := le_abs_self (‖markProj Mr (raaState unmarkRefl R x₀ k)‖ -
          Real.sin ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖))
        linarith
      linarith [h4, h1, h2, h3, hfin]
    have hϕk6 : Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖ ≤ π / 6 := by
      have h1 : Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖ ≤
          Real.arcsin (1 / 2) := Real.arcsin_le_arcsin hsk
      rw [show Real.arcsin (1 / 2) = π / 6 from by
        rw [← Real.sin_pi_div_six]
        exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])] at h1
      exact h1
    have hϕk3 : Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖ ≤ π / 3 := by
      linarith [Real.pi_pos]
    obtain ⟨ω, hstate, hωn, hscalar⟩ := mnrs2_step_decomp Mr Rs unmarkRefl hMneg hMid x₀ hx₀
      γ hγ0 R t hclose hRRs hfix hbound k (by omega) hφkRs hϕk3
    have hykM : markProj Mr (raaState unmarkRefl R x₀ k) ∈ Mr :=
      (Mr.orthogonalProjection (raaState unmarkRefl R x₀ k)).property
    have hzkM : raaState unmarkRefl R x₀ k - markProj Mr (raaState unmarkRefl R x₀ k) ∈ Mrᗮ := by
      rw [mnrs_mark_projection_eq]
      exact Submodule.sub_starProjection_mem_orthogonal _
    have hμM : NormedSpace.normalize (markProj Mr (raaState unmarkRefl R x₀ k)) ∈ Mr := by
      simpa only [NormedSpace.normalize, Complex.coe_smul] using
        Mr.smul_mem ((‖markProj Mr (raaState unmarkRefl R x₀ k)‖⁻¹ : ℝ) : ℂ) hykM
    have hνkM : NormedSpace.normalize (raaState unmarkRefl R x₀ k -
        markProj Mr (raaState unmarkRefl R x₀ k)) ∈ Mrᗮ := by
      simpa only [NormedSpace.normalize, Complex.coe_smul] using
        Mrᗮ.smul_mem ((‖raaState unmarkRefl R x₀ k -
          markProj Mr (raaState unmarkRefl R x₀ k)‖⁻¹ : ℝ) : ℂ) hzkM
    have hPmu : markProj Mr (NormedSpace.normalize (markProj Mr (raaState unmarkRefl R x₀ k))) =
        NormedSpace.normalize (markProj Mr (raaState unmarkRefl R x₀ k)) := by
      rw [mnrs_mark_projection_eq]
      exact (Submodule.starProjection_eq_self_iff).mpr hμM
    have hPnu : markProj Mr (NormedSpace.normalize (raaState unmarkRefl R x₀ k -
        markProj Mr (raaState unmarkRefl R x₀ k))) = 0 := by
      rw [mnrs_mark_projection_eq]
      exact (Submodule.starProjection_apply_eq_zero_iff _).mpr hνkM
    have hzk1 : raaState unmarkRefl R x₀ (k + 1) -
        markProj Mr (raaState unmarkRefl R x₀ (k + 1)) =
        (Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) : ℂ) •
            (NormedSpace.normalize (raaState unmarkRefl R x₀ k -
              markProj Mr (raaState unmarkRefl R x₀ k))) +
          (ω - markProj Mr ω) := by
      have h1 : markProj Mr (raaState unmarkRefl R x₀ (k + 1)) =
          (Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) : ℂ) •
              (NormedSpace.normalize (markProj Mr (raaState unmarkRefl R x₀ k))) +
            markProj Mr ω := by
        rw [hstate, map_add, map_add, map_smul, map_smul, hPmu, hPnu, smul_zero, add_zero]
      rw [h1, hstate]
      module
    have hczk1 : 2 / 3 ≤ ‖raaState unmarkRefl R x₀ (k + 1) -
        markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ := hcosge (k + 1) (by omega)
    have hczk : 2 / 3 ≤ ‖raaState unmarkRefl R x₀ k -
        markProj Mr (raaState unmarkRefl R x₀ k)‖ := hcosge k (by omega)
    have hzk1ne : raaState unmarkRefl R x₀ (k + 1) -
        markProj Mr (raaState unmarkRefl R x₀ (k + 1)) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hczk1
      norm_num at hczk1
    have hzkne : raaState unmarkRefl R x₀ k -
        markProj Mr (raaState unmarkRefl R x₀ k) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hczk
      norm_num at hczk
    have hνk1n : ‖NormedSpace.normalize (raaState unmarkRefl R x₀ (k + 1) -
        markProj Mr (raaState unmarkRefl R x₀ (k + 1)))‖ = 1 :=
      NormedSpace.norm_normalize hzk1ne
    have hνkn : ‖NormedSpace.normalize (raaState unmarkRefl R x₀ k -
        markProj Mr (raaState unmarkRefl R x₀ k))‖ = 1 :=
      NormedSpace.norm_normalize hzkne
    have hkey : ‖raaState unmarkRefl R x₀ (k + 1) -
        markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ •
        (NormedSpace.normalize (raaState unmarkRefl R x₀ (k + 1) -
            markProj Mr (raaState unmarkRefl R x₀ (k + 1))) -
          NormedSpace.normalize (raaState unmarkRefl R x₀ k -
            markProj Mr (raaState unmarkRefl R x₀ k))) =
        (((Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) -
          ‖raaState unmarkRefl R x₀ (k + 1) -
            markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ : ℝ) : ℂ) •
          (NormedSpace.normalize (raaState unmarkRefl R x₀ k -
            markProj Mr (raaState unmarkRefl R x₀ k)))) +
        (ω - markProj Mr ω) := by
      have e1 : ‖raaState unmarkRefl R x₀ (k + 1) -
          markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ •
          (NormedSpace.normalize (raaState unmarkRefl R x₀ (k + 1) -
              markProj Mr (raaState unmarkRefl R x₀ (k + 1))) -
            NormedSpace.normalize (raaState unmarkRefl R x₀ k -
              markProj Mr (raaState unmarkRefl R x₀ k))) =
          (raaState unmarkRefl R x₀ (k + 1) -
            markProj Mr (raaState unmarkRefl R x₀ (k + 1))) -
          ‖raaState unmarkRefl R x₀ (k + 1) -
            markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ •
            (NormedSpace.normalize (raaState unmarkRefl R x₀ k -
              markProj Mr (raaState unmarkRefl R x₀ k))) := by
        rw [smul_sub, NormedSpace.norm_smul_normalize]
      have e2 := congrArg (fun v : W =>
        v - ‖raaState unmarkRefl R x₀ (k + 1) -
          markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ •
          (NormedSpace.normalize (raaState unmarkRefl R x₀ k -
            markProj Mr (raaState unmarkRefl R x₀ k)))) hzk1
      have e3 : ((Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) : ℂ) •
            (NormedSpace.normalize (raaState unmarkRefl R x₀ k -
              markProj Mr (raaState unmarkRefl R x₀ k))) +
            (ω - markProj Mr ω)) -
          ‖raaState unmarkRefl R x₀ (k + 1) -
            markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ •
            (NormedSpace.normalize (raaState unmarkRefl R x₀ k -
              markProj Mr (raaState unmarkRefl R x₀ k))) =
          (((Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) -
            ‖raaState unmarkRefl R x₀ (k + 1) -
              markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ : ℝ) : ℂ) •
            (NormedSpace.normalize (raaState unmarkRefl R x₀ k -
              markProj Mr (raaState unmarkRefl R x₀ k)))) +
          (ω - markProj Mr ω) := by
        rw [Complex.ofReal_sub, sub_smul]
        simp only [Complex.coe_smul]
        abel
      exact (e1.trans e2).trans e3
    have hsknn : 0 ≤ ‖markProj Mr (raaState unmarkRefl R x₀ k)‖ := norm_nonneg _
    have hsk1le : ‖markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ ≤ 1 := by
      have h := Submodule.norm_starProjection_apply_le Mr (raaState unmarkRefl R x₀ (k + 1))
      have hn : ‖raaState unmarkRefl R x₀ (k + 1)‖ = 1 := by rw [mnrs_raa_state_norm, hx₀]
      exact h.trans_eq hn
    have hsin3nn : 0 ≤ Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · have h1 := Real.arcsin_nonneg.mpr hsknn
        linarith
      · have h1 : 3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖ ≤ π := by
          linarith [hϕk6, Real.pi_pos]
        linarith
    have hc3pos : 0 ≤ Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) := by
      have h1 : 3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖ ≤ π / 2 := by
        linarith [hϕk6, Real.pi_pos]
      have h0 : -(π / 2) ≤ 3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖ := by
        have hn := Real.arcsin_nonneg.mpr hsknn
        linarith [Real.pi_pos]
      exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le h0 h1
    have hsk1sq : 0 ≤ 1 - ‖markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ ^ 2 := by
      nlinarith [hsk1le, norm_nonneg (markProj Mr (raaState unmarkRefl R x₀ (k + 1)))]
    have hc1sq : ‖raaState unmarkRefl R x₀ (k + 1) -
        markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ ^ 2 =
        1 - ‖markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ ^ 2 := by
      rw [hznorm (k + 1), Real.cos_arcsin, Real.sq_sqrt hsk1sq]
    have hc2sq : Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) ^ 2 =
        1 - Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) ^ 2 := by
      have h := Real.sin_sq_add_cos_sq
        (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖)
      linarith
    have habsc : |Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) -
        ‖raaState unmarkRefl R x₀ (k + 1) -
          markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖| ≤ 3 * ‖ω‖ := by
      have hsumpos : 0 ≤ ‖raaState unmarkRefl R x₀ (k + 1) -
          markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ +
          Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) :=
        add_nonneg ((by norm_num : (0 : ℝ) ≤ 2 / 3).trans hczk1) hc3pos
      have habs : |Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) -
          ‖raaState unmarkRefl R x₀ (k + 1) -
            markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖| *
          (‖raaState unmarkRefl R x₀ (k + 1) -
            markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ +
          Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖)) ≤
          ‖ω‖ * 2 := by
        have e1 : |Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) -
            ‖raaState unmarkRefl R x₀ (k + 1) -
              markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖| *
            (‖raaState unmarkRefl R x₀ (k + 1) -
              markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ +
            Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖)) =
            |(Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) -
              ‖raaState unmarkRefl R x₀ (k + 1) -
                markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖) *
              (‖raaState unmarkRefl R x₀ (k + 1) -
                markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ +
              Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖))| := by
          rw [abs_mul, abs_of_nonneg hsumpos]
        have e2 : (Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) -
            ‖raaState unmarkRefl R x₀ (k + 1) -
              markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖) *
            (‖raaState unmarkRefl R x₀ (k + 1) -
              markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ +
            Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖)) =
            (‖markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ -
              Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖)) *
            (Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) +
              ‖markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖) := by
          linear_combination hc2sq - hc1sq
        rw [e1, e2, abs_mul]
        have hsum2nn : 0 ≤
            |Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) +
              ‖markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖| := abs_nonneg _
        refine mul_le_mul hscalar ?_ hsum2nn (norm_nonneg ω)
        rw [abs_of_nonneg (add_nonneg hsin3nn
          (norm_nonneg (markProj Mr (raaState unmarkRefl R x₀ (k + 1)))))]
        linarith [Real.sin_le_one (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖),
          hsk1le, hsin3nn]
      have hsumle : 2 / 3 ≤ ‖raaState unmarkRefl R x₀ (k + 1) -
          markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ +
          Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) := by
        linarith [hczk1, hc3pos]
      have hm : |Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) -
          ‖raaState unmarkRefl R x₀ (k + 1) -
            markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖| * (2 / 3) ≤
          |Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) -
          ‖raaState unmarkRefl R x₀ (k + 1) -
            markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖| *
          (‖raaState unmarkRefl R x₀ (k + 1) -
            markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ +
          Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖)) :=
        mul_le_mul_of_nonneg_left hsumle (abs_nonneg _)
      linarith [hm.trans habs]
    have hω'le : ‖ω - markProj Mr ω‖ ≤ ‖ω‖ := mnrs2_unmarked_norm_le Mr ω
    have hstep : ‖raaState unmarkRefl R x₀ (k + 1) -
        markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ *
        ‖NormedSpace.normalize (raaState unmarkRefl R x₀ (k + 1) -
            markProj Mr (raaState unmarkRefl R x₀ (k + 1))) -
          NormedSpace.normalize (raaState unmarkRefl R x₀ k -
            markProj Mr (raaState unmarkRefl R x₀ k))‖ ≤
        3 * ‖ω‖ + ‖ω - markProj Mr ω‖ := by
      have h1 : ‖raaState unmarkRefl R x₀ (k + 1) -
          markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ *
          ‖NormedSpace.normalize (raaState unmarkRefl R x₀ (k + 1) -
              markProj Mr (raaState unmarkRefl R x₀ (k + 1))) -
            NormedSpace.normalize (raaState unmarkRefl R x₀ k -
              markProj Mr (raaState unmarkRefl R x₀ k))‖ =
          ‖((Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) -
            ‖raaState unmarkRefl R x₀ (k + 1) -
              markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ : ℝ) : ℂ) •
            (NormedSpace.normalize (raaState unmarkRefl R x₀ k -
              markProj Mr (raaState unmarkRefl R x₀ k))) +
            (ω - markProj Mr ω)‖ := by
        rw [← hkey, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      rw [h1]
      calc ‖((Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) -
            ‖raaState unmarkRefl R x₀ (k + 1) -
              markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ : ℝ) : ℂ) •
            (NormedSpace.normalize (raaState unmarkRefl R x₀ k -
              markProj Mr (raaState unmarkRefl R x₀ k))) +
            (ω - markProj Mr ω)‖
          ≤ ‖((Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) -
            ‖raaState unmarkRefl R x₀ (k + 1) -
              markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖ : ℝ) : ℂ) •
            (NormedSpace.normalize (raaState unmarkRefl R x₀ k -
              markProj Mr (raaState unmarkRefl R x₀ k)))‖ + ‖ω - markProj Mr ω‖ :=
            norm_add_le _ _
        _ = |Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) -
            ‖raaState unmarkRefl R x₀ (k + 1) -
              markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖| *
            ‖NormedSpace.normalize (raaState unmarkRefl R x₀ k -
              markProj Mr (raaState unmarkRefl R x₀ k))‖ + ‖ω - markProj Mr ω‖ := by
            rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        _ = |Real.cos (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) -
            ‖raaState unmarkRefl R x₀ (k + 1) -
              markProj Mr (raaState unmarkRefl R x₀ (k + 1))‖| * 1 +
            ‖ω - markProj Mr ω‖ := by rw [hνkn]
        _ ≤ 3 * ‖ω‖ + ‖ω - markProj Mr ω‖ := by
            rw [mul_one]
            linarith [habsc]
    have hsin2 : |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖)| ≤
        2 * ‖markProj Mr (raaState unmarkRefl R x₀ k)‖ := by
      have h2ϕnn : 0 ≤ Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · have h1 := Real.arcsin_nonneg.mpr hsknn
          linarith
        · have h1 : 2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖ ≤ π := by
            linarith [hϕk6, Real.pi_pos]
          linarith
      rw [abs_of_nonneg h2ϕnn, Real.sin_two_mul]
      have hcosle := Real.cos_le_one
        (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖)
      have hsinϕk : Real.sin (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) =
          ‖markProj Mr (raaState unmarkRefl R x₀ k)‖ :=
        Real.sin_arcsin (by linarith [hsknn]) (hsk.trans (by norm_num))
      rw [hsinϕk]
      nlinarith [hcosle, hsknn]
    have hskbound : ‖markProj Mr (raaState unmarkRefl R x₀ k)‖ ≤
        (161 / 160) * ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖) := by
      have h4 : ‖markProj Mr (raaState unmarkRefl R x₀ k)‖ ≤
          Real.sin ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖) +
          |‖markProj Mr (raaState unmarkRefl R x₀ k)‖ -
            Real.sin ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖)| := by
        have h := le_abs_self (‖markProj Mr (raaState unmarkRefl R x₀ k)‖ -
          Real.sin ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖))
        linarith
      have h3 : γ / 4 ≤ 1 / 160 := by linarith
      nlinarith [h4, heb, hsinbar, h3, hbarnn k, hγ0.le]
    have hβnn : 0 ≤ betaAt γ (k + 1) := by
      unfold betaAt
      positivity
    have hωb : ‖ω‖ ≤ 2 * (161 / 160) * betaAt γ (k + 1) *
        ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖) := by
      calc ‖ω‖ ≤ betaAt γ (k + 1) *
          |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ k)‖)| := hωn
        _ ≤ betaAt γ (k + 1) * (2 * ‖markProj Mr (raaState unmarkRefl R x₀ k)‖) :=
            mul_le_mul_of_nonneg_left hsin2 hβnn
        _ ≤ betaAt γ (k + 1) * (2 * ((161 / 160) *
              ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖))) := by
            gcongr
        _ = 2 * (161 / 160) * betaAt γ (k + 1) *
            ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖) := by ring
    have hdrift1 : ‖NormedSpace.normalize (raaState unmarkRefl R x₀ (k + 1) -
          markProj Mr (raaState unmarkRefl R x₀ (k + 1))) -
        NormedSpace.normalize (raaState unmarkRefl R x₀ k -
          markProj Mr (raaState unmarkRefl R x₀ k))‖ ≤ 6 * ‖ω‖ := by
      nlinarith [hstep, hω'le, hczk1,
        norm_nonneg (NormedSpace.normalize (raaState unmarkRefl R x₀ (k + 1) -
          markProj Mr (raaState unmarkRefl R x₀ (k + 1))) -
        NormedSpace.normalize (raaState unmarkRefl R x₀ k -
          markProj Mr (raaState unmarkRefl R x₀ k)))]
    calc ‖NormedSpace.normalize (raaState unmarkRefl R x₀ (k + 1) -
          markProj Mr (raaState unmarkRefl R x₀ (k + 1))) -
        NormedSpace.normalize (raaState unmarkRefl R x₀ k -
          markProj Mr (raaState unmarkRefl R x₀ k))‖
        ≤ 6 * ‖ω‖ := hdrift1
      _ ≤ 6 * (2 * (161 / 160) * betaAt γ (k + 1) *
          ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖)) := by gcongr
      _ ≤ 13 * betaAt γ (k + 1) * ((3 : ℝ) ^ k * Real.arcsin ‖markProj Mr x₀‖) := by
          nlinarith [hβnn, mul_nonneg (hbarnn k) hβnn, mul_nonneg (hbarnn k) hβnn]

  have ha : ∀ k, k + 1 ≤ t - 1 →
      ‖attemptState Mr (raaUnitary unmarkRefl R) x₀ (k + 1) -
        NormedSpace.normalize (raaState unmarkRefl R x₀ (k + 1) -
          markProj Mr (raaState unmarkRefl R x₀ (k + 1)))‖ ≤
      3 * ‖attemptState Mr (raaUnitary unmarkRefl R) x₀ k - x₀‖ := by
    intro k hk
    have hψ1 : attemptState Mr (raaUnitary unmarkRefl R) x₀ (k + 1) =
        NormedSpace.normalize (unmarkedPart Mr
          ((raaUnitary unmarkRefl R (k + 1))
            (attemptState Mr (raaUnitary unmarkRefl R) x₀ k))) := rfl
    have hc2 : 2 / 3 ≤ ‖(raaUnitary unmarkRefl R (k + 1)) x₀ -
        markProj Mr ((raaUnitary unmarkRefl R (k + 1)) x₀)‖ :=
      hcosge (k + 1) (by omega)
    rw [hψ1]
    refine (mnrs2_normalize_sub _ _ hc2).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hEq : unmarkedPart Mr ((raaUnitary unmarkRefl R (k + 1))
          (attemptState Mr (raaUnitary unmarkRefl R) x₀ k)) -
        ((raaUnitary unmarkRefl R (k + 1)) x₀ -
          markProj Mr ((raaUnitary unmarkRefl R (k + 1)) x₀)) =
        unmarkedPart Mr ((raaUnitary unmarkRefl R (k + 1))
          (attemptState Mr (raaUnitary unmarkRefl R) x₀ k - x₀)) := by
      unfold unmarkedPart
      simp only [map_sub]
      abel
    rw [hEq]
    calc ‖unmarkedPart Mr ((raaUnitary unmarkRefl R (k + 1))
          (attemptState Mr (raaUnitary unmarkRefl R) x₀ k - x₀))‖
        ≤ ‖(raaUnitary unmarkRefl R (k + 1))
            (attemptState Mr (raaUnitary unmarkRefl R) x₀ k - x₀)‖ :=
          mnrs2_unmarked_norm_le Mr _
      _ = ‖attemptState Mr (raaUnitary unmarkRefl R) x₀ k - x₀‖ :=
          (raaUnitary unmarkRefl R (k + 1)).norm_map _

  have hD : ∀ m, m ≤ t - 1 →
      ‖NormedSpace.normalize (raaState unmarkRefl R x₀ m -
          markProj Mr (raaState unmarkRefl R x₀ m)) - x₀‖ ≤
      Real.arcsin ‖markProj Mr x₀‖ +
        13 * Real.arcsin ‖markProj Mr x₀‖ *
          (∑ j ∈ Finset.range m, betaAt γ (j + 1) * (3 : ℝ) ^ j) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      rw [h0]
      exact hc0
    | succ m ih =>
      intro hm
      have hbnd := hb m hm
      have hprev := ih (by omega)
      have hsplit : (NormedSpace.normalize (raaState unmarkRefl R x₀ (m + 1) -
            markProj Mr (raaState unmarkRefl R x₀ (m + 1))) - x₀) =
          (NormedSpace.normalize (raaState unmarkRefl R x₀ (m + 1) -
            markProj Mr (raaState unmarkRefl R x₀ (m + 1))) -
            NormedSpace.normalize (raaState unmarkRefl R x₀ m -
              markProj Mr (raaState unmarkRefl R x₀ m))) +
          (NormedSpace.normalize (raaState unmarkRefl R x₀ m -
            markProj Mr (raaState unmarkRefl R x₀ m)) - x₀) := by abel
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [Finset.mul_sum, Finset.sum_range_succ]
      rw [Finset.mul_sum] at hprev
      have hmul : 13 * betaAt γ (m + 1) * ((3 : ℝ) ^ m * Real.arcsin ‖markProj Mr x₀‖) =
          13 * Real.arcsin ‖markProj Mr x₀‖ * (betaAt γ (m + 1) * (3 : ℝ) ^ m) := by ring
      linarith [hbnd, hprev, hmul]

  have hβnn : ∀ i, 0 ≤ betaAt γ i := by
    intro i
    unfold betaAt
    positivity
  have hicc : ∀ n, (∑ j ∈ Finset.range n, betaAt γ (j + 1)) =
      (∑ l ∈ Finset.Icc 1 n, betaAt γ l) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  have hB : ∀ n, (∑ l ∈ Finset.Icc 1 n, betaAt γ l) ≤ 9 / π ^ 3 * γ := by
    intro n
    have hsum : (∑ l ∈ Finset.Icc 1 n, betaAt γ l) =
        18 / (4 * π ^ 3) * γ * (∑ l ∈ Finset.Icc 1 n, (1 : ℝ) / (l : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by
        unfold betaAt
        rw [div_eq_mul_inv (18 / (4 * π ^ 3) * γ) ((l : ℝ) ^ 2), inv_eq_one_div]
    have hK : (0 : ℝ) ≤ 18 / (4 * π ^ 3) * γ := by positivity
    refine (hsum.trans_le (mul_le_mul_of_nonneg_left (mnrs_sum_inv_sq_le_two n) hK)).trans_eq ?_
    ring

  have hTle : (∑ j ∈ Finset.range (t - 1),
        betaAt γ (j + 1) * ((3 : ℝ) ^ (t - 1) - (3 : ℝ) ^ j)) ≤
      (3 : ℝ) ^ (t - 1) * (∑ j ∈ Finset.range (t - 1), betaAt γ (j + 1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ =>
      (mul_le_mul_of_nonneg_left (sub_le_self _ (pow_nonneg (by norm_num) _))
        (hβnn (j + 1))).trans_eq (mul_comm _ _)

  have hΔ : ∀ n, n ≤ t - 1 →
      ‖attemptState Mr (raaUnitary unmarkRefl R) x₀ n - x₀‖ ≤
      Real.arcsin ‖markProj Mr x₀‖ * (((3 : ℝ) ^ n - 1) / 2) +
        (13 * Real.arcsin ‖markProj Mr x₀‖ / 2) *
          (∑ j ∈ Finset.range n, betaAt γ (j + 1) * ((3 : ℝ) ^ n - (3 : ℝ) ^ j)) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0ψ : attemptState Mr (raaUnitary unmarkRefl R) x₀ 0 = x₀ := rfl
      rw [h0ψ, sub_self, norm_zero]
      simp only [Finset.range_zero, Finset.sum_empty, pow_zero]
      norm_num
    | succ n ih =>
      intro hn
      have hsplit : attemptState Mr (raaUnitary unmarkRefl R) x₀ (n + 1) - x₀ =
          (attemptState Mr (raaUnitary unmarkRefl R) x₀ (n + 1) -
            NormedSpace.normalize (raaState unmarkRefl R x₀ (n + 1) -
              markProj Mr (raaState unmarkRefl R x₀ (n + 1)))) +
          (NormedSpace.normalize (raaState unmarkRefl R x₀ (n + 1) -
            markProj Mr (raaState unmarkRefl R x₀ (n + 1))) - x₀) := by abel
      have h1 := ha n hn
      have h2 := hD (n + 1) hn
      have ihn := ih (by omega)
      have hpow : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := pow_succ' _ _
      have hS2 : (∑ j ∈ Finset.range (n + 1), betaAt γ (j + 1) * (3 : ℝ) ^ j) =
          (∑ j ∈ Finset.range n, betaAt γ (j + 1) * (3 : ℝ) ^ j) +
            betaAt γ (n + 1) * (3 : ℝ) ^ n :=
        Finset.sum_range_succ _ n
      have hS : (∑ j ∈ Finset.range (n + 1),
            betaAt γ (j + 1) * (3 * (3 : ℝ) ^ n - (3 : ℝ) ^ j)) =
          3 * (∑ j ∈ Finset.range n, betaAt γ (j + 1) * ((3 : ℝ) ^ n - (3 : ℝ) ^ j)) +
          2 * (∑ j ∈ Finset.range n, betaAt γ (j + 1) * (3 : ℝ) ^ j) +
          2 * (betaAt γ (n + 1) * (3 : ℝ) ^ n) := by
        have hA : (∑ j ∈ Finset.range n,
              betaAt γ (j + 1) * (3 * (3 : ℝ) ^ n - (3 : ℝ) ^ j)) =
            3 * (∑ j ∈ Finset.range n, betaAt γ (j + 1) * ((3 : ℝ) ^ n - (3 : ℝ) ^ j)) +
            2 * (∑ j ∈ Finset.range n, betaAt γ (j + 1) * (3 : ℝ) ^ j) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        have hB' : betaAt γ (n + 1) * (3 * (3 : ℝ) ^ n - (3 : ℝ) ^ n) =
            2 * (betaAt γ (n + 1) * (3 : ℝ) ^ n) := by ring
        rw [Finset.sum_range_succ, hA, hB']
      have hS3 : (13 * Real.arcsin ‖markProj Mr x₀‖ / 2) *
          (∑ j ∈ Finset.range (n + 1),
            betaAt γ (j + 1) * (3 * (3 : ℝ) ^ n - (3 : ℝ) ^ j)) =
          3 * ((13 * Real.arcsin ‖markProj Mr x₀‖ / 2) *
            (∑ j ∈ Finset.range n, betaAt γ (j + 1) * ((3 : ℝ) ^ n - (3 : ℝ) ^ j))) +
          13 * Real.arcsin ‖markProj Mr x₀‖ *
            (∑ j ∈ Finset.range (n + 1), betaAt γ (j + 1) * (3 : ℝ) ^ j) := by
        rw [hS, hS2]
        ring
      have hF : Real.arcsin ‖markProj Mr x₀‖ * ((3 * (3 : ℝ) ^ n - 1) / 2) =
          3 * (Real.arcsin ‖markProj Mr x₀‖ * ((3 : ℝ) ^ n - 1) / 2) +
          Real.arcsin ‖markProj Mr x₀‖ := by ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [hpow, hF, hS3]
      linarith [h1, h2, ihn]

  have hmain := hΔ (t - 1) (Nat.le_refl _)
  have h1 : Real.arcsin ‖markProj Mr x₀‖ * (((3 : ℝ) ^ (t - 1) - 1) / 2) ≤ π / 8 := by
    have hle : ((3 : ℝ) ^ (t - 1) - 1) / 2 ≤ (3 : ℝ) ^ (t - 1) / 2 := by linarith
    have h2 : Real.arcsin ‖markProj Mr x₀‖ * (((3 : ℝ) ^ (t - 1) - 1) / 2) ≤
        Real.arcsin ‖markProj Mr x₀‖ * ((3 : ℝ) ^ (t - 1) / 2) :=
      mul_le_mul_of_nonneg_left hle hA0nn
    have h3 : Real.arcsin ‖markProj Mr x₀‖ * ((3 : ℝ) ^ (t - 1) / 2) =
        (Real.arcsin ‖markProj Mr x₀‖ * (3 : ℝ) ^ (t - 1)) / 2 := by ring
    have h4 : Real.arcsin ‖markProj Mr x₀‖ * (3 : ℝ) ^ (t - 1) ≤ π / 4 := by
      rw [mul_comm]
      exact hbart1le
    linarith [h2, h3, h4, Real.pi_pos]
  have h2 : (13 * Real.arcsin ‖markProj Mr x₀‖ / 2) *
      (∑ j ∈ Finset.range (t - 1),
        betaAt γ (j + 1) * ((3 : ℝ) ^ (t - 1) - (3 : ℝ) ^ j)) ≤
      (3 / 2) * γ := by
    have hA : (13 * Real.arcsin ‖markProj Mr x₀‖ / 2) *
        (∑ j ∈ Finset.range (t - 1),
          betaAt γ (j + 1) * ((3 : ℝ) ^ (t - 1) - (3 : ℝ) ^ j)) ≤
        (13 * Real.arcsin ‖markProj Mr x₀‖ / 2) * ((3 : ℝ) ^ (t - 1) * (9 / π ^ 3 * γ)) := by
      refine mul_le_mul_of_nonneg_left ?_
        (div_nonneg (mul_nonneg (by norm_num) hA0nn) (by norm_num))
      exact hTle.trans (mul_le_mul_of_nonneg_left
        (by rw [hicc (t - 1)]; exact hB (t - 1))
        (pow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) (t - 1)))
    have hEq1 : (13 * Real.arcsin ‖markProj Mr x₀‖ / 2) *
        ((3 : ℝ) ^ (t - 1) * (9 / π ^ 3 * γ)) =
        (13 / 2) * (9 / π ^ 3) * γ *
          (Real.arcsin ‖markProj Mr x₀‖ * (3 : ℝ) ^ (t - 1)) := by ring
    have hstep2 : (13 / 2) * (9 / π ^ 3) * γ *
        (Real.arcsin ‖markProj Mr x₀‖ * (3 : ℝ) ^ (t - 1)) ≤
        (13 / 2) * (9 / π ^ 3) * γ * (π / 4) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [mul_comm]
      exact hbart1le
    have hEq2 : (13 / 2) * (9 / π ^ 3) * γ * (π / 4) = 117 / (8 * π ^ 2) * γ := by
      field_simp [Real.pi_pos.ne']
      ring
    have hfinal : 117 / (8 * π ^ 2) * γ ≤ (3 / 2) * γ := by
      have hπ2 : (39 / 4 : ℝ) ≤ π ^ 2 := by
        have hππ : (3.14 : ℝ) * 3.14 ≤ π * π :=
          mul_le_mul hπge hπge (by norm_num) Real.pi_pos.le
        have h314 : (3.14 : ℝ) * 3.14 = 24649 / 2500 := by norm_num
        have hval : (39 / 4 : ℝ) ≤ 24649 / 2500 := by norm_num
        rw [pow_two]
        linarith [hππ, h314, hval]
      have hstep : 117 / (8 * π ^ 2) ≤ 3 / 2 := by
        have hden : (0 : ℝ) < 8 * π ^ 2 := mul_pos (by norm_num) (pow_pos Real.pi_pos 2)
        rw [div_le_iff₀ hden]
        linarith [hπ2]
      exact mul_le_mul_of_nonneg_right hstep hγ0.le
    exact ((hA.trans_eq hEq1).trans hstep2).trans ((le_of_eq hEq2).trans hfinal)
  linarith [hmain, h1, h2]

theorem mnrs_tolerant_raa_lemma_two : Lemma2 := by
  intro W _ _ _ Mr unmarkRefl hMneg hMid x₀ hx₀ γ hγ0 hγ1 ε hε0 hε1 hεle
    tMax R c₁ c₂ hc₁ hc₂ costR costMark Rs hxRs hclose hRRs hfix hbound hcost hmark hwin hmin
  refine ⟨?_, ?_⟩
  · intro hpM
    classical
    have hs1le : ‖markProj Mr x₀‖ ≤ 1 :=
      (Submodule.norm_starProjection_apply_le Mr x₀).trans_eq hx₀
    have hs0val : Real.sqrt (markedMass Mr x₀) = ‖markProj Mr x₀‖ := by
      unfold markedMass
      exact Real.sqrt_sq (norm_nonneg _)
    have hεm : ε ≤ ‖markProj Mr x₀‖ ^ 2 := hεle hpM
    have hsqrt : Real.sqrt ε ≤ ‖markProj Mr x₀‖ := by
      have h2 := Real.sqrt_le_sqrt hεm
      rwa [Real.sqrt_sq (norm_nonneg (markProj Mr x₀))] at h2
    have hmem : (π / 4 : ℝ) ≤ (3 : ℝ) ^ tMax * Real.arcsin ‖markProj Mr x₀‖ :=
      hwin.1.trans (mul_le_mul_of_nonneg_left (Real.arcsin_le_arcsin hsqrt)
        (pow_nonneg (by norm_num) _))
    have hex : ∃ n, (π / 4 : ℝ) ≤ (3 : ℝ) ^ n * Real.arcsin ‖markProj Mr x₀‖ :=
      ⟨tMax, hmem⟩
    obtain ⟨t, htG, htmin, htle⟩ : ∃ t, (π / 4 : ℝ) ≤
          (3 : ℝ) ^ t * Real.arcsin ‖markProj Mr x₀‖ ∧
        (∀ j, j < t → ¬(π / 4 : ℝ) ≤
          (3 : ℝ) ^ j * Real.arcsin ‖markProj Mr x₀‖) ∧ t ≤ tMax :=
      ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj,
        Nat.find_le hmem⟩
    rcases Nat.eq_zero_or_pos t with rfl | ht0pos
    · rw [pow_zero, one_mul] at htG
      have hIcc : Real.arcsin ‖markProj Mr x₀‖ ∈ Set.Icc (π / 4) (3 * π / 4) :=
        ⟨htG, ((Real.arcsin_mem_Icc _).2).trans (by linarith [Real.pi_pos])⟩
      have hsin := mnrs2_sin_window _ hIcc
      rw [Real.sin_arcsin (by linarith [norm_nonneg (markProj Mr x₀)]) hs1le] at hsin
      have hsq : (1 / Real.sqrt 2) ^ 2 ≤ markedMass Mr x₀ := by
        change (1 / Real.sqrt 2) ^ 2 ≤ ‖markProj Mr x₀‖ ^ 2
        exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hsin
      have hval : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
        rw [← mnrs2_sqrt_two_div_two, div_pow,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have hfin : 1 / 12 - 3 * γ ≤ markedMass Mr x₀ := by
        have hγ' : 3 * γ ≤ 3 * (1 / 40) := by nlinarith [hγ1]
        have hc : 1 / 12 - 3 * (1 / 40) = 1 / 120 := by norm_num
        have h12 : 1 / 12 - 3 * γ ≤ 1 / 2 := by linarith
        rw [hval] at hsq
        exact h12.trans hsq
      exact hfin.trans (mnrs_tolerant_success_ge_initial Mr (raaUnitary unmarkRefl R) x₀
        (by rw [hx₀]) (Nat.max tMax 1))
    · have hwt : (3 : ℝ) ^ t * Real.arcsin ‖markProj Mr x₀‖ ≤ 3 * π / 4 := by
        have h1 := htmin (t - 1) (by omega)
        rw [not_le] at h1
        have hp : (3 : ℝ) ^ t * Real.arcsin ‖markProj Mr x₀‖ =
            3 * ((3 : ℝ) ^ (t - 1) * Real.arcsin ‖markProj Mr x₀‖) := by
          have h := pow_succ (3 : ℝ) (t - 1)
          rw [show t - 1 + 1 = t from by omega] at h
          rw [h]
          ring
        linarith [h1, hp, Real.pi_pos]
      have htrRRs : ∀ i, 1 ≤ i → i ≤ t → ∀ z ∈ Rs, R i z ∈ Rs := fun i hi hti =>
        hRRs i hi (hti.trans (htle.trans (Nat.le_max_left tMax 1)))
      have htrfix : ∀ i, 1 ≤ i → i ≤ t →
          R i (raaState unmarkRefl R x₀ (i - 1)) = raaState unmarkRefl R x₀ (i - 1) :=
        fun i hi hti => hfix i hi (hti.trans (htle.trans (Nat.le_max_left tMax 1)))
      have htrbound : ∀ i, 1 ≤ i → i ≤ t → ∀ ψ ∈ Rs,
          ψ ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ (i - 1)})ᗮ →
          ‖R i ψ + ψ - (2 : ℂ) • (lineProj (raaState unmarkRefl R x₀ (i - 1)) ψ)‖
            ≤ betaAt γ i * ‖ψ‖ :=
        fun i hi hti ψ hψ horth =>
          hbound i hi (hti.trans (htle.trans (Nat.le_max_left tMax 1))) ψ hψ horth
      have hδ := mnrs2_delta_chain Mr Rs unmarkRefl hMneg hMid x₀ hx₀ γ hγ0 hγ1 t ht0pos R
        hxRs hclose htrRRs htrfix htrbound ⟨htG, hwt⟩
      have hpl := mnrs_projection_lower Mr Rs unmarkRefl hMneg hMid x₀ hx₀ γ hγ0
        (hγ1.trans (by norm_num)) t R hxRs hclose htrRRs htrfix htrbound
        (by rw [hs0val]; exact ⟨htG, hwt⟩)
        (fun j hj hmem' => htmin j hj (by rw [hs0val] at hmem'; exact hmem'.1))
      have hφt : raaState unmarkRefl R x₀ t = (raaUnitary unmarkRefl R t) x₀ := rfl
      have hδu : ‖(raaUnitary unmarkRefl R t)
            (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1)) -
            raaState unmarkRefl R x₀ t‖ ≤ π / 8 + (3 / 2) * γ := by
        have hE : (raaUnitary unmarkRefl R t)
            (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1)) -
            raaState unmarkRefl R x₀ t =
            (raaUnitary unmarkRefl R t)
              (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1) - x₀) := by
          simp only [hφt, map_sub]
        rw [hE, (raaUnitary unmarkRefl R t).norm_map]
        exact hδ
      have hlip : ‖markProj Mr ((raaUnitary unmarkRefl R t)
            (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1))) -
            markProj Mr (raaState unmarkRefl R x₀ t)‖ ≤
          ‖(raaUnitary unmarkRefl R t)
            (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1)) -
            raaState unmarkRefl R x₀ t‖ := by
        have hE2 : markProj Mr ((raaUnitary unmarkRefl R t)
              (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1))) -
              markProj Mr (raaState unmarkRefl R x₀ t) =
              markProj Mr ((raaUnitary unmarkRefl R t)
                (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1) - x₀)) := by
          simp only [hφt, map_sub]
        have hE3 : (raaUnitary unmarkRefl R t)
            (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1)) -
            raaState unmarkRefl R x₀ t =
            (raaUnitary unmarkRefl R t)
              (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1) - x₀) := by
          simp only [hφt, map_sub]
        have h := Submodule.norm_starProjection_apply_le Mr
          ((raaUnitary unmarkRefl R t)
            (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1) - x₀))
        rw [hE2, hE3]
        exact h
      have h3 := norm_sub_norm_le (markProj Mr (raaState unmarkRefl R x₀ t))
        (markProj Mr ((raaUnitary unmarkRefl R t)
          (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1))))
      rw [norm_sub_rev] at h3
      have hX : 5 / 17 - 3 * γ ≤ ‖markProj Mr ((raaUnitary unmarkRefl R t)
          (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1)))‖ := by
        have hkey : (1 / Real.sqrt 2 - γ) - (π / 8 + (3 / 2) * γ) ≤
            ‖markProj Mr ((raaUnitary unmarkRefl R t)
              (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1)))‖ := by
          linarith [hpl, hlip, hδu, h3]
        have h710 : (7 / 10 : ℝ) ≤ 1 / Real.sqrt 2 := mnrs_sqrt_numeric.1
        have hπ8 : π / 8 ≤ 63 / 160 := by
          have hπle : π ≤ 63 / 20 := by
            rw [show (63 : ℝ) / 20 = 3.15 from by norm_num]
            exact Real.pi_lt_d2.le
          linarith
        linarith [hkey, h710, hπ8]
      have hXnn : 0 ≤ 5 / 17 - 3 * γ := by
        have hγ' : 3 * γ ≤ 3 * (1 / 40) := by nlinarith [hγ1]
        have hc : 5 / 17 - 3 * (1 / 40) = 149 / 680 := by norm_num
        linarith
      have hmass : markedMass Mr ((raaUnitary unmarkRefl R t)
          (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1))) =
          ‖markProj Mr ((raaUnitary unmarkRefl R t)
            (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1)))‖ ^ 2 := rfl
      have hsq : (5 / 17 - 3 * γ) ^ 2 ≤ markedMass Mr ((raaUnitary unmarkRefl R t)
          (attemptState Mr (raaUnitary unmarkRefl R) x₀ (t - 1))) := by
        rw [hmass]
        exact (sq_le_sq₀ hXnn (norm_nonneg _)).mpr hX
      have hfin : 1 / 12 - 3 * γ ≤ (5 / 17 - 3 * γ) ^ 2 := by
        have hexp : (5 / 17 - 3 * γ) ^ 2 = 25 / 289 - (30 / 17) * γ + 9 * γ ^ 2 := by ring
        have hc : (25 : ℝ) / 289 - 1 / 12 = 11 / 3468 := by norm_num
        rw [hexp]
        linarith [hγ0.le, sq_nonneg γ, hc]
      exact hfin.trans (hsq.trans (mnrs_tolerant_success_ge_attempt Mr
        (raaUnitary unmarkRefl R) x₀ (by rw [hx₀]) (Nat.max tMax 1) t
        (Finset.mem_Icc.mpr ⟨ht0pos, htle.trans (Nat.le_max_left tMax 1)⟩)))
  · exact mnrs_tolerant_attempt_cost_bound γ c₁ c₂ hγ0 (hγ1.trans (by norm_num)) hc₁ hc₂
      costR costMark tMax hcost hmark

end Qatlib.Concepts.WalkSearch.MnrsAmplify
