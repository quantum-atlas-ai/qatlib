/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabEquiv04.MainResults.Model.AdiabaticDefs
import Qatlib.Papers.AdiabEquiv04.MainResults.Model.EigenRayleigh
import Qatlib.Papers.AdiabEquiv04.MainResults.Model.SpectralBasics
import Qatlib.Papers.AdiabEquiv04.MainResults.Perturbation.SpectralPerturbation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.AdiabEquiv04.MainResults.Perturbation

open Qatlib.Papers.AdiabEquiv04.MainResults.Model

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

theorem dotProduct_star_swap' {κ : Type} [Fintype κ] (a b : κ → ℂ) :
    (star b) ⬝ᵥ a = star ((star a) ⬝ᵥ b) := by
  rw [dotProduct, dotProduct, star_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.star_apply, star_mul, star_star]

theorem herm_dot_swap {κ : Type} [Fintype κ] {M : Matrix κ κ ℂ} (hM : M.IsHermitian)
    (x y : κ → ℂ) :
    (star x) ⬝ᵥ (M *ᵥ y) = (star (M *ᵥ x)) ⬝ᵥ y := by
  have h := dotProduct_star_mulVec_left M x y
  rwa [hM.eq] at h

theorem normSq_smul_complex {κ : Type} [Fintype κ] (c : ℂ) (ψ : κ → ℂ) :
    (∑ i, Complex.normSq ((c • ψ) i)) = Complex.normSq c * ∑ i, Complex.normSq (ψ i) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Complex.normSq_mul]

theorem rayleigh_smul_complex {κ : Type} [Fintype κ] (c : ℂ) (M : Matrix κ κ ℂ)
    (ψ : κ → ℂ) :
    ((star (c • ψ)) ⬝ᵥ (M *ᵥ (c • ψ))).re =
      Complex.normSq c * ((star ψ) ⬝ᵥ (M *ᵥ ψ)).re := by
  have h1 : (star (c • ψ)) = (star c) • star ψ := by
    ext i
    simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul]
    ring
  rw [h1, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul]
  have hc : star c * c = ((Complex.normSq c : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [hc, smul_eq_mul, Complex.mul_re]
  simp

theorem normSq_nonneg_aux {κ : Type} [Fintype κ] (ψ : κ → ℂ) :
    0 ≤ normSq ψ :=
  Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (ψ i))

theorem normSq_pos_aux {κ : Type} [Fintype κ] {ψ : κ → ℂ} (h : ψ ≠ 0) :
    0 < normSq ψ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  have hnonneg : ∀ j ∈ (Finset.univ : Finset κ), 0 ≤ Complex.normSq (ψ j) :=
    fun j _ => Complex.normSq_nonneg (ψ j)
  have hlt : 0 < Complex.normSq (ψ i) := by rwa [Complex.normSq_pos]
  have hle : Complex.normSq (ψ i) ≤ normSq ψ :=
    Finset.single_le_sum hnonneg (Finset.mem_univ i)
  linarith

theorem normSq_add_of_orth {κ : Type} [Fintype κ] {a b : κ → ℂ}
    (hab : (star a) ⬝ᵥ b = 0) :
    normSq (a + b) = normSq a + normSq b := by
  show (∑ i, Complex.normSq ((a + b) i)) =
      (∑ i, Complex.normSq (a i)) + ∑ i, Complex.normSq (b i)
  rw [normSq_eq_re_dotProduct (ι := κ) (a + b), normSq_eq_re_dotProduct (ι := κ) a,
    normSq_eq_re_dotProduct (ι := κ) b]
  have hexp : (star (a + b)) ⬝ᵥ (a + b) =
      ((star a) ⬝ᵥ a) + ((star a) ⬝ᵥ b) + ((star b) ⬝ᵥ a) + ((star b) ⬝ᵥ b) := by
    rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add]
    abel
  have hba : (star b) ⬝ᵥ a = star ((star a) ⬝ᵥ b) := dotProduct_star_swap' a b
  rw [hexp, hba, hab, star_zero]
  simp only [Complex.add_re, Complex.zero_re]
  ring

def unitVec {κ : Type} [Fintype κ] [DecidableEq κ] (y : κ → ℂ) : κ → ℂ :=
  ((Real.sqrt (normSq y) : ℝ) : ℂ)⁻¹ • y

theorem normSq_unitVec {κ : Type} [Fintype κ] [DecidableEq κ] {y : κ → ℂ} (hy : y ≠ 0) :
    normSq (unitVec y) = 1 := by
  unfold unitVec normSq
  rw [normSq_smul_complex]
  have hS : 0 ≤ ∑ i, Complex.normSq (y i) := normSq_nonneg_aux y
  have hc : Complex.normSq (((Real.sqrt (∑ i, Complex.normSq (y i)) : ℝ) : ℂ)⁻¹) =
      (∑ i, Complex.normSq (y i))⁻¹ := by
    rw [show (((Real.sqrt (∑ i, Complex.normSq (y i)) : ℝ) : ℂ)⁻¹) =
      (((Real.sqrt (∑ i, Complex.normSq (y i)))⁻¹ : ℝ) : ℂ) from (Complex.ofReal_inv _).symm]
    rw [Complex.normSq_ofReal, ← _root_.mul_inv_rev]
    congr 1
    exact Real.mul_self_sqrt hS
  rw [hc]
  exact inv_mul_cancel₀ (ne_of_gt (normSq_pos_aux hy))

theorem rayleigh_unitVec {κ : Type} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℂ)
    {y : κ → ℂ} (hy : y ≠ 0) :
    rayleigh M y = normSq y * rayleigh M (unitVec y) := by
  have hpos : 0 < normSq y := normSq_pos_aux hy
  have hc0 : ((Real.sqrt (normSq y) : ℝ) : ℂ) ≠ 0 := by
    have h0 : (0:ℝ) < Real.sqrt (normSq y) := Real.sqrt_pos.mpr hpos
    exact_mod_cast ne_of_gt h0
  have hdecomp : ((Real.sqrt (normSq y) : ℝ) : ℂ) • unitVec y = y := by
    unfold unitVec
    rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hstep : rayleigh M (((Real.sqrt (normSq y) : ℝ) : ℂ) • unitVec y) = rayleigh M y := by
    rw [hdecomp]
  rw [← hstep]
  unfold rayleigh
  rw [rayleigh_smul_complex]
  congr 1
  rw [Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (le_of_lt hpos)]

theorem rayleigh_abs_le {κ : Type} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℂ) {K : ℝ}
    (hK : ∀ φ : κ → ℂ, IsNormalized φ → |rayleigh M φ| ≤ K) (y : κ → ℂ) :
    |rayleigh M y| ≤ K * normSq y := by
  by_cases hy : y = 0
  · subst hy
    simp [rayleigh, normSq, Matrix.mulVec_zero, dotProduct_zero, zero_dotProduct]
  · calc |rayleigh M y| = |normSq y * rayleigh M (unitVec y)| := by
          rw [rayleigh_unitVec M hy]
      _ = normSq y * |rayleigh M (unitVec y)| := by
          rw [abs_mul, abs_of_nonneg (normSq_nonneg_aux y)]
      _ ≤ normSq y * K :=
          mul_le_mul_of_nonneg_left (hK (unitVec y) (normSq_unitVec hy)) (normSq_nonneg_aux y)
      _ = K * normSq y := mul_comm _ _

theorem rayleigh_range_ge_ground {κ ν : Type} [Fintype κ] [DecidableEq κ]
    [Fintype ν] [DecidableEq ν]
    (V : Matrix κ ν ℂ) (hV : Vᴴ * V = 1) (H₁ : Hamiltonian κ) (hν : 0 < Fintype.card ν)
    (c : ν → ℂ) :
    normSq (V *ᵥ c) * groundEnergy (restrict V H₁ hV) hν ≤ rayleigh H₁.mat (V *ᵥ c) := by
  rw [← rayleigh_isometry V hV H₁ c, normSq_isometry V hV c]
  by_cases hc : c = 0
  · subst hc
    simp [rayleigh, normSq, Matrix.mulVec_zero, dotProduct_zero, zero_dotProduct]
  · have hpos : 0 < normSq c := normSq_pos_aux hc
    rw [rayleigh_unitVec (restrict V H₁ hV).mat hc]
    exact mul_le_mul_of_nonneg_left
      (groundEnergy_le_rayleigh (restrict V H₁ hV) hν (unitVec c) (normSq_unitVec hc))
      (le_of_lt hpos)

theorem rayleigh_H2_ge {κ ν : Type} [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (H₂ : Hamiltonian κ) (V : Matrix κ ν ℂ) (J : ℝ)
    (hpos : ∀ ψ : κ → ℂ, IsNormalized ψ → Vᴴ *ᵥ ψ = 0 → J ≤ rayleigh H₂.mat ψ)
    {y : κ → ℂ} (hVy : Vᴴ *ᵥ y = 0) :
    J * normSq y ≤ rayleigh H₂.mat y := by
  by_cases hy : y = 0
  · subst hy
    simp [rayleigh, normSq, Matrix.mulVec_zero, dotProduct_zero, zero_dotProduct]
  · have hposy : 0 < normSq y := normSq_pos_aux hy
    have hVyu : Vᴴ *ᵥ unitVec y = 0 := by
      unfold unitVec
      rw [mulVec_smul, hVy, smul_zero]
    have hJ : J ≤ rayleigh H₂.mat (unitVec y) :=
      hpos (unitVec y) (normSq_unitVec hy) hVyu
    have h1 : J * normSq y ≤ rayleigh H₂.mat (unitVec y) * normSq y :=
      mul_le_mul_of_nonneg_right hJ (le_of_lt hposy)
    have h2 : rayleigh H₂.mat (unitVec y) * normSq y =
        normSq y * rayleigh H₂.mat (unitVec y) := mul_comm _ _
    rw [rayleigh_unitVec H₂.mat hy]
    linarith [h1, h2]

theorem quad_min (A K t : ℝ) (hA : 0 < A) :
    -(K ^ 2 / A) ≤ A * t ^ 2 - 2 * K * t := by
  have h1 : 0 ≤ (A * t - K) ^ 2 := sq_nonneg _
  have h2 : A * (A * t ^ 2 - 2 * K * t) = (A * t - K) ^ 2 - K ^ 2 := by ring
  rw [← neg_div, div_le_iff₀ hA]
  nlinarith [h1, h2]

theorem core_bound (gS J K u s ux sy : ℝ)
    (hux : ux ^ 2 = u) (hsy : sy ^ 2 = s) (hu : u + s = 1)
    (hu0 : 0 ≤ u) (hs0 : 0 ≤ s) (hux0 : 0 ≤ ux) (hsy0 : 0 ≤ sy)
    (hK0 : 0 ≤ K) (hgSK : gS ≤ K) (hJ : 2 * K < J) :
    gS - K ^ 2 / (J - 2 * K) ≤ u * gS - K * s - 2 * K * ux * sy + J * s := by
  have hA : 0 < J - 2 * K := by linarith
  have hux1 : ux ≤ 1 := by nlinarith [hux, hux0, hu0, hu, hs0]
  have hq : -(K ^ 2 / (J - 2 * K)) ≤ (J - 2 * K) * sy ^ 2 - 2 * K * sy :=
    quad_min (J - 2 * K) K sy hA
  have h1 : (J - 2 * K) * s ≤ (J - K - gS) * s := by
    have hJK : J - 2 * K ≤ J - K - gS := by linarith
    exact mul_le_mul_of_nonneg_right hJK hs0
  have huxsy : ux * sy ≤ sy := by
    have := mul_le_mul_of_nonneg_right hux1 hsy0
    simpa using this
  have h2 : -2 * K * sy ≤ -2 * K * ux * sy := by
    have h3 : (0:ℝ) ≤ 2 * K := by linarith
    have := mul_le_mul_of_nonneg_left huxsy h3
    nlinarith [this]
  have hsa : 0 ≤ (J - 2 * K) * s - 2 * K * sy + K ^ 2 / (J - 2 * K) := by
    rw [← hsy]
    linarith [hq]
  have stepA : 0 ≤ s * (J - K - gS) - 2 * K * ux * sy + K ^ 2 / (J - 2 * K) := by
    nlinarith [hsa, h1, h2]
  nlinarith [stepA, hu, hu0, hs0]

theorem rayleigh_add_orth {κ : Type} [Fintype κ] {M : Matrix κ κ ℂ} (hM : M.IsHermitian)
    {x y : κ → ℂ} (hxy : (star x) ⬝ᵥ y = 0) :
    rayleigh M (x + y) =
      rayleigh M x + rayleigh M y + 2 * ((star x) ⬝ᵥ (M *ᵥ y)).re := by
  unfold rayleigh
  have hexp : (star (x + y)) ⬝ᵥ (M *ᵥ (x + y)) =
      ((star x) ⬝ᵥ (M *ᵥ x)) + ((star x) ⬝ᵥ (M *ᵥ y))
        + ((star y) ⬝ᵥ (M *ᵥ x)) + ((star y) ⬝ᵥ (M *ᵥ y)) := by
    rw [Matrix.mulVec_add, star_add, add_dotProduct, dotProduct_add, dotProduct_add]
    abel
  have hcross : ((star y) ⬝ᵥ (M *ᵥ x)) = star ((star x) ⬝ᵥ (M *ᵥ y)) := by
    rw [herm_dot_swap hM y x, dotProduct_star_swap' x (M *ᵥ y)]
  rw [hexp, hcross]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

theorem lemma_3_17_ground_lower
    (V : Matrix ι σ ℂ) (hV : Vᴴ * V = 1)
    (H₁ H₂ : Hamiltonian ι) (J K : ℝ) (hJ : 2 * K < J) (hK0 : 0 ≤ K)
    (hcardS : 0 < Fintype.card σ) (hcard : 0 < Fintype.card ι)
    (hvan : ∀ a : Vector σ, H₂.mat *ᵥ (V *ᵥ a) = 0)
    (hpos : ∀ ψ : Vector ι, IsNormalized ψ → Vᴴ *ᵥ ψ = 0 → J ≤ rayleigh H₂.mat ψ)
    (hKoff : ∀ x y : Vector ι,
      |((star x) ⬝ᵥ (H₁.mat *ᵥ y)).re| ≤ K * Real.sqrt (normSq x) * Real.sqrt (normSq y)) :
    groundEnergy (H₁.add H₂) hcard ≥
      groundEnergy (restrict V H₁ hV) hcardS - K ^ 2 / (J - 2 * K) := by
  set gS : ℝ := groundEnergy (restrict V H₁ hV) hcardS with hgS
  have hKunit : ∀ φ : Vector ι, IsNormalized φ → |rayleigh H₁.mat φ| ≤ K := by
    intro φ hφ
    show |((star φ) ⬝ᵥ (H₁.mat *ᵥ φ)).re| ≤ K
    have hφ' : normSq φ = 1 := hφ
    have h := hKoff φ φ
    simp only [hφ', Real.sqrt_one, mul_one] at h
    exact h
  suffices hmain : ∀ v : Vector ι, IsNormalized v →
      gS - K ^ 2 / (J - 2 * K) ≤ rayleigh (H₁.add H₂).mat v by
    obtain ⟨v₀, hv₀⟩ := exists_groundVec (H₁.add H₂) hcard
    have h := hmain v₀ hv₀.1
    rwa [rayleigh_of_groundVector (H₁.add H₂) hcard v₀ hv₀] at h
  intro v hv
  set c : Vector σ := Vᴴ *ᵥ v with hc
  set x : Vector ι := V *ᵥ c with hx
  set y : Vector ι := v - x with hy
  have hVx : Vᴴ *ᵥ x = c := by rw [hx, isometry_mulVec_mulVec V hV]
  have hVy : Vᴴ *ᵥ y = 0 := by
    rw [hy, Matrix.mulVec_sub, hVx, hc, sub_self]
  have hvxy : v = x + y := by rw [hy]; abel
  have hxy : (star x) ⬝ᵥ y = 0 := by
    rw [hx, ← dotProduct_star_mulVec_left V c y, hVy]
    simp
  have hnorm_add : normSq v = normSq x + normSq y := by
    rw [hvxy, normSq_add_of_orth hxy]
  have hus : normSq x + normSq y = 1 := by rw [← hnorm_add]; exact hv
  have h1x : normSq x * gS ≤ rayleigh H₁.mat x := by
    rw [hx]
    exact rayleigh_range_ge_ground V hV H₁ hcardS c
  have hy_abs := rayleigh_abs_le H₁.mat hKunit y
  have h1y : -K * normSq y ≤ rayleigh H₁.mat y := by
    have h2 := neg_abs_le (rayleigh H₁.mat y)
    linarith
  have hcross : -2 * K * Real.sqrt (normSq x) * Real.sqrt (normSq y) ≤
      2 * ((star x) ⬝ᵥ (H₁.mat *ᵥ y)).re := by
    have h := (abs_le.mp (hKoff x y)).1
    linarith
  have h2y : J * normSq y ≤ rayleigh H₂.mat y := rayleigh_H2_ge H₂ V J hpos hVy
  have hH2xvec : H₂.mat *ᵥ x = 0 := by rw [hx]; exact hvan c
  have hH2x : rayleigh H₂.mat x = 0 := by
    unfold rayleigh
    rw [hH2xvec, dotProduct_zero, Complex.zero_re]
  have hH2cross : ((star x) ⬝ᵥ (H₂.mat *ᵥ y)).re = 0 := by
    rw [herm_dot_swap H₂.herm x y, hH2xvec]
    simp
  have hH2v : rayleigh H₂.mat v = rayleigh H₂.mat y := by
    rw [hvxy, rayleigh_add_orth H₂.herm hxy, hH2x, hH2cross]
    ring
  have hH1v : rayleigh H₁.mat v =
      rayleigh H₁.mat x + rayleigh H₁.mat y + 2 * ((star x) ⬝ᵥ (H₁.mat *ᵥ y)).re := by
    rw [hvxy]; exact rayleigh_add_orth H₁.herm hxy
  have hgSK : gS ≤ K := by
    obtain ⟨ξ₀, hξ₀⟩ := exists_groundVec (restrict V H₁ hV) hcardS
    have hle : gS ≤ rayleigh (restrict V H₁ hV).mat ξ₀ :=
      groundEnergy_le_rayleigh (restrict V H₁ hV) hcardS ξ₀ hξ₀.1
    have hKabs : |rayleigh (restrict V H₁ hV).mat ξ₀| ≤ K := by
      have hnorm : IsNormalized (V *ᵥ ξ₀) := by
        show normSq (V *ᵥ ξ₀) = 1
        rw [normSq_isometry V hV]
        exact hξ₀.1
      have hk := hKunit (V *ᵥ ξ₀) hnorm
      rwa [← rayleigh_isometry V hV H₁ ξ₀] at hk
    have hle2 : rayleigh (restrict V H₁ hV).mat ξ₀ ≤ K :=
      le_trans (le_abs_self _) hKabs
    linarith
  have hsum : rayleigh (H₁.add H₂).mat v = rayleigh H₁.mat v + rayleigh H₂.mat v := by
    rw [show (H₁.add H₂).mat = H₁.mat + H₂.mat from rfl, rayleigh_add]
  rw [hsum, hH1v, hH2v]
  have key := core_bound gS J K (normSq x) (normSq y) (Real.sqrt (normSq x)) (Real.sqrt (normSq y))
    (Real.sq_sqrt (normSq_nonneg_aux x)) (Real.sq_sqrt (normSq_nonneg_aux y)) hus
    (normSq_nonneg_aux x) (normSq_nonneg_aux y) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hK0 hgSK hJ
  linarith [key, h1x, h1y, hcross, h2y]

end Qatlib.Papers.AdiabEquiv04.MainResults.Perturbation
