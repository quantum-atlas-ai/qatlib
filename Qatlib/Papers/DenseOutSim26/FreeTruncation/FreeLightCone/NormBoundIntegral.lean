/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DenseOutSim26.FreeTruncation.Core.DenseOutput

/-!
# Lemma 1: norm bound via the shell-sum integral (arXiv:2609.40094v1, p.11)

The paper evaluates the shell sum of a power-law Hamiltonian as
`‖H‖ ≈ J₀ ω_D ∫₁^L r^{D−1−α} dr` (Eq. (23)) and obtains the three regimes of
Eq. (24):

* `α > D`:  `(J₀ω_D/(α−D)) (1 − L^{−(α−D)})`, converging to the finite `S_∞`;
* `α = D`:  `J₀ω_D log L`;
* `α < D`:  `(J₀ω_D/(D−α)) (L^{D−α} − 1) = Θ(L^{D−α})`.

The three integral identities below are the exact content of Eq. (24); the final
`IsTheta` statement records the `Θ(L^{D−α})` growth of the last regime.
-/

namespace Qatlib.Papers.DenseOutSim26.FreeTruncation.FreeLightCone

open MeasureTheory intervalIntegral
open Qatlib.Papers.DenseOutSim26.FreeTruncation.Core

set_option autoImplicit false

/-- Lemma 1, Eq. (24), regime `α > D`: the shell-sum norm equals
`(J₀ω_D/(α−D)) (1 − L^{−(α−D)})`, which converges to
`S_∞ = J₀ω_D/(α−D)` as `L → ∞`. -/
theorem lemma1_shellSumNorm_alpha_gt_D
    {J0 ωD D α L : ℝ} (hL : 1 ≤ L) (h : D < α) :
    shellSumNorm J0 ωD D α L
      = J0 * ωD / (α - D) * (1 - L ^ (-(α - D))) := by
  unfold shellSumNorm
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  have hz : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) L := by
    rw [Set.uIcc_of_le hL]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h1
    linarith
  have hne : D - 1 - α ≠ -1 := by intro hh; linarith
  have hint : ∫ r in (1 : ℝ)..L, r ^ (D - 1 - α) = (L ^ (D - α) - 1) / (D - α) := by
    have hh := integral_rpow (a := (1 : ℝ)) (b := L) (r := D - 1 - α)
      (Or.inr ⟨hne, hz⟩)
    rw [show D - 1 - α + 1 = D - α by ring, Real.one_rpow] at hh
    simpa using hh
  rw [hint]
  have hpow : L ^ (D - α) = L ^ (-(α - D)) := by
    rw [show D - α = -(α - D) by ring]
  rw [hpow]
  have hden : α - D ≠ 0 := by linarith
  have hden2 : D - α ≠ 0 := by linarith
  field_simp
  ring

/-- Lemma 1, Eq. (24), regime `α = D`: the shell-sum norm equals `J₀ω_D log L`. -/
theorem lemma1_shellSumNorm_alpha_eq_D
    {J0 ωD D α L : ℝ} (hL : 1 ≤ L) (h : α = D) :
    shellSumNorm J0 ωD D α L = J0 * ωD * Real.log L := by
  unfold shellSumNorm
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  rw [h]
  have hfun : (fun r : ℝ => r ^ (D - 1 - D)) = fun r : ℝ => r⁻¹ := by
    funext r
    rw [show D - 1 - D = -1 by ring, Real.rpow_neg_one]
  rw [hfun, integral_inv_of_pos one_pos hL0, div_one]

/-- Lemma 1, Eq. (24), regime `α < D`: the shell-sum norm equals
`J₀ω_D (L^{D−α} − 1)/(D−α)`. -/
theorem lemma1_shellSumNorm_alpha_lt_D
    {J0 ωD D α L : ℝ} (hL : 1 ≤ L) (h : α < D) :
    shellSumNorm J0 ωD D α L
      = J0 * ωD * ((L ^ (D - α) - 1) / (D - α)) := by
  unfold shellSumNorm
  have hz : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) L := by
    rw [Set.uIcc_of_le hL]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h1
    linarith
  have hne : D - 1 - α ≠ -1 := by intro hh; linarith
  have hint : ∫ r in (1 : ℝ)..L, r ^ (D - 1 - α) = (L ^ (D - α) - 1) / (D - α) := by
    have hh := integral_rpow (a := (1 : ℝ)) (b := L) (r := D - 1 - α)
      (Or.inr ⟨hne, hz⟩)
    rw [show D - 1 - α + 1 = D - α by ring, Real.one_rpow] at hh
    simpa using hh
  rw [hint]

/-- Lemma 1, Eq. (24), regime `α > D`: the truncated shell-sum norm is
uniformly bounded by the infinite-lattice value `S_∞ = J₀ω_D/(α−D)`, hence
`‖H‖ = O(1)` in `L`.  (This is the `Θ(1)` norm input of Theorem 2.) -/
theorem lemma1_shellSumNorm_le_Sinf
    {J0 ωD D α L : ℝ} (hJ : 0 ≤ J0) (hω : 0 ≤ ωD) (hL : 1 ≤ L) (h : D < α) :
    shellSumNorm J0 ωD D α L ≤ J0 * ωD / (α - D) := by
  rw [lemma1_shellSumNorm_alpha_gt_D hL h]
  have hden : 0 < α - D := by linarith
  have hpow : 0 ≤ L ^ (-(α - D)) := Real.rpow_nonneg (by linarith) _
  have hcoef : 0 ≤ J0 * ωD / (α - D) :=
    div_nonneg (mul_nonneg hJ hω) hden.le
  nlinarith

/-- Lemma 1, Eq. (24), regime `α < D`: the shell-sum norm grows like
`L^{D−α}`, i.e. it is `Θ(L^{D−α})` as `L → ∞` (with `J₀ω_D ≠ 0`). -/
theorem lemma1_shellSumNorm_alpha_lt_D_isTheta
    {J0 ωD D α : ℝ} (hJ : J0 ≠ 0) (hω : ωD ≠ 0) (h : α < D) :
    Asymptotics.IsTheta Filter.atTop (fun L : ℝ => shellSumNorm J0 ωD D α L)
      (fun L : ℝ => L ^ (D - α)) := by
  have hp : 0 < D - α := by linarith
  have hc : J0 * ωD ≠ 0 := mul_ne_zero hJ hω
  have hcpos : 0 < |J0 * ωD| := abs_pos.mpr hc
  have heq : ∀ᶠ L : ℝ in Filter.atTop,
      shellSumNorm J0 ωD D α L = J0 * ωD * ((L ^ (D - α) - 1) / (D - α)) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with L hL
    rw [lemma1_shellSumNorm_alpha_lt_D hL h]
  constructor
  · -- shell-sum ≤ C · L^{D−α}
    refine Asymptotics.IsBigO.of_bound (|J0 * ωD| / (D - α)) ?_
    filter_upwards [heq, Filter.eventually_ge_atTop (1 : ℝ)] with L he hL
    rw [he]
    have hLp : (1 : ℝ) ≤ L ^ (D - α) := Real.one_le_rpow hL hp.le
    have hnum0 : 0 ≤ L ^ (D - α) - 1 := by linarith
    have hnum_le : L ^ (D - α) - 1 ≤ L ^ (D - α) := by linarith
    have hquot : (L ^ (D - α) - 1) / (D - α) ≤ L ^ (D - α) / (D - α) := by
      apply div_le_div_of_nonneg_right hnum_le hp.le
    have hquot0 : 0 ≤ (L ^ (D - α) - 1) / (D - α) := div_nonneg hnum0 hp.le
    have hnormeq : ‖J0 * ωD * ((L ^ (D - α) - 1) / (D - α))‖
        = |J0 * ωD| * ((L ^ (D - α) - 1) / (D - α)) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hquot0]
    rw [hnormeq, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    calc |J0 * ωD| * ((L ^ (D - α) - 1) / (D - α))
        ≤ |J0 * ωD| * (L ^ (D - α) / (D - α)) := by
          exact mul_le_mul_of_nonneg_left hquot hcpos.le
      _ = |J0 * ωD| / (D - α) * L ^ (D - α) := by ring
  · -- L^{D−α} ≤ C · shell-sum
    obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → 2 ≤ L ^ (D - α) :=
      Filter.eventually_atTop.1
        ((tendsto_rpow_atTop hp).eventually (Filter.eventually_ge_atTop 2))
    refine Asymptotics.IsBigO.of_bound (2 * (D - α) / |J0 * ωD|) ?_
    filter_upwards [heq, Filter.eventually_ge_atTop (max L₀ 1)] with L he hL
    have hL1 : (1 : ℝ) ≤ L := le_trans (le_max_right _ _) hL
    have hL2 : L₀ ≤ L := le_trans (le_max_left _ _) hL
    have hbig : (2 : ℝ) ≤ L ^ (D - α) := hL₀ L hL2
    rw [he]
    have hquot0 : 0 ≤ (L ^ (D - α) - 1) / (D - α) := by
      apply div_nonneg _ hp.le
      linarith
    have hquot : L ^ (D - α) / 2 ≤ (L ^ (D - α) - 1) / (D - α) * (D - α) := by
      rw [div_mul_cancel₀ _ hp.ne']
      linarith
    have hlow : L ^ (D - α) ≤ 2 * ((L ^ (D - α) - 1) / (D - α)) * (D - α) := by
      nlinarith [hquot]
    have hnormeq : ‖J0 * ωD * ((L ^ (D - α) - 1) / (D - α))‖
        = |J0 * ωD| * ((L ^ (D - α) - 1) / (D - α)) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hquot0]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _), hnormeq]
    calc L ^ (D - α)
        ≤ 2 * ((L ^ (D - α) - 1) / (D - α)) * (D - α) := hlow
      _ = 2 * (D - α) / |J0 * ωD| *
            (|J0 * ωD| * ((L ^ (D - α) - 1) / (D - α))) := by
          field_simp

end Qatlib.Papers.DenseOutSim26.FreeTruncation.FreeLightCone
