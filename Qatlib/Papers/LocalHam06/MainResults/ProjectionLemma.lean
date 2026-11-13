/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocalHam06.MainResults.OperatorDefs

/-!
# The projection lemma for ground energy

The theorem `projection_lemma` gives the two-sided ground-energy estimate of Lemma 1 in
[KempeKitaevRegev2006]. A symmetric penalty vanishing on a nonzero subspace and bounded below by
`J` on its orthogonal complement confines the total ground energy to an interval around the
section energy of the other summand.

## Main statements

* `projection_lemma`: Bounds the ground energy between the section energy and that energy minus
  `‖H1‖^2 / (J - 2 * ‖H1‖)`.

## References

* [Kempe et al., 2006][KempeKitaevRegev2006]
-/

noncomputable section

open scoped ComplexOrder
open InnerProductSpace

namespace Qatlib.Papers.LocalHam06.MainResults.ProjectionLemma

open Qatlib.Papers.LocalHam06.MainResults.OperatorDefs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Nontrivial E]

set_option maxHeartbeats 400000 in

/-- Under the stated symmetry, kernel, and penalty-gap hypotheses with `J > 2 * ‖H1‖`, the
ground energy of `H1 + H2` lies between `sectionEnergy S H1 - ‖H1‖^2 / (J - 2 * ‖H1‖)` and
`sectionEnergy S H1`. This is the projection lemma of [KempeKitaevRegev2006]. -/
theorem projection_lemma
    (S : Submodule ℂ E) (H1 H2 : E →L[ℂ] E) (J : ℝ)
    (hH1 : (H1 : E →ₗ[ℂ] E).IsSymmetric)
    (hH2 : (H2 : E →ₗ[ℂ] E).IsSymmetric)
    (hS : S ≠ ⊥)
    (hJ : 2 * ‖H1‖ < J)
    (hH2zero : ∀ v ∈ S, H2 v = 0)
    (hgap : ∀ v ∈ Sᗮ, J * ‖v‖ ^ 2 ≤ rayleigh H2 v) :
    sectionEnergy S H1 - ‖H1‖ ^ 2 / (J - 2 * ‖H1‖) ≤ groundEnergy (H1 + H2) ∧
      groundEnergy (H1 + H2) ≤ sectionEnergy S H1 := by
  set K : ℝ := ‖H1‖ with hK
  have hKnonneg : 0 ≤ K := by rw [hK]; exact norm_nonneg H1
  have hden : 0 < J - 2 * K := by rw [hK]; linarith

  have hupper : groundEnergy (H1 + H2) ≤ sectionEnergy S H1 := by
    rw [groundEnergy, sectionEnergy]
    refine (le_csInf_iff (bddBelow_sectionSet S H1)
      (sectionSet_nonempty S H1 hS)).2 ?_
    rintro y ⟨w, ⟨hw1, hwS⟩, rfl⟩
    have hH2w : H2 w = 0 := hH2zero w hwS
    have hval : rayleigh (H1 + H2) w = rayleigh H1 w := by
      unfold rayleigh
      rw [ContinuousLinearMap.add_apply, hH2w, add_zero]
    exact le_trans (csInf_le (bddBelow_rect (H1 + H2)) ⟨w, hw1, rfl⟩) (le_of_eq hval)
  refine ⟨?_, hupper⟩

  rw [groundEnergy]
  refine (le_csInf_iff (bddBelow_rect (H1 + H2)) (rect_nonempty (H1 + H2))).2 ?_
  rintro y ⟨v, hv, rfl⟩
  set p : E := S.starProjection v with hp_def
  set q : E := v - p with hq_def
  have hpS : p ∈ S := S.starProjection_apply_mem v
  have hqS : q ∈ Sᗮ := S.sub_starProjection_mem_orthogonal v
  have hvpq : v = p + q := by
    rw [hq_def]
    exact (add_sub_cancel p v).symm
  have horth : ⟪p, q⟫_ℂ = 0 := (S.mem_orthogonal q).1 hqS p hpS
  have hnorm_split : ‖v‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
    have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p q horth
    rw [hvpq]
    simpa [pow_two] using hsq
  have hH2p : H2 p = 0 := hH2zero p hpS

  have hH2q_mem : H2 q ∈ Sᗮ := by
    rw [S.mem_orthogonal]
    intro u hu
    rw [← hH2.apply_clm u q, hH2zero u hu, inner_zero_left]
  have hp2q : ⟪p, H2 q⟫_ℂ = 0 := (S.mem_orthogonal (H2 q)).1 hH2q_mem p hpS
  have hHval : (H1 + H2) (p + q) = H1 p + H1 q + H2 q := by
    simp only [map_add, ContinuousLinearMap.add_apply, hH2p, add_zero]
    abel
  have hval : rayleigh (H1 + H2) v =
      rayleigh H1 p + (inner ℂ p (H1 q)).re + (inner ℂ q (H1 p)).re
        + rayleigh H1 q + rayleigh H2 q := by
    unfold rayleigh
    rw [hvpq, hHval]
    simp only [inner_add_left, inner_add_right, Complex.add_re, hp2q, Complex.zero_re]
    ring
  by_cases hp0 : p = 0
  · have hvq : v = q := by rw [hvpq, hp0, zero_add]
    have hqunit : ‖q‖ = 1 := by rw [← hvq]; exact hv
    have hq1 : ‖q‖ ^ 2 = 1 := by rw [hqunit]; norm_num
    have hH2q : J * ‖q‖ ^ 2 ≤ rayleigh H2 q := hgap q hqS
    have hH1q : -(K * ‖q‖ ^ 2) ≤ rayleigh H1 q := by
      simpa [← hK] using rayleigh_neg_le H1 q
    have hH1q' : -K ≤ rayleigh H1 q := by nlinarith [hH1q, hq1]
    have hH2q' : J ≤ rayleigh H2 q := by nlinarith [hH2q, hq1]
    have hsec : sectionEnergy S H1 ≤ K := by
      simpa [← hK] using sectionEnergy_le_norm S H1 hS
    have hvalq : rayleigh (H1 + H2) v = rayleigh H1 q + rayleigh H2 q := by
      rw [hvq]
      unfold rayleigh
      rw [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    rw [hvalq]
    have hnonneg : 0 ≤ K ^ 2 / (J - 2 * K) := div_nonneg (sq_nonneg K) (le_of_lt hden)
    nlinarith [hH1q', hH2q', hsec, hnonneg, hden, hKnonneg]
  · have hp_pos : 0 < ‖p‖ := norm_pos_iff.mpr hp0
    set a : ℝ := ‖p‖ with ha_def
    set b : ℝ := ‖q‖ with hb_def
    have ha : 0 < a := by rw [ha_def]; exact hp_pos
    have hb : 0 ≤ b := by rw [hb_def]; exact norm_nonneg q
    have hnorm_ab : a ^ 2 + b ^ 2 = 1 := by
      rw [ha_def, hb_def, ← hnorm_split, hv]
      norm_num
    have ha2le : a ^ 2 ≤ 1 := by nlinarith [hnorm_ab, sq_nonneg b]
    have ha1 : a ≤ 1 := (sq_le_one_iff₀ ha.le).mp ha2le

    have hv1unit : ‖a⁻¹ • p‖ = 1 := by
      have hnorm : ‖(a⁻¹ : ℝ)‖ = a⁻¹ := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
      rw [norm_smul, hnorm, ← ha_def, inv_mul_cancel₀ (ne_of_gt ha)]
    have hv1S : a⁻¹ • p ∈ S := S.smul_mem _ hpS
    have hdecomp : a • (a⁻¹ • p) = p := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt ha), one_smul]
    have hrp : rayleigh H1 p = a ^ 2 * rayleigh H1 (a⁻¹ • p) := by
      conv_lhs => rw [← hdecomp]
      rw [rayleigh_smul_real]
    have hcoef : a⁻¹ ^ 2 * a ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt ha), one_pow]
    have hsec_le_r1 : sectionEnergy S H1 ≤ rayleigh H1 (a⁻¹ • p) := by
      have hle := sectionEnergy_le_rayleigh S H1 hv1unit hv1S
      rw [rayleigh_smul_real, hrp] at hle
      calc
        sectionEnergy S H1 ≤ a⁻¹ ^ 2 * (a ^ 2 * rayleigh H1 (a⁻¹ • p)) := hle
        _ = rayleigh H1 (a⁻¹ • p) := by rw [← mul_assoc, hcoef, one_mul]
    have hr1_le : rayleigh H1 (a⁻¹ • p) ≤ K := by
      have h := rayleigh_le H1 (a⁻¹ • p)
      rw [hv1unit, one_pow, mul_one] at h
      simpa [← hK] using h
    have hkey : rayleigh H1 (a⁻¹ • p) - b ^ 2 * K ≤ rayleigh H1 p := by
      have hmul : b ^ 2 * rayleigh H1 (a⁻¹ • p) ≤ b ^ 2 * K :=
        mul_le_mul_of_nonneg_left hr1_le (sq_nonneg b)
      nlinarith [hrp, hnorm_ab, hmul]

    have hcross1 : -(K * a * b) ≤ (inner ℂ p (H1 q)).re := by
      have habs : |(inner ℂ p (H1 q)).re| ≤ K * a * b := by
        calc
          |(inner ℂ p (H1 q)).re| ≤ ‖inner ℂ p (H1 q)‖ := Complex.abs_re_le_norm _
          _ ≤ ‖p‖ * ‖H1 q‖ := norm_inner_le_norm p (H1 q)
          _ ≤ a * (K * b) := by
              have hq_le : ‖H1 q‖ ≤ K * b := by
                calc
                  ‖H1 q‖ ≤ ‖H1‖ * ‖q‖ := H1.le_opNorm q
                  _ = K * b := by rw [← hK, hb_def]
              rw [ha_def.symm]
              exact mul_le_mul_of_nonneg_left hq_le ha.le
          _ = K * a * b := by ring
      linarith [neg_abs_le (inner ℂ p (H1 q)).re]
    have hcross2 : -(K * a * b) ≤ (inner ℂ q (H1 p)).re := by
      have habs : |(inner ℂ q (H1 p)).re| ≤ K * a * b := by
        calc
          |(inner ℂ q (H1 p)).re| ≤ ‖inner ℂ q (H1 p)‖ := Complex.abs_re_le_norm _
          _ ≤ ‖q‖ * ‖H1 p‖ := norm_inner_le_norm q (H1 p)
          _ ≤ b * (K * a) := by
              have hp_le : ‖H1 p‖ ≤ K * a := by
                calc
                  ‖H1 p‖ ≤ ‖H1‖ * ‖p‖ := H1.le_opNorm p
                  _ = K * a := by rw [← hK, ha_def]
              rw [hb_def.symm]
              exact mul_le_mul_of_nonneg_left hp_le hb
          _ = K * a * b := by ring
      linarith [neg_abs_le (inner ℂ q (H1 p)).re]
    have hcross : -2 * K * a * b ≤
        (inner ℂ p (H1 q)).re + (inner ℂ q (H1 p)).re := by
      linarith [hcross1, hcross2]
    have hcross_b : -2 * K * b ≤ -2 * K * a * b := by
      have hab : a * b ≤ 1 * b := mul_le_mul_of_nonneg_right ha1 hb
      nlinarith [hab, hKnonneg, hb]
    have hH1q : -(K * b ^ 2) ≤ rayleigh H1 q := by
      have h := rayleigh_neg_le H1 q
      rw [← hb_def] at h
      simpa [← hK] using h
    have hH2q : J * b ^ 2 ≤ rayleigh H2 q := by
      have h := hgap q hqS
      rwa [← hb_def] at h
    have hlower : rayleigh (H1 + H2) v ≥
        rayleigh H1 (a⁻¹ • p) + (J - 2 * K) * b ^ 2 - 2 * K * b := by
      rw [hval]
      nlinarith [hkey, hcross, hcross_b, hH1q, hH2q]

    have hmin : -(K ^ 2 / (J - 2 * K)) ≤ (J - 2 * K) * b ^ 2 - 2 * K * b := by
      have hprod : K ^ 2 / (J - 2 * K) * (J - 2 * K) = K ^ 2 :=
        div_mul_cancel₀ _ (ne_of_gt hden)
      have hsq : 0 ≤ ((J - 2 * K) * b - K) ^ 2 := sq_nonneg _
      nlinarith [hsq, hprod, hden]
    nlinarith [hsec_le_r1, hlower, hmin]

end Qatlib.Papers.LocalHam06.MainResults.ProjectionLemma
