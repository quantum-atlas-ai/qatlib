/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HittingTimes08.MainResults.Detect
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HittingTimes08.MainResults

open scoped BigOperators

namespace HittingLaw

variable {J : Type*} [Fintype J]

def sqLaw (L : HittingLaw J) : HittingLaw J where
  val j := L.val j ^ 2
  mass := L.mass
  val_pos j := pow_pos (L.val_pos j) 2
  mass_nonneg := L.mass_nonneg

theorem tail_sqLaw (L : HittingLaw J) {y : ℝ} (hy : 0 ≤ y) :
    L.sqLaw.tail y = L.tail (Real.sqrt y) := by
  unfold tail
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simpa only [sqLaw] using (Real.sqrt_lt hy (L.val_pos j).le).symm

theorem quantile_sq (L : HittingLaw J) {ε : ℝ} (hε : 0 ≤ ε) :
    L.sqLaw.quantile ε = L.quantile ε ^ 2 := by
  set a : ℝ := L.quantile ε with ha
  have ha0 : 0 ≤ a := L.quantile_nonneg ε
  have hfeas : L.sqLaw.tail (a ^ 2) ≤ ε := by
    rw [tail_sqLaw L (sq_nonneg a), Real.sqrt_sq ha0]
    exact L.tail_quantile_le hε
  apply le_antisymm
  · unfold HittingLaw.quantile
    refine csInf_le ⟨0, fun y hy => hy.1⟩ ⟨pow_nonneg ha0 2, hfeas⟩
  · unfold HittingLaw.quantile
    refine le_csInf ?_ ?_
    · refine ⟨L.sqLaw.valueSum + 1, ?_, ?_⟩
      · exact add_nonneg (Finset.sum_nonneg fun i _ => (L.sqLaw.val_pos i).le) zero_le_one
      · exact L.sqLaw.feasible_nonempty hε
    · intro y hy
      have hsqrt_tail : L.tail (Real.sqrt y) ≤ ε := by
        rw [← tail_sqLaw L hy.1]
        exact hy.2
      have ha_le : a ≤ Real.sqrt y := by
        rw [ha]
        unfold HittingLaw.quantile
        exact csInf_le ⟨0, fun z hz => hz.1⟩ ⟨Real.sqrt_nonneg y, hsqrt_tail⟩
      calc a ^ 2 ≤ (Real.sqrt y) ^ 2 := pow_le_pow_left₀ ha0 ha_le 2
        _ = y := Real.sq_sqrt hy.1

theorem mean_sq_le (L : HittingLaw J) :
    L.mean ^ 2 ≤ L.totalMass * L.sqLaw.mean := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset J)
      (fun j : J => Real.sqrt (L.mass j))
      (fun j : J => Real.sqrt (L.mass j) * L.val j)
  have h1 : (∑ j, Real.sqrt (L.mass j) * (Real.sqrt (L.mass j) * L.val j)) = L.mean := by
    unfold mean
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, Real.mul_self_sqrt (L.mass_nonneg j)]
  have h2 : (∑ j, Real.sqrt (L.mass j) ^ 2) = L.totalMass := by
    unfold totalMass
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Real.sq_sqrt (L.mass_nonneg j)
  have h3 : (∑ j, (Real.sqrt (L.mass j) * L.val j) ^ 2) = L.sqLaw.mean := by
    unfold HittingLaw.mean
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [HittingLaw.sqLaw]
    rw [mul_pow, Real.sq_sqrt (L.mass_nonneg j)]
  simpa [h1, h2, h3] using hCS

theorem theorem_3_15_first (L : HittingLaw J) (HT : ℝ)
    (hTot : L.totalMass ≤ 1) (hbridge : 2 * L.sqLaw.mean ≤ HT) :
    L.mean ≤ Real.sqrt (HT / 2) := by
  have hm0 : 0 ≤ L.mean :=
    Finset.sum_nonneg fun j _ => mul_nonneg (L.mass_nonneg j) (L.val_pos j).le
  have hsm0 : 0 ≤ L.sqLaw.mean :=
    Finset.sum_nonneg fun j _ => mul_nonneg (L.sqLaw.mass_nonneg j) (L.sqLaw.val_pos j).le
  have hbound : L.mean ^ 2 ≤ HT / 2 := by
    have h1 : L.totalMass * L.sqLaw.mean ≤ 1 * L.sqLaw.mean :=
      mul_le_mul_of_nonneg_right hTot hsm0
    have h2 := L.mean_sq_le
    linarith
  rw [Real.le_sqrt (x := L.mean) (y := HT / 2) hm0 (by linarith)]
  exact hbound

theorem theorem_3_15_second (L : HittingLaw J) {ε : ℝ} (hε : 0 ≤ ε) :
    L.quantile ε = Real.sqrt (L.sqLaw.quantile ε) := by
  rw [quantile_sq L hε, Real.sqrt_sq (L.quantile_nonneg ε)]

end HittingLaw

namespace PhaseSpectrum

variable {J : Type*} [Fintype J]

theorem corollary_3_13 (S : PhaseSpectrum J) (v1 ε : ℝ) (j0 : J)
    (hval : S.law.val j0 = v1) (hv1 : 0 < v1)
    (hmax : ∀ j, S.law.val j ≤ v1)
    (hmass : 1 / 2 ≤ S.law.mass j0)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    S.law.quantile ε = v1 := by
  apply le_antisymm
  · unfold HittingLaw.quantile
    refine csInf_le ⟨0, fun y hy => hy.1⟩ ⟨hv1.le, ?_⟩
    have hz : S.law.tail v1 = 0 := by
      unfold HittingLaw.tail
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_filter] at hj
      linarith [hmax j, hj.2]
    rw [hz]; exact hε0.le
  · unfold HittingLaw.quantile
    refine le_csInf ?_ ?_
    · refine ⟨S.law.valueSum + 1, ?_, S.law.feasible_nonempty hε0.le⟩
      exact add_nonneg (Finset.sum_nonneg fun i _ => (S.law.val_pos i).le) zero_le_one
    · intro y hy
      by_contra hlt
      push_neg at hlt
      have hmem : j0 ∈ Finset.univ.filter (fun j => y < S.law.val j) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hval]; exact hlt
      have hge : 1 / 2 ≤ S.law.tail y := by
        unfold HittingLaw.tail
        exact hmass.trans (Finset.single_le_sum (fun i _ => S.law.mass_nonneg i) hmem)
      linarith [hy.2]

theorem theorem_3_14 (S : PhaseSpectrum J) (v1 ε : ℝ) (j0 : J)
    (hval : S.law.val j0 = v1) (hv1 : 0 < v1)
    (hmax : ∀ j, S.law.val j ≤ v1)
    (hmass : 1 / 2 ≤ S.law.mass j0)
    (hTot : S.law.totalMass = 1)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    S.law.mean ≤ S.law.quantile ε := by
  have hq : S.law.quantile ε = v1 :=
    corollary_3_13 S v1 ε j0 hval hv1 hmax hmass hε0 hε1
  rw [hq]
  unfold HittingLaw.mean
  calc ∑ j, S.law.mass j * S.law.val j ≤ ∑ j, S.law.mass j * v1 :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hmax j) (S.law.mass_nonneg j)
    _ = S.law.totalMass * v1 := by rw [HittingLaw.totalMass, Finset.sum_mul]
    _ = 1 * v1 := by rw [hTot]
    _ = v1 := one_mul v1

end PhaseSpectrum

theorem lemma_3_12_exists {Z : Type*} [Fintype Z] [Nonempty Z]
    (a0 a1 : Z → ℝ) (hsum : ∑ z, a0 z ^ 2 = ∑ z, a1 z ^ 2) :
    ∃ z, a0 z ^ 2 ≤ a1 z ^ 2 := by
  by_contra h
  push_neg at h
  have hlt : ∑ z, a1 z ^ 2 < ∑ z, a0 z ^ 2 :=
    Finset.sum_lt_sum (fun z _ => (h z).le) (by
      obtain ⟨z⟩ := ‹Nonempty Z›
      exact ⟨z, Finset.mem_univ z, h z⟩)
  linarith

theorem lemma_3_12_projection {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    1 / Real.sqrt 2 ≤ 2 * a * c / Real.sqrt (8 * a ^ 2 * c ^ 2) := by
  have hac : 0 < a * c := mul_pos ha hc
  have hsqrt4 : Real.sqrt 4 = (2 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  have hsqrt8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt4]
  have hs : Real.sqrt (8 * a ^ 2 * c ^ 2) = 2 * Real.sqrt 2 * (a * c) := by
    rw [show (8 : ℝ) * a ^ 2 * c ^ 2 = 8 * (a * c) ^ 2 by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8), hsqrt8,
      Real.sqrt_sq_eq_abs, abs_of_pos hac]
  have hsimp : 2 * a * c / (2 * Real.sqrt 2 * (a * c)) = 1 / Real.sqrt 2 := by
    rw [div_eq_div_iff (ne_of_gt (by positivity)) (ne_of_gt (by positivity))]
    ring
  rw [hs]
  exact hsimp.ge

theorem lemma_3_12 {Z : Type*} [Fintype Z] [Nonempty Z]
    (a0 a1 cotv : Z → ℝ) (hsum : ∑ z, a0 z ^ 2 = ∑ z, a1 z ^ 2)
    (hpos : ∀ z, 0 < a0 z) (hcot : ∀ z, 0 < cotv z) :
    ∃ z, 1 / Real.sqrt 2 ≤
      2 * a0 z * cotv z / Real.sqrt (8 * (a0 z) ^ 2 * (cotv z) ^ 2) := by
  obtain ⟨z, _hz⟩ := lemma_3_12_exists a0 a1 hsum
  exact ⟨z, lemma_3_12_projection (hpos z) (hcot z)⟩

end Qatlib.Papers.HittingTimes08.MainResults
