/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HittingTimes08.MainResults.HittingSpectrum

/-!
# An idealized spectral detection model

The structure `PhaseSpectrum` records positive phases, their nonnegative masses, and a separate
zero-phase mass. This module defines an ideal threshold detector with repetition and proves
acceptance and cost estimates in terms of reciprocal-phase quantiles, following
[MagniezEtAl2008].

## Main statements

* `lemma_3_4_accept`: bounds acceptance from below when the low-phase mass is small.
* `theorem_3_5`: combines a quantile bound with acceptance and cost estimates.

## References

* [Magniez et al., 2008][MagniezEtAl2008]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HittingTimes08.MainResults

open scoped BigOperators

/-- A finite family of positive phases with nonnegative masses and a separate nonnegative
zero-phase mass, without a normalization requirement. -/
structure PhaseSpectrum (J : Type*) [Fintype J] where
  phase : J → ℝ
  mass : J → ℝ
  zeroMass : ℝ
  phase_pos : ∀ j, 0 < phase j
  mass_nonneg : ∀ j, 0 ≤ mass j
  zeroMass_nonneg : 0 ≤ zeroMass

namespace PhaseSpectrum

variable {J : Type*} [Fintype J]

/-- The sum of the masses attached to the positive phases. -/
def totalMass (S : PhaseSpectrum J) : ℝ := ∑ j, S.mass j

/-- The hitting law with values equal to reciprocal phases and masses inherited from the
spectrum. -/
def law (S : PhaseSpectrum J) : HittingLaw J where
  val j := 1 / S.phase j
  mass := S.mass
  val_pos j := one_div_pos.mpr (S.phase_pos j)
  mass_nonneg := S.mass_nonneg

/-- The ideal detection weight `2 / 3` when `Δ ≤ |α|`, and zero otherwise. -/
def idealThresholdWeight (Δ α : ℝ) : ℝ := if Δ ≤ |α| then 2 / 3 else 0

/-- The amplified weight `1 - (1 - q) ^ k` for `k` repetitions. -/
def ampProb (q : ℝ) (k : ℕ) : ℝ := 1 - (1 - q) ^ k

/-- The mass-weighted sum of amplified ideal threshold weights over the positive phases. -/
def idealDetectWeight (S : PhaseSpectrum J) (Δ : ℝ) (k : ℕ) : ℝ :=
  ∑ j, S.mass j * ampProb (idealThresholdWeight Δ (S.phase j)) k

/-- The detection cost model `k * (1 / Δ + 1)`. -/
def detectCostModel (Δ : ℝ) (k : ℕ) : ℝ := (k : ℝ) * (1 / Δ + 1)

/-- The combined acceptance expression `p + (1 - p) * detAcc`. -/
def idealMainDetectWeight (p detAcc : ℝ) : ℝ := p + (1 - p) * detAcc

/-- A positive phase at least `Δ` has ideal threshold weight `2 / 3`. -/
theorem estimateNonzero_of_pos {Δ α : ℝ} (hα : 0 < α) (h : Δ ≤ α) :
    idealThresholdWeight Δ α = 2 / 3 := by
  unfold idealThresholdWeight
  rw [abs_of_pos hα, if_pos h]

/-- A positive phase below `Δ` has ideal threshold weight zero. -/
theorem estimateNonzero_of_not {Δ α : ℝ} (hα : 0 < α) (h : ¬ Δ ≤ α) :
    idealThresholdWeight Δ α = 0 := by
  unfold idealThresholdWeight
  rw [abs_of_pos hα, if_neg h]

/-- For `0 < Δ ≤ 1`, the detection cost is at most `2 * k / Δ`. -/
theorem detectCost_le (Δ : ℝ) (k : ℕ) (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) :
    detectCostModel Δ k ≤ 2 * (k : ℝ) / Δ := by
  unfold detectCostModel
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h1 : (1 : ℝ) ≤ 1 / Δ := by
    rw [le_div_iff₀ hΔ0]; simpa using hΔ1
  have h2 : 1 / Δ + 1 ≤ 2 * (1 / Δ) := by linarith
  calc (k : ℝ) * (1 / Δ + 1) ≤ (k : ℝ) * (2 * (1 / Δ)) :=
        mul_le_mul_of_nonneg_left h2 hk0
    _ = 2 * (k : ℝ) / Δ := by ring

/-- The ideal detection weight is `(1 - (1 / 3) ^ k)` times the total mass of phases at least
`Δ`. -/
theorem detectAccept_eq (S : PhaseSpectrum J) (Δ : ℝ) (k : ℕ) :
    S.idealDetectWeight Δ k =
      ∑ j ∈ Finset.univ.filter (fun j => Δ ≤ S.phase j),
        S.mass j * (1 - (1 / 3 : ℝ) ^ k) := by
  unfold idealDetectWeight
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ) (fun j => Δ ≤ S.phase j)]
  have hnot : (∑ j ∈ Finset.univ.filter (fun j => ¬ Δ ≤ S.phase j),
      S.mass j * ampProb (idealThresholdWeight Δ (S.phase j)) k) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_filter] at hj
    rw [estimateNonzero_of_not (S.phase_pos j) hj.2]
    unfold ampProb
    simp
  rw [hnot, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_filter] at hj
  rw [estimateNonzero_of_pos (S.phase_pos j) hj.2]
  unfold ampProb
  norm_num

/-- If all positive-phase masses vanish, the ideal detection weight is zero. -/
theorem detectAccept_zero (S : PhaseSpectrum J) (Δ : ℝ) (k : ℕ)
    (hzero : ∀ j, S.mass j = 0) : S.idealDetectWeight Δ k = 0 := by
  unfold idealDetectWeight
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [hzero j, zero_mul]

/-- For `0 < ε ≤ 1`, total mass at most one, low-phase mass at most `ε`, and `(1 / 3) ^ k ≤ ε /
2`, acceptance is at least `totalMass - 2 * ε`. This is the idealized acceptance estimate
for Lemma 3.4 in [MagniezEtAl2008]. -/
theorem lemma_3_4_accept (S : PhaseSpectrum J) (Δ ε : ℝ) (k : ℕ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hk : (1 / 3 : ℝ) ^ k ≤ ε / 2)
    (hmass : S.totalMass ≤ 1)
    (hQH : (∑ j ∈ Finset.univ.filter (fun j => S.phase j < Δ), S.mass j) ≤ ε) :
    S.totalMass - 2 * ε ≤ S.idealDetectWeight Δ k := by
  have hq0 : (0 : ℝ) ≤ (1 / 3 : ℝ) ^ k := pow_nonneg (by norm_num) k
  have hq1 : (1 / 3 : ℝ) ^ k ≤ 1 := by
    have hle : (1 / 3 : ℝ) ^ k ≤ (1 : ℝ) ^ k :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) k
    simpa using hle

  have hsplit : S.totalMass =
      (∑ j ∈ Finset.univ.filter (fun j => Δ ≤ S.phase j), S.mass j) +
        (∑ j ∈ Finset.univ.filter (fun j => S.phase j < Δ), S.mass j) := by
    unfold totalMass
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ) (fun j => Δ ≤ S.phase j)]
    congr 1
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_le
  set A : ℝ := ∑ j ∈ Finset.univ.filter (fun j => Δ ≤ S.phase j), S.mass j
  set B : ℝ := ∑ j ∈ Finset.univ.filter (fun j => S.phase j < Δ), S.mass j
  have hB : B ≤ ε := hQH
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => S.mass_nonneg j
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => S.mass_nonneg j
  have hA1 : A ≤ 1 := by
    have htot : S.totalMass ≤ 1 := hmass
    rw [hsplit] at htot
    linarith
  have hac : S.idealDetectWeight Δ k = (1 - (1 / 3 : ℝ) ^ k) * A := by
    rw [detectAccept_eq]
    unfold A
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hac]
  have hqε : (1 / 3 : ℝ) ^ k ≤ ε := by linarith
  have hmul : (1 / 3 : ℝ) ^ k * A ≤ (1 / 3 : ℝ) ^ k := by
    simpa using mul_le_mul_of_nonneg_left hA1 hq0
  have hchain : S.totalMass - 2 * ε ≤ A - ε := by
    rw [hsplit]; linarith
  have hstep : A - ε ≤ (1 - (1 / 3 : ℝ) ^ k) * A := by
    nlinarith [hmul, hqε]
  exact hchain.trans hstep

/-- If `T ≥ 1` bounds the `ε`-quantile, `0 < ε ≤ 1`, total mass is at most one, and repetition
error is at most `ε / 2`, threshold `1 / T` gives acceptance at least `totalMass - 2 * ε`
and cost at most `2 * k * T`, as in Theorem 3.5 of [MagniezEtAl2008]. -/
theorem theorem_3_5 (S : PhaseSpectrum J) (ε T : ℝ) (k : ℕ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hT1 : 1 ≤ T)
    (hk : (1 / 3 : ℝ) ^ k ≤ ε / 2)
    (hmass : S.totalMass ≤ 1)
    (hT : (S.law).quantile ε ≤ T) :
    S.totalMass - 2 * ε ≤ S.idealDetectWeight (1 / T) k ∧
      detectCostModel (1 / T) k ≤ 2 * (k : ℝ) * T := by
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT1
  have htail : (S.law).tail T ≤ ε :=
    ((S.law).tail_antitone hT).trans ((S.law).tail_quantile_le hε0.le)
  have hQH : (∑ j ∈ Finset.univ.filter (fun j => S.phase j < 1 / T), S.mass j) ≤ ε := by
    have heq : Finset.univ.filter (fun j => S.phase j < 1 / T) =
        Finset.univ.filter (fun j => T < (S.law).val j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, law, HittingLaw.val]
      constructor
      · intro h
        rw [lt_div_iff₀ hT0] at h
        rw [lt_div_iff₀ (S.phase_pos j)]
        linarith
      · intro h
        rw [lt_div_iff₀ (S.phase_pos j)] at h
        rw [lt_div_iff₀ hT0]
        linarith
    rw [heq]
    exact htail
  refine ⟨?_, ?_⟩
  · have hΔ1 : 1 / T ≤ 1 := by
      rw [div_le_one hT0]; exact hT1
    exact lemma_3_4_accept S (1 / T) ε k hε0 hε1 hk hmass hQH
  · have hΔ1 : 1 / T ≤ 1 := by
      rw [div_le_one hT0]; exact hT1
    have := detectCost_le (1 / T) k (by positivity) hΔ1
    calc detectCostModel (1 / T) k ≤ 2 * (k : ℝ) / (1 / T) := this
      _ = 2 * (k : ℝ) * T := by field_simp

/-- If all positive-phase masses vanish, detection at threshold `1 / T` has zero ideal
acceptance. -/
theorem theorem_3_5_zero (S : PhaseSpectrum J) (T : ℝ) (k : ℕ)
    (hzero : ∀ j, S.mass j = 0) : S.idealDetectWeight (1 / T) k = 0 :=
  detectAccept_zero S (1 / T) k hzero

/-- For `0 ≤ p < 1` and `ε > 0`, a conditional detection weight at least `1 - 2 * ε / (1 - p)`
gives combined acceptance at least `1 - 2 * ε`, as in Corollary 3.6 of [MagniezEtAl2008]. -/
theorem corollary_3_6 (p detAcc ε : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 < ε)
    (hm : 0 < 1 - p)
    (hdet : 1 - 2 * ε / (1 - p) ≤ detAcc) :
    1 - 2 * ε ≤ idealMainDetectWeight p detAcc := by
  have hmul := mul_le_mul_of_nonneg_left hdet hm.le
  have hcollapse : (1 - p) * (1 - 2 * ε / (1 - p)) = (1 - p) - 2 * ε := by
    field_simp
  rw [hcollapse] at hmul
  unfold idealMainDetectWeight
  linarith

end PhaseSpectrum

end Qatlib.Papers.HittingTimes08.MainResults
