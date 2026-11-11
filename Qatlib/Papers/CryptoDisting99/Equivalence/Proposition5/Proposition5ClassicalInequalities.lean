/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CryptoDisting99.Equivalence.Defs
import Qatlib.Papers.CryptoDisting99.Equivalence.Proposition5.FigOneBounds
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Real.Sqrt

/-!
# Classical distinguishability inequalities

This module proves the classical inequalities in Proposition 5 relating the Bhattacharyya
coefficient, Kolmogorov distance, error probability, and Shannon distinguishability. Binary
entropy estimates and posterior-weight identities supply the scalar ingredients.

These constructions accompany the results of [FuchsVanDeGraaf1999].

## Main statements

* `proposition5_43`: bounds Kolmogorov distance using the Bhattacharyya coefficient.
* `proposition5_44`: bounds Shannon distinguishability using the error probability.
* `proposition5`: collects the proved classical inequalities.

## References

* [Fuchs and van de Graaf, 1999][FuchsVanDeGraaf1999]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CryptoDisting99.Equivalence

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence
open scoped BigOperators

variable {X : Type} [Fintype X]

/-- Binary entropy vanishes at zero. -/
@[simp] lemma binaryEntropy_zero : binaryEntropy 0 = 0 := by simp [binaryEntropy]

/-- Binary entropy vanishes at one. -/
@[simp] lemma binaryEntropy_one : binaryEntropy 1 = 0 := by simp [binaryEntropy]

/-- Binary entropy equals one at one half. -/
@[simp] lemma binaryEntropy_two_inv : binaryEntropy (1 / 2) = 1 := by
  unfold binaryEntropy
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
  field_simp

/-- Binary entropy is invariant under replacing its argument by its complement. -/
@[simp] lemma binaryEntropy_one_sub (r : ℝ) :
    binaryEntropy (1 - r) = binaryEntropy r := by
  unfold binaryEntropy; rw [Real.binEntropy_one_sub]

/-- Binary entropy is concave on the unit interval. -/
lemma concaveOn_binaryEntropy : ConcaveOn ℝ (Set.Icc 0 1) binaryEntropy := by
  have hc : (0 : ℝ) ≤ (Real.log 2)⁻¹ := le_of_lt (inv_pos.mpr (Real.log_pos (by norm_num)))
  have h := (Real.strictConcave_binEntropy.concaveOn).smul hc
  simpa [binaryEntropy] using! h

/-- Binary entropy is nonnegative on the unit interval. -/
lemma binaryEntropy_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : 0 ≤ binaryEntropy r := by
  unfold binaryEntropy
  exact mul_nonneg (le_of_lt (inv_pos.mpr (Real.log_pos (by norm_num))))
    (Real.binEntropy_nonneg h0 h1)

/-- Binary entropy is at most one for every real argument. -/
lemma binaryEntropy_le_one (r : ℝ) : binaryEntropy r ≤ 1 := by
  unfold binaryEntropy
  have h := Real.binEntropy_le_log_two (p := r)
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc (Real.log 2)⁻¹ * Real.binEntropy r ≤ (Real.log 2)⁻¹ * Real.log 2 :=
        mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hpos))
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- For a parameter between zero and one half, binary entropy is at least twice the parameter. -/
lemma two_mul_le_binaryEntropy_of_le_half {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    2 * r ≤ binaryEntropy r := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hmemh : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have key := concaveOn_binaryEntropy.2 hmem0 hmemh
    (show (0 : ℝ) ≤ 1 - 2 * r by linarith)
    (show (0 : ℝ) ≤ 2 * r by linarith)
    (show 1 - 2 * r + 2 * r = 1 by ring)
  rw [binaryEntropy_zero, binaryEntropy_two_inv] at key
  simp only [smul_eq_mul, mul_one, mul_zero, zero_add] at key
  rw [show 2 * r * (1 / 2) = r by ring] at key
  linarith

/-- On the unit interval, binary entropy is at least twice the smaller of a parameter and its
complement. -/
lemma two_mul_min_le_binaryEntropy {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    2 * min r (1 - r) ≤ binaryEntropy r := by
  rcases le_total r (1 / 2) with h | h
  · rw [min_eq_left (by linarith)]
    exact two_mul_le_binaryEntropy_of_le_half hr0 h
  · rw [min_eq_right (by linarith)]
    have h' := two_mul_le_binaryEntropy_of_le_half (r := 1 - r) (by linarith) (by linarith)
    rw [binaryEntropy_one_sub r] at h'
    linarith

/-- Taking the smaller of a parameter and its complement preserves binary entropy. -/
lemma binaryEntropy_min (r : ℝ) :
    binaryEntropy (min r (1 - r)) = binaryEntropy r := by
  rcases le_total r (1 / 2) with h | h
  · rw [min_eq_left (by linarith)]
  · rw [min_eq_right (by linarith), binaryEntropy_one_sub]

/-- The Bhattacharyya coefficient is the sum of products of the square roots of corresponding
probabilities. -/
theorem bhattacharyya_eq_sum_sqrt_mul (p0 p1 : FinDist X) :
    bhattacharyya p0 p1 = ∑ x, Real.sqrt (p0.prob x) * Real.sqrt (p1.prob x) := by
  unfold bhattacharyya
  exact Finset.sum_congr rfl fun x _ => Real.sqrt_mul (p0.nonneg x) (p1.prob x)

/-- Expands the squared difference of the square roots of two point probabilities. -/
private lemma sq_sub_sqrt (p0 p1 : FinDist X) (x : X) :
    (Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)) ^ 2
      = p0.prob x + p1.prob x - 2 * (Real.sqrt (p0.prob x) * Real.sqrt (p1.prob x)) := by
  have ha : Real.sqrt (p0.prob x) * Real.sqrt (p0.prob x) = p0.prob x :=
    Real.mul_self_sqrt (p0.nonneg x)
  have hb : Real.sqrt (p1.prob x) * Real.sqrt (p1.prob x) = p1.prob x :=
    Real.mul_self_sqrt (p1.nonneg x)
  have hsq : (Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)) ^ 2
      = Real.sqrt (p0.prob x) * Real.sqrt (p0.prob x)
        + Real.sqrt (p1.prob x) * Real.sqrt (p1.prob x)
        - 2 * (Real.sqrt (p0.prob x) * Real.sqrt (p1.prob x)) := by ring
  rw [hsq, ha, hb]

/-- Expands the squared sum of the square roots of two point probabilities. -/
private lemma sq_add_sqrt (p0 p1 : FinDist X) (x : X) :
    (Real.sqrt (p0.prob x) + Real.sqrt (p1.prob x)) ^ 2
      = p0.prob x + p1.prob x + 2 * (Real.sqrt (p0.prob x) * Real.sqrt (p1.prob x)) := by
  have ha : Real.sqrt (p0.prob x) * Real.sqrt (p0.prob x) = p0.prob x :=
    Real.mul_self_sqrt (p0.nonneg x)
  have hb : Real.sqrt (p1.prob x) * Real.sqrt (p1.prob x) = p1.prob x :=
    Real.mul_self_sqrt (p1.nonneg x)
  have hsq : (Real.sqrt (p0.prob x) + Real.sqrt (p1.prob x)) ^ 2
      = Real.sqrt (p0.prob x) * Real.sqrt (p0.prob x)
        + Real.sqrt (p1.prob x) * Real.sqrt (p1.prob x)
        + 2 * (Real.sqrt (p0.prob x) * Real.sqrt (p1.prob x)) := by ring
  rw [hsq, ha, hb]

/-- One minus the Bhattacharyya coefficient is half the sum of squared differences of square
roots of probabilities. -/
theorem one_sub_bhattacharyya_eq_sum_sq (p0 p1 : FinDist X) :
    1 - bhattacharyya p0 p1 =
      (1 / 2) * ∑ x, (Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)) ^ 2 := by
  have hB := bhattacharyya_eq_sum_sqrt_mul p0 p1
  have hsum : (∑ x, (Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)) ^ 2)
      = 2 - 2 * ∑ x, Real.sqrt (p0.prob x) * Real.sqrt (p1.prob x) := by
    rw [Finset.sum_congr rfl fun x _ => sq_sub_sqrt p0 p1 x]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      p0.sum_one, p1.sum_one]
    ring
  rw [hB, hsum]
  ring

/-- Expresses Kolmogorov distance using the absolute difference and sum of square roots of
corresponding probabilities. -/
theorem kolmogorov_eq_sum_abs_mul (p0 p1 : FinDist X) :
    classicalKolmogorov p0 p1 =
      (1 / 2) * ∑ x, |Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)| *
        (Real.sqrt (p0.prob x) + Real.sqrt (p1.prob x)) := by
  have hpt : ∀ x, |p0.prob x - p1.prob x| =
      |Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)| *
        (Real.sqrt (p0.prob x) + Real.sqrt (p1.prob x)) := by
    intro x
    have ha : Real.sqrt (p0.prob x) * Real.sqrt (p0.prob x) = p0.prob x :=
      Real.mul_self_sqrt (p0.nonneg x)
    have hb : Real.sqrt (p1.prob x) * Real.sqrt (p1.prob x) = p1.prob x :=
      Real.mul_self_sqrt (p1.nonneg x)
    have hfac : p0.prob x - p1.prob x =
        (Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)) *
          (Real.sqrt (p0.prob x) + Real.sqrt (p1.prob x)) := by
      rw [sub_mul, mul_add, mul_add, ha, hb]
      ring
    rw [hfac, abs_mul,
      abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  unfold classicalKolmogorov
  rw [tv]
  have hsum : (∑ x, |p0.prob x - p1.prob x|) =
      ∑ x, |Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)| *
        (Real.sqrt (p0.prob x) + Real.sqrt (p1.prob x)) :=
    Finset.sum_congr rfl fun x _ => hpt x
  rw [hsum]
  ring

/-- One minus the Bhattacharyya coefficient is bounded above by Kolmogorov distance, as in
Proposition 5, equation (43), of [FuchsVanDeGraaf1999]. -/
theorem proposition5_43_left (p0 p1 : FinDist X) :
    1 - bhattacharyya p0 p1 ≤ classicalKolmogorov p0 p1 := by
  rw [one_sub_bhattacharyya_eq_sum_sq, kolmogorov_eq_sum_abs_mul]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine Finset.sum_le_sum fun x _ => ?_
  have h1 : |Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)| ≤
      Real.sqrt (p0.prob x) + Real.sqrt (p1.prob x) := by
    rw [abs_le]
    constructor <;> linarith [Real.sqrt_nonneg (p0.prob x), Real.sqrt_nonneg (p1.prob x)]
  calc (Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)) ^ 2
      = |Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)| *
          |Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)| := by
        rw [← sq, sq_abs]
    _ ≤ |Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)| *
          (Real.sqrt (p0.prob x) + Real.sqrt (p1.prob x)) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

/-- Kolmogorov distance is at most the square root of one minus the squared Bhattacharyya
coefficient, as in Proposition 5, equation (43), of [FuchsVanDeGraaf1999]. -/
theorem proposition5_43_right (p0 p1 : FinDist X) :
    classicalKolmogorov p0 p1 ≤ Real.sqrt (1 - (bhattacharyya p0 p1) ^ 2) := by
  rw [kolmogorov_eq_sum_abs_mul]
  have hF : (∑ x, (Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)) ^ 2)
      = 2 * (1 - bhattacharyya p0 p1) := by
    have h := one_sub_bhattacharyya_eq_sum_sq p0 p1
    linarith
  have hG : (∑ x, (Real.sqrt (p0.prob x) + Real.sqrt (p1.prob x)) ^ 2)
      = 2 * (1 + bhattacharyya p0 p1) := by
    have hB := bhattacharyya_eq_sum_sqrt_mul p0 p1
    have hsum : (∑ x, (Real.sqrt (p0.prob x) + Real.sqrt (p1.prob x)) ^ 2)
        = 2 + 2 * ∑ x, Real.sqrt (p0.prob x) * Real.sqrt (p1.prob x) := by
      rw [Finset.sum_congr rfl fun x _ => sq_add_sqrt p0 p1 x]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        p0.sum_one, p1.sum_one]
      ring
    rw [hB, hsum]
    ring
  have hCS : (∑ x, |Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)| *
        (Real.sqrt (p0.prob x) + Real.sqrt (p1.prob x))) ^ 2 ≤
      (∑ x, (Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)) ^ 2) *
        (∑ x, (Real.sqrt (p0.prob x) + Real.sqrt (p1.prob x)) ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset X)
      (fun x => |Real.sqrt (p0.prob x) - Real.sqrt (p1.prob x)|)
      (fun x => Real.sqrt (p0.prob x) + Real.sqrt (p1.prob x))
    simpa [sq_abs] using! h
  refine Real.le_sqrt_of_sq_le ?_
  have hmul : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
  rw [mul_pow, hmul]
  have h' := hCS
  rw [hF, hG] at h'
  nlinarith

/-- Proves both bounds relating Kolmogorov distance and the Bhattacharyya coefficient in
Proposition 5, equation (43), of [FuchsVanDeGraaf1999]. -/
theorem proposition5_43 (p0 p1 : FinDist X) :
    1 - bhattacharyya p0 p1 ≤ classicalKolmogorov p0 p1 ∧
      classicalKolmogorov p0 p1 ≤ Real.sqrt (1 - (bhattacharyya p0 p1) ^ 2) :=
  ⟨proposition5_43_left p0 p1, proposition5_43_right p0 p1⟩

/-- The ratio of the first point probability to the sum of both point probabilities lies in the
unit interval. -/
lemma posterior_mem (p0 p1 : FinDist X) (x : X) :
    p0.prob x / (p0.prob x + p1.prob x) ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 := p0.nonneg x
  have h1 := p1.nonneg x
  constructor
  · exact div_nonneg h0 (add_nonneg h0 h1)
  · by_cases h : p0.prob x + p1.prob x = 0
    · simp [h]
    · have hpos : 0 < p0.prob x + p1.prob x :=
        lt_of_le_of_ne (add_nonneg h0 h1) (Ne.symm h)
      rw [div_le_one hpos]
      linarith

/-- The average of two point probabilities is nonnegative. -/
lemma weight_nonneg (p0 p1 : FinDist X) (x : X) : 0 ≤ (p0.prob x + p1.prob x) / 2 := by
  have h0 := p0.nonneg x; have h1 := p1.nonneg x; linarith

/-- The pointwise averages of two probability distributions sum to one. -/
lemma sum_weight_eq_one (p0 p1 : FinDist X) :
    (∑ x, (p0.prob x + p1.prob x) / 2) = 1 := by
  rw [← Finset.sum_div, Finset.sum_add_distrib, p0.sum_one, p1.sum_one]
  norm_num

/-- Multiplying the smaller posterior probability by the mixture weight gives half the smaller
point probability. -/
lemma weight_mul_min_eq (p0 p1 : FinDist X) (x : X) :
    ((p0.prob x + p1.prob x) / 2) *
      min (p0.prob x / (p0.prob x + p1.prob x))
        (1 - p0.prob x / (p0.prob x + p1.prob x))
      = min (p0.prob x) (p1.prob x) / 2 := by
  have h0 := p0.nonneg x
  have h1 := p1.nonneg x
  by_cases h : p0.prob x + p1.prob x = 0
  · have h0' : p0.prob x = 0 := by linarith
    have h1' : p1.prob x = 0 := by linarith
    simp [h0', h1']
  · have hpos : 0 < p0.prob x + p1.prob x :=
      lt_of_le_of_ne (add_nonneg h0 h1) (Ne.symm h)
    have hrw : p0.prob x / (p0.prob x + p1.prob x) =
        p0.prob x * (p0.prob x + p1.prob x)⁻¹ := div_eq_mul_inv ..
    rw [hrw]
    rcases le_total (p0.prob x) (p1.prob x) with hle | hle
    · have hmin : min (p0.prob x) (p1.prob x) = p0.prob x := min_eq_left hle
      have hmin2 : min (p0.prob x * (p0.prob x + p1.prob x)⁻¹)
          (1 - p0.prob x * (p0.prob x + p1.prob x)⁻¹) =
          p0.prob x * (p0.prob x + p1.prob x)⁻¹ := by
        rw [min_eq_left]
        rw [le_sub_iff_add_le, show p0.prob x * (p0.prob x + p1.prob x)⁻¹ +
          p0.prob x * (p0.prob x + p1.prob x)⁻¹ =
          2 * (p0.prob x * (p0.prob x + p1.prob x)⁻¹) by ring]
        rw [show (2 : ℝ) * (p0.prob x * (p0.prob x + p1.prob x)⁻¹) =
            2 * p0.prob x / (p0.prob x + p1.prob x) by field_simp]
        rw [div_le_one hpos]
        linarith
      rw [hmin2, hmin]
      field_simp
    · have hmin : min (p0.prob x) (p1.prob x) = p1.prob x := min_eq_right hle
      have hmin2 : min (p0.prob x * (p0.prob x + p1.prob x)⁻¹)
          (1 - p0.prob x * (p0.prob x + p1.prob x)⁻¹) =
          1 - p0.prob x * (p0.prob x + p1.prob x)⁻¹ := by
        rw [min_eq_right]
        rw [sub_le_iff_le_add, show p0.prob x * (p0.prob x + p1.prob x)⁻¹ +
          p0.prob x * (p0.prob x + p1.prob x)⁻¹ =
          2 * (p0.prob x * (p0.prob x + p1.prob x)⁻¹) by ring]
        rw [show (2 : ℝ) * (p0.prob x * (p0.prob x + p1.prob x)⁻¹) =
            2 * p0.prob x / (p0.prob x + p1.prob x) by field_simp]
        rw [le_div_iff₀ hpos]
        linarith
      rw [hmin2, hmin]
      field_simp
      ring

/-- The mixture-weighted sum of the smaller posterior probabilities equals the classical error
probability. -/
lemma sum_weight_mul_min_eq (p0 p1 : FinDist X) :
    (∑ x, ((p0.prob x + p1.prob x) / 2) *
      min (p0.prob x / (p0.prob x + p1.prob x))
        (1 - p0.prob x / (p0.prob x + p1.prob x)))
      = classicalErrProb p0 p1 := by
  unfold classicalErrProb
  rw [Finset.sum_congr rfl (fun x _ => weight_mul_min_eq p0 p1 x)]
  rw [← Finset.sum_div]
  ring

/-- One minus the binary entropy of the error probability is bounded above by Shannon
distinguishability, as in Proposition 5, equation (44), of [FuchsVanDeGraaf1999]. -/
theorem proposition5_44_left (p0 p1 : FinDist X) :
    1 - binaryEntropy (classicalErrProb p0 p1) ≤ shannonDist p0 p1 := by
  unfold shannonDist
  have hj := concaveOn_binaryEntropy.le_map_sum
    (t := Finset.univ)
    (w := fun x => (p0.prob x + p1.prob x) / 2)
    (p := fun x => min (p0.prob x / (p0.prob x + p1.prob x))
        (1 - p0.prob x / (p0.prob x + p1.prob x)))
    (fun x _ => by
      have h0 := p0.nonneg x; have h1 := p1.nonneg x; linarith)
    (sum_weight_eq_one p0 p1)
    (fun x _ => by
      have h := posterior_mem p0 p1 x
      exact ⟨le_min h.1 (by linarith [h.2]),
        min_le_iff.mpr (Or.inr (by linarith [h.1]))⟩)
  simp only [smul_eq_mul] at hj
  rw [sum_weight_mul_min_eq] at hj
  have hcongr : (∑ x, ((p0.prob x + p1.prob x) / 2) *
      binaryEntropy (min (p0.prob x / (p0.prob x + p1.prob x))
        (1 - p0.prob x / (p0.prob x + p1.prob x)))) =
      ∑ x, ((p0.prob x + p1.prob x) / 2) *
        binaryEntropy (p0.prob x / (p0.prob x + p1.prob x)) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [binaryEntropy_min (p0.prob x / (p0.prob x + p1.prob x))]
  rw [hcongr] at hj
  linarith

/-- Shannon distinguishability is at most one minus twice the classical error probability, as in
Proposition 5, equation (44), of [FuchsVanDeGraaf1999]. -/
theorem proposition5_44_right (p0 p1 : FinDist X) :
    shannonDist p0 p1 ≤ 1 - 2 * classicalErrProb p0 p1 := by
  unfold shannonDist
  have hpt : ∀ x ∈ (Finset.univ : Finset X),
      ((p0.prob x + p1.prob x) / 2) * (2 * min (p0.prob x / (p0.prob x + p1.prob x))
        (1 - p0.prob x / (p0.prob x + p1.prob x))) ≤
      ((p0.prob x + p1.prob x) / 2) * binaryEntropy (p0.prob x / (p0.prob x + p1.prob x)) := by
    intro x _
    apply mul_le_mul_of_nonneg_left _ (weight_nonneg p0 p1 x)
    exact two_mul_min_le_binaryEntropy (posterior_mem p0 p1 x).1 (posterior_mem p0 p1 x).2
  have hsum := Finset.sum_le_sum hpt
  have hleft : (∑ x, ((p0.prob x + p1.prob x) / 2) *
      (2 * min (p0.prob x / (p0.prob x + p1.prob x))
        (1 - p0.prob x / (p0.prob x + p1.prob x)))) =
      2 * classicalErrProb p0 p1 := by
    rw [show (∑ x, ((p0.prob x + p1.prob x) / 2) *
        (2 * min (p0.prob x / (p0.prob x + p1.prob x))
          (1 - p0.prob x / (p0.prob x + p1.prob x)))) =
        2 * ∑ x, ((p0.prob x + p1.prob x) / 2) *
          min (p0.prob x / (p0.prob x + p1.prob x))
            (1 - p0.prob x / (p0.prob x + p1.prob x)) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring]
    rw [sum_weight_mul_min_eq]
  rw [hleft] at hsum
  linarith

/-- Shannon distinguishability is at most one. -/
lemma shannonDist_le_one (p0 p1 : FinDist X) : shannonDist p0 p1 ≤ 1 := by
  unfold shannonDist
  have h : 0 ≤ ∑ x, ((p0.prob x + p1.prob x) / 2) *
      binaryEntropy (p0.prob x / (p0.prob x + p1.prob x)) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (weight_nonneg p0 p1 x)
      (binaryEntropy_nonneg (posterior_mem p0 p1 x).1 (posterior_mem p0 p1 x).2)
  linarith

/-- The mixture weight times twice the geometric mean of the posterior probabilities equals the
geometric mean of the point probabilities. -/
lemma weight_mul_sqrt_eq (p0 p1 : FinDist X) (x : X) :
    ((p0.prob x + p1.prob x) / 2) *
      (2 * Real.sqrt ((p0.prob x / (p0.prob x + p1.prob x)) *
        (1 - p0.prob x / (p0.prob x + p1.prob x))))
      = Real.sqrt (p0.prob x * p1.prob x) := by
  have h0 := p0.nonneg x
  have h1 := p1.nonneg x
  by_cases h : p0.prob x + p1.prob x = 0
  · have h0' : p0.prob x = 0 := by linarith
    have h1' : p1.prob x = 0 := by linarith
    simp [h0', h1']
  · have hpos : 0 < p0.prob x + p1.prob x :=
      lt_of_le_of_ne (add_nonneg h0 h1) (Ne.symm h)
    have hfac : (p0.prob x / (p0.prob x + p1.prob x)) *
        (1 - p0.prob x / (p0.prob x + p1.prob x))
        = (p0.prob x * p1.prob x)/((p0.prob x + p1.prob x)^2) := by
      field_simp
      ring
    rw [hfac]
    have hsqrt : Real.sqrt ((p0.prob x * p1.prob x)/((p0.prob x + p1.prob x)^2))
        = Real.sqrt (p0.prob x * p1.prob x) / (p0.prob x + p1.prob x) := by
      rw [Real.sqrt_div' _ (by positivity : (0:ℝ) ≤ (p0.prob x + p1.prob x)^2)]
      rw [Real.sqrt_sq (le_of_lt hpos)]
    rw [hsqrt]
    field_simp

/-- The mixture-weighted sum of twice the geometric means of posterior probabilities equals the
Bhattacharyya coefficient. -/
lemma sum_weight_mul_sqrt_eq (p0 p1 : FinDist X) :
    (∑ x, ((p0.prob x + p1.prob x) / 2) *
      (2 * Real.sqrt ((p0.prob x / (p0.prob x + p1.prob x)) *
        (1 - p0.prob x / (p0.prob x + p1.prob x)))))
      = bhattacharyya p0 p1 := by
  unfold bhattacharyya
  exact Finset.sum_congr rfl (fun x _ => weight_mul_sqrt_eq p0 p1 x)

/-- One minus the Bhattacharyya coefficient is bounded above by Shannon distinguishability,
giving the left inequality of Proposition 5, equation (45), of [FuchsVanDeGraaf1999]. -/
theorem proposition5_45_left (p0 p1 : FinDist X) :
    1 - bhattacharyya p0 p1 ≤ shannonDist p0 p1 := by
  unfold shannonDist
  have hpt : ∀ x ∈ (Finset.univ : Finset X),
      ((p0.prob x + p1.prob x) / 2) * binaryEntropy (p0.prob x / (p0.prob x + p1.prob x)) ≤
      ((p0.prob x + p1.prob x) / 2) *
        (2 * Real.sqrt ((p0.prob x / (p0.prob x + p1.prob x)) *
          (1 - p0.prob x / (p0.prob x + p1.prob x)))) := by
    intro x _
    apply mul_le_mul_of_nonneg_left _ (weight_nonneg p0 p1 x)
    exact binaryEntropy_le_two_sqrt (posterior_mem p0 p1 x).1 (posterior_mem p0 p1 x).2
  have hsum := Finset.sum_le_sum hpt
  rw [sum_weight_mul_sqrt_eq] at hsum
  linarith

/-- Restates the lower bound on Shannon distinguishability by one minus the Bhattacharyya
coefficient from [FuchsVanDeGraaf1999]. -/
theorem proposition5_45_left_conj (p0 p1 : FinDist X) :
    1 - bhattacharyya p0 p1 ≤ shannonDist p0 p1 :=
  proposition5_45_left p0 p1

/-- Proves the lower and upper bounds on Shannon distinguishability in terms of the classical
error probability from Proposition 5, equation (44), of [FuchsVanDeGraaf1999]. -/
theorem proposition5_44 (p0 p1 : FinDist X) :
    1 - binaryEntropy (classicalErrProb p0 p1) ≤ shannonDist p0 p1 ∧
      shannonDist p0 p1 ≤ 1 - 2 * classicalErrProb p0 p1 :=
  ⟨proposition5_44_left p0 p1, proposition5_44_right p0 p1⟩

/-- Collects equation (43), equation (44), and the left inequality of equation (45) from
Proposition 5 of [FuchsVanDeGraaf1999]. -/
theorem proposition5 (p0 p1 : FinDist X) :
    (1 - bhattacharyya p0 p1 ≤ classicalKolmogorov p0 p1 ∧
      classicalKolmogorov p0 p1 ≤ Real.sqrt (1 - (bhattacharyya p0 p1) ^ 2)) ∧
    (1 - binaryEntropy (classicalErrProb p0 p1) ≤ shannonDist p0 p1 ∧
      shannonDist p0 p1 ≤ 1 - 2 * classicalErrProb p0 p1) ∧
    (1 - bhattacharyya p0 p1 ≤ shannonDist p0 p1) :=
  ⟨proposition5_43 p0 p1, proposition5_44 p0 p1, proposition5_45_left p0 p1⟩

end Qatlib.Papers.CryptoDisting99.Equivalence
