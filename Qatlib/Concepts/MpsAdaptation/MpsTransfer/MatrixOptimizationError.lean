/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MatrixOptimizationDual

/-!
# Error bounds for finite mixture samplers

This module quantifies the error of capped and approximate-weight samplers used with matrix
optimization families. `Family.capped_l1` identifies the exact ℓ¹ distance to the unbounded
stopped law, including the failure outcome, as twice the remaining rejection mass. The mixture
constructions support the sampling perspective on semidefinite programming in
[BrandaoSvore2017].

`EffectiveMasses` packages nonnegative real masses with rational approximations and an explicit
error modulus. `effective_sampler_l1` combines normalized weight error with component output
errors, and `effective_precision` specializes the normalization estimate at a chosen precision
index.

## Main statements

* `Family.capped_l1`: the exact error due to a finite rejection budget.
* `effective_normalization`: the normalization error for integerized rational masses.
* `effective_sampler_l1`: the sum of weight and component error bounds.
* `effective_precision`: the bound obtained from the supplied error modulus.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.GibbsMetropolis.RationalBath

open Qatlib.Concepts.MpsAdaptation.MpsTransfer.Family
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open Qatlib
open scoped ENNReal Classical

/-- The real-valued probabilities of a probability mass function on a finite type sum to 1. -/
theorem pmf_real_sum {A : Type} [Fintype A] (p : PMF A) : ∑ i, (p i).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun i _ => p.apply_ne_top i)]
  have hs := p.tsum_coe
  rw [tsum_fintype] at hs
  rw [hs, ENNReal.toReal_one]

namespace Family

variable {K D m : ℕ}

/-- Each successful output probability of the capped sampler is the corresponding
stopped-sampler probability multiplied by one minus the rejection mass raised to `fuel`. -/
theorem capped_success_exact (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b) (i : Fin m) :
    ((F.capped w b fuel).map F.cappedValue) (some i) =
      (1-rationalRejectMass w b ^ fuel) * ((F.stopped w b hW hb).map F.value) i := by
  rw [F.capped_some w b fuel hW hb, F.stopped_output]

/-- The ℓ¹ distance between the capped output law and the stopped law embedded through `some`
equals twice the real rejection mass raised to `fuel`. -/
theorem capped_l1 (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b) :
    let C := (F.capped w b fuel).map F.cappedValue
    let P := ((F.stopped w b hW hb).map F.value).map some
    (∑ i : Option (Fin m), |(C i).toReal - (P i).toReal|) =
      2 * (rationalRejectMass w b ^ fuel).toReal := by
  classical
  (try dsimp only)
  have hr : rationalRejectMass w b ≤ 1 :=
    (rational_unbounded_actual_first_stop_law K w b hW hb).1.le
  have hβ : rationalRejectMass w b ^ fuel ≤ 1 := pow_le_one₀ zero_le hr
  rw [Fintype.sum_option, F.capped_none w b fuel hb, map_some_none]
  simp only [ENNReal.toReal_zero, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  have hi (i : Fin m) :
      |(((F.capped w b fuel).map F.cappedValue) (some i)).toReal -
        ((((F.stopped w b hW hb).map F.value).map some) (some i)).toReal| =
      (rationalRejectMass w b ^ fuel).toReal *
        (((F.stopped w b hW hb).map F.value) i).toReal := by
    rw [map_some_apply, F.capped_success_exact w b fuel hW hb,
      ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hβ (by simp), ENNReal.toReal_one]
    rw [show (1 - (rationalRejectMass w b ^ fuel).toReal) *
        (((F.stopped w b hW hb).map F.value) i).toReal -
        (((F.stopped w b hW hb).map F.value) i).toReal =
        -((rationalRejectMass w b ^ fuel).toReal *
          (((F.stopped w b hW hb).map F.value) i).toReal) by ring]
    rw [abs_neg, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
  simp_rw [hi]
  rw [← Finset.mul_sum, pmf_real_sum, mul_one]
  ring

end Family

/-- For nonnegative mixture weights, componentwise ℓ¹ error bounds imply a mixture error bounded
by the weighted sum of those bounds. -/
theorem mixture_component_l1 {K M : ℕ} (w : Fin K → ℝ)
    (q q' : Fin K → Fin M → ℝ) (ν : Fin K → ℝ)
    (hw : ∀ t, 0 ≤ w t) (he : ∀ t, ∑ i, |q' t i-q t i| ≤ ν t) :
    (∑ i, |(∑ t, w t*q' t i)-(∑ t, w t*q t i)|) ≤ ∑ t, w t*ν t := by
  calc
    _ = ∑ i, |∑ t, w t * (q' t i-q t i)| := by
      congr 1; funext i
      rw [← Finset.sum_sub_distrib]
      simp only [mul_sub]
    _ ≤ ∑ i, ∑ t, w t * |q' t i-q t i| := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [abs_mul, abs_of_nonneg (hw _)] using
        (Finset.abs_sum_le_sum_abs (fun t => w t*(q' t i-q t i)) Finset.univ)
    _ = ∑ t, w t * ∑ i, |q' t i-q t i| := by
      rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ ≤ ∑ t, w t * ν t := Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (he t) (hw t)

/-- Nonnegative real masses of positive total mass, equipped with nonnegative rational
approximations of positive total mass, ℓ¹ error bounds, and a modulus achieving error at
most `1 / (k + 1)`. -/
structure EffectiveMasses (K : ℕ) where
  value : Fin K → ℝ
  value_nonneg : ∀ i, 0 ≤ value i
  approximate : ℕ → Fin K → ℚ
  nonneg : ∀ n i, 0 ≤ approximate n i
  positive : ∀ n, 0 < ∑ i, (approximate n i : ℝ)
  total_pos : 0 < ∑ i, value i
  error : ℕ → ℝ
  accuracy : ∀ n, ∑ i, |(approximate n i : ℝ)-value i| ≤ error n
  modulus : ℕ → ℕ
  error_at_modulus : ∀ k, error (modulus k) ≤ 1 / ((k : ℝ)+1)

/-- The ℓ¹ distance between normalized integerized approximate masses and normalized target
masses is at most twice the approximation error divided by the target total mass. -/
theorem effective_normalization {K : ℕ} (E : EffectiveMasses K) (n : ℕ) :
    (∑ i, |(intWeights (E.approximate n) i : ℝ) /
      (weightTotal (intWeights (E.approximate n)) : ℝ) -
      E.value i / (∑ j, E.value j)|) ≤ 2 * E.error n / (∑ j, E.value j) := by
  simp_rw [(intWeights_normalization _ (E.nonneg n) (E.positive n)).2]
  exact (normalized_l1_bound _ _ (fun i => by exact_mod_cast E.nonneg n i)
    (E.positive n) E.total_pos).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (E.accuracy n) (by norm_num)) E.total_pos.le)

/-- The finite ℓ¹ distance satisfies the triangle inequality. -/
theorem l1_triangle {M : ℕ} (a b c : Fin M → ℝ) :
    (∑ i, |a i-c i|) ≤ (∑ i, |a i-b i|) + ∑ i, |b i-c i| := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_sub_le (a i) (b i) (c i)

/-- The exact stopped sampler using integerized approximate masses has ℓ¹ error at most twice
the mass approximation error divided by the target total, plus the target-weighted component
error bounds. -/
theorem effective_sampler_l1 {K D m : ℕ} (F : Family K D m)
    (E : EffectiveMasses K) (n : ℕ) (q : Fin K → Fin m → ℝ) (ν : Fin K → ℝ)
    (he : ∀ t, ∑ i, |F.realOutput t i-q t i| ≤ ν t) :
    let w := intWeights (E.approximate n)
    let hW := (intWeights_normalization _ (E.nonneg n) (E.positive n)).1
    let p := (F.stopped w (blockWidth w) hW (blockWidth_capacity w)).map F.value
    (∑ i, |(p i).toReal - ∑ t, (E.value t / ∑ u, E.value u) * q t i|) ≤
      2*E.error n/(∑ u, E.value u) +
        ∑ t, (E.value t / ∑ u, E.value u) * ν t := by
  (try dsimp only)
  simp_rw [F.stopped_real]
  refine (l1_triangle _
    (fun i => ∑ t, (E.value t / ∑ u, E.value u) * F.realOutput t i) _).trans ?_
  apply add_le_add
  · exact (mixture_weight_l1 _ _ F.realOutput F.realOutput_nonneg F.realOutput_sum).trans
      (effective_normalization E n)
  · exact mixture_component_l1 _ q F.realOutput ν
      (fun t => div_nonneg (E.value_nonneg t) E.total_pos.le) he

/-- At the approximation index selected by the modulus, normalized integerized masses have ℓ¹
error at most `2 / (k + 1)` divided by the target total mass. -/
theorem effective_precision {K : ℕ} (E : EffectiveMasses K) (k : ℕ) :
    (∑ i, |(intWeights (E.approximate (E.modulus k)) i : ℝ) /
      (weightTotal (intWeights (E.approximate (E.modulus k))) : ℝ) -
      E.value i / (∑ j, E.value j)|) ≤
        2 / ((k : ℝ)+1) / (∑ j, E.value j) := by
  refine (effective_normalization E (E.modulus k)).trans ?_
  apply div_le_div_of_nonneg_right _ E.total_pos.le
  simpa only [mul_div, mul_one] using
    mul_le_mul_of_nonneg_left (E.error_at_modulus k) (by norm_num : (0 : ℝ) ≤ 2)

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
