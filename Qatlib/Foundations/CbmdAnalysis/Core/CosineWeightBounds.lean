/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.CosinePropagators
import Qatlib.Foundations.CbmdAnalysis.Core.CosineRegulatorNorm
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Cosine weight sums and tail bounds

This module proves absolute summability, inverse-square tail estimates, and logarithmic mass
bounds for cosine sample coefficients. It defines `cosineFiniteWeightMass` and transfers these
estimates to bounded vector-valued samples and their regulator-weighted tails, providing
quantitative weight control for [WangEtAl2026].

## Main statements

* `cosineSampleCoefficient_tail_tsum_le`: an explicit bound on the infinite coefficient-norm
  tail.
* `cosineFiniteWeightMass_le_exp_log`: an exponential-times-logarithmic upper bound on finite
  mass.
* `cosineSample_weighted_tail_norm_le`: the corresponding regulator-weighted vector tail
  estimate.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open scoped BigOperators

/-- For `u > 0`, the inverse-cubic term `2 / (u + 1) ^ 3` is bounded by the telescoping
difference `1 / u ^ 2 - 1 / (u + 1) ^ 2`. -/
private theorem cosine_cubic_le_telescope (u : ℝ) (hu : 0 < u) :
    2 / (u + 1) ^ 3 ≤ 1 / u ^ 2 - 1 / (u + 1) ^ 2 := by
  have hu1 : 0 < u + 1 := by positivity
  apply (le_sub_iff_add_le).mpr
  field_simp
  nlinarith [sq_nonneg u]

/-- For positive parameters, every finite coefficient-norm tail starting at `K + 1` is at most
`γ * τ ^ 2 / (π ^ 3 * (K + 1 / 2) ^ 2)`. -/
theorem cosineSampleCoefficient_tail_sum_range_le {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (K N : ℕ) :
    (∑ j ∈ Finset.range N, ‖cosineSampleCoefficient γ τ (K + 1 + j)‖) ≤
      γ * τ ^ 2 / (Real.pi ^ 3 * ((K : ℝ) + 1 / 2) ^ 2) := by
  let C := γ * τ ^ 2 / Real.pi ^ 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ j ∈ Finset.range N,
      C * (1 / ((K : ℝ) + 1 / 2 + j) ^ 2 - 1 / ((K : ℝ) + 1 / 2 + (j + 1 : ℕ)) ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      have ht := mul_le_mul_of_nonneg_left
        (cosine_cubic_le_telescope ((K : ℝ) + 1 / 2 + j) (by positivity)) hC
      apply (cosineSampleCoefficient_norm_le_cubic hγ hτ (K + 1 + j)).trans
      convert! ht using 1 <;> push_cast <;> dsimp [C] <;> field_simp <;> ring
    _ = C * (1 / ((K : ℝ) + 1 / 2) ^ 2 -
        1 / ((K : ℝ) + 1 / 2 + N) ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub']
      simp only [Nat.cast_zero, add_zero]
    _ ≤ C * (1 / ((K : ℝ) + 1 / 2) ^ 2) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) hC
    _ = _ := by dsimp [C]; field_simp

/-- For positive `γ` and `τ`, the cosine sample coefficient norms form a summable sequence. -/
theorem cosineSampleCoefficient_norm_summable {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) :
    Summable (fun k : ℕ => ‖cosineSampleCoefficient γ τ k‖) := by
  have htail : Summable (fun j : ℕ => ‖cosineSampleCoefficient γ τ (j + 1)‖) :=
    summable_of_sum_range_le (fun _ => norm_nonneg _)
      (by intro N; simpa only [Nat.zero_add, Nat.add_comm 1] using!
        cosineSampleCoefficient_tail_sum_range_le hγ hτ 0 N)
  exact (summable_nat_add_iff 1).mp htail

/-- For positive parameters, the infinite coefficient-norm tail after index `K` is at most `γ *
τ ^ 2 / (π ^ 3 * (K + 1 / 2) ^ 2)`. -/
theorem cosineSampleCoefficient_tail_tsum_le {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (K : ℕ) :
    (∑' j : ℕ, ‖cosineSampleCoefficient γ τ (K + 1 + j)‖) ≤
      γ * τ ^ 2 / (Real.pi ^ 3 * ((K : ℝ) + 1 / 2) ^ 2) :=
  Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _)
    (cosineSampleCoefficient_tail_sum_range_le hγ hτ K)

/-- The sum of the first `N` coefficient norms is at most `(4 / π) * (1 + log N)` for all real
parameters. -/
theorem cosineSampleCoefficient_sum_range_le_log (γ τ : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, ‖cosineSampleCoefficient γ τ k‖) ≤
      (4 / Real.pi) * (1 + Real.log N) := by
  have hs : (∑ k ∈ Finset.range N, ‖cosineSampleCoefficient γ τ k‖) ≤
      (4 / Real.pi) * (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, (4 / Real.pi) * (1 / ((k : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro k _
        apply (cosineSampleCoefficient_norm_le_harmonic γ τ k).trans
        have hk : 0 < (k : ℝ) + 1 / 2 := by positivity
        have hk1 : 0 < (k : ℝ) + 1 := by positivity
        field_simp
        nlinarith
      _ = _ := by
        rw [harmonic, Rat.cast_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        push_cast
        rw [one_div]
  exact hs.trans (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity))

/-- For positive parameters, the total coefficient-norm sum is at most `(4 / π) * (1 + log (2 +
γ * τ ^ 2)) + 1 / π ^ 3`. -/
theorem cosineSampleCoefficient_norm_tsum_le_log {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) :
    (∑' k : ℕ, ‖cosineSampleCoefficient γ τ k‖) ≤
      (4 / Real.pi) * (1 + Real.log (2 + γ * τ ^ 2)) + 1 / Real.pi ^ 3 := by
  let X := γ * τ ^ 2
  let K : ℕ := ⌈X⌉₊
  have hX : 0 < X := by dsimp [X]; positivity
  have hK : X ≤ (K : ℝ) := Nat.le_ceil X
  have hKu : (K : ℝ) < X + 1 := Nat.ceil_lt_add_one hX.le
  have hd : X ≤ ((K : ℝ) + 1 / 2) ^ 2 := by nlinarith [sq_nonneg ((K : ℝ) - 1 / 2)]
  have htail : (∑' j : ℕ, ‖cosineSampleCoefficient γ τ (K + 1 + j)‖) ≤ 1 / Real.pi ^ 3 := by
    apply (cosineSampleCoefficient_tail_tsum_le hγ hτ K).trans
    have hd0 : 0 < ((K : ℝ) + 1 / 2) ^ 2 := by positivity
    apply (div_le_div_iff₀ (mul_pos (pow_pos Real.pi_pos _) hd0) (pow_pos Real.pi_pos _)).mpr
    change X * Real.pi ^ 3 ≤ 1 * (Real.pi ^ 3 * ((K : ℝ) + 1 / 2) ^ 2)
    nlinarith [mul_le_mul_of_nonneg_left hd (pow_nonneg Real.pi_pos.le 3)]
  have hhead := cosineSampleCoefficient_sum_range_le_log γ τ (K + 1)
  have hlog : Real.log (K + 1 : ℕ) ≤ Real.log (2 + X) := by
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have hsplit := (cosineSampleCoefficient_norm_summable hγ hτ).sum_add_tsum_nat_add (K + 1)
  rw [← hsplit]
  simp only [Nat.add_comm _ (K + 1)]
  apply add_le_add _ htail
  exact hhead.trans (mul_le_mul_of_nonneg_left (show 1 + Real.log (K + 1 : ℕ) ≤
    1 + Real.log (2 + γ * τ ^ 2) by dsimp [X] at hlog; linarith) (by positivity))

/-- For positive parameters, one plus the total coefficient-norm sum is at most `16 * log (2 + γ
* τ ^ 2)`. -/
theorem cosineSampleCoefficient_total_mass_le {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) :
    1 + (∑' k : ℕ, ‖cosineSampleCoefficient γ τ k‖) ≤
      16 * Real.log (2 + γ * τ ^ 2) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    simpa only [show (1 - (2 : ℝ)⁻¹) = 1 / 2 by norm_num] using!
        Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 + γ * τ ^ 2) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by nlinarith [sq_nonneg τ]))
  have hπ : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
  have hf : 4 / Real.pi ≤ (4 : ℝ) := (div_le_iff₀ Real.pi_pos).mpr (by nlinarith)
  have hg : 1 / Real.pi ^ 3 ≤ (1 : ℝ) :=
    (div_le_one (pow_pos Real.pi_pos _)).mpr (one_le_pow₀ hπ)
  have hh := cosineSampleCoefficient_norm_tsum_le_log hγ hτ
  have hm := mul_le_mul_of_nonneg_right hf (show 0 ≤ 1 + Real.log (2 + γ * τ ^ 2) by linarith)
  linarith

/-- The regulator norm at one multiplied by one plus the sum of the first `N` sample coefficient
norms. -/
def cosineFiniteWeightMass (γ τ : ℝ) (N : ℕ) : ℝ :=
  ‖cosineRegulator γ τ 1‖ *
    (1 + ∑ k ∈ Finset.range N, ‖cosineSampleCoefficient γ τ k‖)

/-- For positive parameters, the finite cosine weight mass is at most `16 * ‖cosineRegulator γ τ
1‖ * log (2 + γ * τ ^ 2)`. -/
theorem cosineFiniteWeightMass_le {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (N : ℕ) :
    cosineFiniteWeightMass γ τ N ≤
      16 * ‖cosineRegulator γ τ 1‖ * Real.log (2 + γ * τ ^ 2) := by
  have hsum := Summable.sum_le_tsum (Finset.range N) (fun _ _ => norm_nonneg _)
    (cosineSampleCoefficient_norm_summable hγ hτ)
  have hmass := cosineSampleCoefficient_total_mass_le hγ hτ
  unfold cosineFiniteWeightMass
  have h := mul_le_mul_of_nonneg_left
    (show 1 + (∑ k ∈ Finset.range N, ‖cosineSampleCoefficient γ τ k‖) ≤
      16 * Real.log (2 + γ * τ ^ 2) by linarith)
    (norm_nonneg (cosineRegulator γ τ 1))
  convert! h using 1
  ring

/-- For positive parameters, the finite cosine weight mass is at most `16 * exp (τ * sqrt (γ /
2)) * log (2 + γ * τ ^ 2)`. -/
theorem cosineFiniteWeightMass_le_exp_log {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (N : ℕ) :
    cosineFiniteWeightMass γ τ N ≤
      16 * Real.exp (τ * Real.sqrt (γ / 2)) * Real.log (2 + γ * τ ^ 2) := by
  apply (cosineFiniteWeightMass_le hγ hτ N).trans
  apply mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (cosineRegulator_one_norm_le hγ hτ) (by norm_num))
  exact Real.log_nonneg (by nlinarith [sq_nonneg τ])

section Samples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- For positive parameters, numerator values of norm at most one at all sample poles give a
summable sequence of weighted sample norms. -/
theorem cosineSample_norm_summable {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (U : ℂ → E) (hUsample : ∀ k, ‖U (cosineSamplePole γ τ k)‖ ≤ 1) :
    Summable (fun k : ℕ => ‖cosineSample γ τ U k‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => ?_) (cosineSampleCoefficient_norm_summable hγ hτ)
  rw [cosineSample, norm_smul]
  simpa only [mul_one] using! mul_le_mul_of_nonneg_left (hUsample k)
    (norm_nonneg (cosineSampleCoefficient γ τ k))

variable [CompleteSpace E]

/-- For positive parameters, numerator values of norm at most one at all sample poles give a
summable weighted sample sequence. -/
theorem cosineSample_summable {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (U : ℂ → E) (hUsample : ∀ k, ‖U (cosineSamplePole γ τ k)‖ ≤ 1) :
    Summable (cosineSample γ τ U) := (cosineSample_norm_summable hγ hτ U hUsample).of_norm

omit [CompleteSpace E] in

/-- For positive parameters and sample values of norm at most one, the weighted sample tail
after index `K` has norm at most `γ * τ ^ 2 / (π ^ 3 * (K + 1 / 2) ^ 2)`. -/
theorem cosineSample_tail_tsum_norm_le {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (U : ℂ → E) (hUsample : ∀ k, ‖U (cosineSamplePole γ τ k)‖ ≤ 1) (K : ℕ) :
    ‖∑' j : ℕ, cosineSample γ τ U (K + 1 + j)‖ ≤
      γ * τ ^ 2 / (Real.pi ^ 3 * ((K : ℝ) + 1 / 2) ^ 2) := by
  have hn : Summable (fun j : ℕ => ‖cosineSample γ τ U (K + 1 + j)‖) :=
    (cosineSample_norm_summable hγ hτ U hUsample).comp_injective (by intro i j h; omega)
  have hc : Summable (fun j : ℕ => ‖cosineSampleCoefficient γ τ (K + 1 + j)‖) :=
    (cosineSampleCoefficient_norm_summable hγ hτ).comp_injective (by intro i j h; omega)
  apply (norm_tsum_le_tsum_norm hn).trans
  apply (Summable.tsum_le_tsum _ hn hc).trans (cosineSampleCoefficient_tail_tsum_le hγ hτ K)
  intro j
  rw [cosineSample, norm_smul]
  simpa only [mul_one] using! mul_le_mul_of_nonneg_left (hUsample (K + 1 + j))
    (norm_nonneg (cosineSampleCoefficient γ τ (K + 1 + j)))

omit [CompleteSpace E] in

/-- For positive parameters and sample values of norm at most one, the regulator-weighted tail
after index `K` has norm at most `‖cosineRegulator γ τ 1‖ * γ * τ ^ 2 / (π ^ 3 * (K + 1 / 2)
^ 2)`. -/
theorem cosineSample_weighted_tail_norm_le {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (U : ℂ → E) (hUsample : ∀ k, ‖U (cosineSamplePole γ τ k)‖ ≤ 1) (K : ℕ) :
    ‖cosineRegulator γ τ 1 • ∑' j : ℕ, cosineSample γ τ U (K + 1 + j)‖ ≤
      ‖cosineRegulator γ τ 1‖ * γ * τ ^ 2 /
        (Real.pi ^ 3 * ((K : ℝ) + 1 / 2) ^ 2) := by
  rw [norm_smul]
  convert! mul_le_mul_of_nonneg_left (cosineSample_tail_tsum_norm_le hγ hτ U hUsample K)
    (norm_nonneg (cosineRegulator γ τ 1)) using 1
  ring

end Samples
end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
