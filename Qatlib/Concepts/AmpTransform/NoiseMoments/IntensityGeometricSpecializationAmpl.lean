/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseMoments.IntensityGeometricSpecializationStat

/-!
# Normalized intensity moments away from resonance

`normalized_unresonant_moments` evaluates the mean and variance of a shifted character-sum
intensity divided by (M+L)² when y and 2y are nonzero. `intensityGeometricSpecialization_answer`
specializes these formulas to zero and real signal shifts and establishes decay bounds relevant
to the noise analysis of [Cornwell2014].

## Main statements

* `normalized_unresonant_moments`: For y ≠ 0 and 2y ≠ 0, the normalized intensity ‖c+S‖²/T² has
  mean (‖c‖²+L)/T² and variance (L²−L+2L‖c‖²)/T⁴, where T=M+L.
* `intensityGeometricSpecialization_answer`: Proves the normalized signal and noise intensity
  means, variance bounds away from resonance, the stated envelope inequality, and decay of the
  noise mean and variance bound as L grows; see [Cornwell, Corollaries 6 and 8][Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Concepts.SpectralReadout.NoiseStatistics
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.NoiseMoments

/-- For y ≠ 0 and 2y ≠ 0, the normalized intensity ‖c+S‖²/T² has mean (‖c‖²+L)/T² and variance
(L²−L+2L‖c‖²)/T⁴, where T=M+L. -/
theorem normalized_unresonant_moments (N L M : ℕ) [NeZero N] (y : ZMod N)
    (c : ℂ) (hy : y ≠ 0) (hres : 2*y ≠ 0) :
    let T : ℝ := (M+L : ℕ)
    let F := fun ω : Fin L → ZMod N => ‖c + ∑ i, ZMod.stdAddChar (ω i*y)‖^2 / T^2
    let mu := (‖c‖^2 + (L : ℝ))/T^2
    ((N : ℝ)^L)⁻¹ * ∑ ω, F ω = mu ∧
    ((N : ℝ)^L)⁻¹ * ∑ ω, (F ω - mu)^2 =
      ((L : ℝ)^2-L+2*(L : ℝ)*‖c‖^2)/T^4 := by
  (try dsimp only)
  have hm := (noise_sequence_second_moment N L y c 1 hy).2
  have hv := noise_sequence_variance_corrected N L y c 1 hy
  simp only [Complex.ofReal_one, one_mul, one_pow, if_neg hres,
    zero_mul, mul_zero, add_zero] at hm hv
  constructor
  · rw [← Finset.sum_div, ← mul_div_assoc, hm]
  · have he (ω : Fin L → ZMod N) :
        (‖c + ∑ i, ZMod.stdAddChar (ω i*y)‖^2 / ((M+L : ℕ) : ℝ)^2 -
          (‖c‖^2 + (L : ℝ))/((M+L : ℕ) : ℝ)^2)^2 =
        (‖c + ∑ i, ZMod.stdAddChar (ω i*y)‖^2 - (‖c‖^2 + (L : ℝ)))^2 /
          ((M+L : ℕ) : ℝ)^4 := by rw [← sub_div, div_pow]; ring
    simp_rw [he]
    rw [← Finset.sum_div, ← mul_div_assoc, hv]
    congr 1
    ring

/-- Proves the normalized signal and noise intensity means, variance bounds away from resonance,
the stated envelope inequality, and decay of the noise mean and variance bound as L grows;
see [Cornwell, Corollaries 6 and 8][Cornwell2014]. -/
theorem intensityGeometricSpecialization_answer : IntensityGeometricSpecialization := by
  intro N L M _ y hy _hT
  (try dsimp only)
  refine ⟨⟨by positivity, ?_⟩, ?_, ?_, ?_, ?_⟩
  · apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg (M : ℝ)]
  · intro hres
    have h0 := normalized_unresonant_moments N L M y 0 hy hres
    have hM := normalized_unresonant_moments N L M y (M : ℂ) hy hres
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, mul_zero,
      add_zero, Complex.norm_natCast] at h0 hM
    simp only [zero_add]
    refine ⟨h0.1, hM.1, ?_, ?_⟩
    · rw [h0.2]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg (sq_nonneg (M : ℝ)) (Nat.cast_nonneg (α := ℝ) L)]
    · rw [hM.2]
      apply le_of_eq
      congr 1
      ring
  · intro J hJ
    by_cases hj : J = 0
    · subst J
      simp
    · have hjp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
      have htp : (0 : ℝ) < (M+J : ℕ) := by exact_mod_cast hJ
      have hden : 0 < (M : ℝ)*J+(J : ℝ)^2 := by positivity
      rw [Nat.cast_add, one_div, inv_mul_eq_div]
      rw [div_le_div_iff₀ (sq_pos_of_pos (by simpa [Nat.cast_add] using htp)) hden]
      nlinarith [sq_nonneg (M : ℝ), Nat.cast_nonneg (α := ℝ) M,
        mul_nonneg (sq_nonneg (M : ℝ)) hjp.le]
  · apply squeeze_zero' (Filter.Eventually.of_forall (fun J => by positivity)) _
      (noise_intensity_resonance_safe_bounds_vanish M).1
    exact Filter.Eventually.of_forall (fun J =>
      div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (M : ℝ)]) (by positivity))
  · apply squeeze_zero' _ _ (noise_intensity_resonance_safe_bounds_vanish M).2
    · exact Filter.Eventually.of_forall (fun J =>
        div_nonneg (add_nonneg (noise_length_square_sub_nonneg J) (by positivity)) (by positivity))
    · apply Filter.Eventually.of_forall
      intro J
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hbase := noise_length_square_sub_nonneg J
      have hmul := mul_nonneg (sq_nonneg (M : ℝ)) (Nat.cast_nonneg (α := ℝ) J)
      nlinarith

end Qatlib.Concepts.AmpTransform.NoiseMoments
