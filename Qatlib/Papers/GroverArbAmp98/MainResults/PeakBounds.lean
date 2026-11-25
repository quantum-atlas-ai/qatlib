/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GroverArbAmp98.MainResults.MeasurementTime
public import Qatlib.Papers.GroverArbAmp98.MainResults.TwoMeasurements

@[expose] public section

/-!
# The normalized Grover envelope and its real peak times

The marked and unmarked centered masses together with their mean masses
sum to one for a normalized input. The parallelogram identity expresses
the two rotating masses using those same means. Substituting the actual
dynamics parameters into the cosine model gives the real peak times of
[Biham et al.][BihamEtAl1999].
-/

set_option autoImplicit false

open scoped BigOperators
open Qatlib.Papers.GroverArbAmp98.MainResults
open Qatlib.Papers.GroverArbAmp98.MainResults.Dynamics

namespace Qatlib.Papers.GroverArbAmp98.MainResults

/-- A normalized input gives the baseline in Equation (17) and an upper
envelope bounded by one. -/
theorem normalized_baseline_and_peak {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (x : Amps r m) (hnorm : probMarked x + probUnmarked x = 1) :
    Pav x = 1 - (∑ j, Complex.normSq (x.2 j - lbar x 0)) -
      (1 / 2) * ((m : ℝ) * Complex.normSq (lbar x 0) +
        (r : ℝ) * Complex.normSq (kbar x 0)) ∧ Pmax x ≤ 1 := by
  let means := (m : ℝ) * Complex.normSq (lbar x 0) + (r : ℝ) * Complex.normSq (kbar x 0)
  let unmarkedDev := ∑ j, Complex.normSq (x.2 j - lbar x 0)
  have htotal : varMarked x + unmarkedDev + means = 1 := by
    have hmarked := sum_normSq_centered hr x.1
    have hunmarked := sum_normSq_centered hm x.2
    dsimp only [varMarked, unmarkedDev, means, kbar_zero, lbar_zero]
    unfold probMarked probUnmarked at hnorm
    linarith
  have hscale : Complex.normSq (sC r m) = (r : ℝ) / (m : ℝ) := by
    rw [sC, sReal, Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (by positivity)]
  have hpair :
      (m : ℝ) / 4 * (Complex.normSq (fplus x) + Complex.normSq (fminus x)) = means / 2 := by
    rw [fplus, fminus, Complex.normSq_add, Complex.normSq_sub]
    simp only [means, kbar_zero, lbar_zero, Complex.normSq_mul, Complex.normSq_I,
      one_mul, hscale]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    field_simp
    ring
  have hpav : Pav x = varMarked x + means / 2 := by rw [Pav, hpair]
  have hamp : DeltaP x ≤ means / 2 := by
    rw [← hpair, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    rw [DeltaP, hC, norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) / 2)]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) / 4)
      (sq_nonneg (‖fplus x‖ - ‖fminus x‖))]
  have hdev : 0 ≤ unmarkedDev := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  constructor
  · change Pav x = 1 - unmarkedDev - (1 / 2) * means
    linarith
  · rw [Pmax_eq]
    linarith

/-- The source real peak time computed from the actual oscillation
coefficient and rotation angle. -/
noncomputable def realPeakTime {r m : ℕ} (x : Amps r m) (j : ℕ) : ℝ :=
  (((j : ℝ) + 1 / 2) * Real.pi - (hC x).arg / 2) / omega r m

/-- The real cosine profile of the supplied amplitude dynamics attains
the upper envelope at the source time. -/
theorem real_peak_time_value {r m : ℕ} (x : Amps r m) (j : ℕ)
    (hω : omega r m ≠ 0) :
    MeasurementTime.successAt (Pav x) (DeltaP x)
      (2 * (omega r m * realPeakTime x j + (hC x).arg / 2)) = Pmax x := by
  simpa only [realPeakTime, MeasurementTime.Pmax, Pmax_eq] using
    MeasurementTime.optimal_time_achieves_Pmax
      (Pav x) (DeltaP x) ((hC x).arg / 2) (omega r m) j hω

/-- An actual iteration attains the envelope when its natural-number
iteration count equals the reported real peak time. -/
theorem marked_probability_at_integral_peak {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (x : Amps r m) (j t : ℕ) (hω : omega r m ≠ 0)
    (ht : (t : ℝ) = realPeakTime x j) :
    probMarked (orbit x t) = Pmax x := by
  rw [TwoMeasurements.probMarked_eq_phase r m hr hm, ht]
  have hphase : 2 * omega r m * realPeakTime x j + (hC x).arg =
      2 * (omega r m * realPeakTime x j + (hC x).arg / 2) := by ring
  rw [hphase]
  exact real_peak_time_value x j hω

end Qatlib.Papers.GroverArbAmp98.MainResults
