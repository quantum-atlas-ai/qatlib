/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma7Stat

/-!
# Converting phase error to amplitude error

`zoo_amplitude_estimation_angle_error` bounds the error in a squared sine amplitude by a linear
term involving `sqrt (a * (1 - a))` and a quadratic phase error term. The supporting lemmas give
an exact trigonometric expansion and a displacement bound valid for arbitrary real angles. See
[BrassardEtAl2002] for background.

## Main statements

* `zoo_amplitude_estimation_angle_error`: If the phase error is at most nonnegative `ε` under
  the stated angle hypotheses, the amplitude error is at most `2 * ε * sqrt (a * (1 - a)) +
  ε^2`, as in [Brassard et al., Lemma 7][BrassardEtAl2002].

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

namespace Qatlib.Concepts.AmplitudeCore.PhaseEstimation

/-- Expands the change in squared sine under displacement `d` into a double angle term and a
squared sine displacement term. -/
lemma zoo_amplitude_estimation_angle_error_expansion (θ d : ℝ) :
    Real.sin (θ + d) ^ 2 - Real.sin θ ^ 2 =
      (Real.sin θ * Real.cos θ) * Real.sin (2 * d) +
        (1 - 2 * Real.sin θ ^ 2) * Real.sin d ^ 2 := by
  rw [Real.sin_add, Real.sin_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq d,
    mul_nonneg (sq_nonneg (Real.sin θ)) (sq_nonneg (Real.sin d))]

/-- The square root of `sin θ^2 * (1 - sin θ^2)` is `|sin θ * cos θ|`. -/
lemma zoo_amplitude_estimation_angle_error_sqrt (θ : ℝ) :
    Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) =
      |Real.sin θ * Real.cos θ| := by
  have hc : 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hc, ← mul_pow, Real.sqrt_sq_eq_abs]

/-- The squared sine displacement error is at most `2 * |d| * sqrt (sin θ^2 * (1 - sin θ^2)) +
d^2`. -/
lemma zoo_amplitude_estimation_angle_error_displacement (θ d : ℝ) :
    |Real.sin (θ + d) ^ 2 - Real.sin θ ^ 2| ≤
      2 * |d| * Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) + d ^ 2 := by
  have hc : |1 - 2 * Real.sin θ ^ 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.sin θ)]
  have hs : |Real.sin (2 * d)| ≤ 2 * |d| := by
    simpa [abs_mul] using (Real.abs_sin_le_abs (x := 2 * d))
  rw [zoo_amplitude_estimation_angle_error_expansion,
    zoo_amplitude_estimation_angle_error_sqrt]
  calc
    _ ≤ |Real.sin θ * Real.cos θ| * |Real.sin (2 * d)| +
        |1 - 2 * Real.sin θ ^ 2| * Real.sin d ^ 2 := by
      have ht := abs_add_le ((Real.sin θ * Real.cos θ) * Real.sin (2 * d))
        ((1 - 2 * Real.sin θ ^ 2) * Real.sin d ^ 2)
      rw [abs_mul (Real.sin θ * Real.cos θ),
        abs_mul (1 - 2 * Real.sin θ ^ 2),
        abs_of_nonneg (sq_nonneg (Real.sin d))] at ht
      exact ht
    _ ≤ |Real.sin θ * Real.cos θ| * (2 * |d|) + 1 * Real.sin d ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hs (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hc (sq_nonneg _))
    _ ≤ _ := by nlinarith [(Real.sin_sq_le_sq (x := d))]

/-- If the phase error is at most nonnegative `ε` under the stated angle hypotheses, the
amplitude error is at most `2 * ε * sqrt (a * (1 - a)) + ε^2`, as in [Brassard et al., Lemma
7][BrassardEtAl2002]. -/
theorem zoo_amplitude_estimation_angle_error :
    ∀ (a a_tilde theta theta_tilde ε : ℝ),
      a = Real.sin theta ^ 2 →
      a_tilde = Real.sin theta_tilde ^ 2 →
      0 ≤ theta → theta ≤ 2 * Real.pi →
      0 ≤ theta_tilde → theta_tilde ≤ 2 * Real.pi →
      0 ≤ ε →
      |theta_tilde - theta| ≤ ε →
      |a_tilde - a| ≤ 2 * ε * Real.sqrt (a * (1 - a)) + ε ^ 2 := by
  intro a a_tilde theta theta_tilde ε ha hat _ _ _ _ he hd
  subst a
  subst a_tilde
  have hb := zoo_amplitude_estimation_angle_error_displacement theta (theta_tilde - theta)
  rw [add_sub_cancel] at hb
  have hsq : (theta_tilde - theta) ^ 2 ≤ ε ^ 2 := by
    nlinarith [sq_abs (theta_tilde - theta), abs_nonneg (theta_tilde - theta)]
  have hm := mul_le_mul_of_nonneg_right hd
    (Real.sqrt_nonneg (Real.sin theta ^ 2 * (1 - Real.sin theta ^ 2)))
  nlinarith

example : Lemma7Spec.expected :=
  zoo_amplitude_estimation_angle_error

end Qatlib.Concepts.AmplitudeCore.PhaseEstimation
