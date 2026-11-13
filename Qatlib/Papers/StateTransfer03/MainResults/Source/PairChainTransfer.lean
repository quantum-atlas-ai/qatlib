/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StateTransfer03.MainResults.Defs

/-!
# Perfect transfer for two- and three-vertex paths

Explicit path weights, eigenvalues, and complex phase identities give closed formulas for
`pathSpectralAmplitude` on two and three vertices. The formulas evaluate to unit-norm amplitudes
at `π / 2` and `π / sqrt 2`, respectively, establishing spectral perfect transfer. See
[ChristandlEtAl2004].

## Main statements

* `pathSpectralAmplitude_two`: the two-vertex amplitude is `-i sin t`.
* `pathSpectralAmplitude_three`: the three-vertex amplitude is `-sin² (t / sqrt 2)`.
* `chain_perfect_transfer_two_three`: both base paths possess spectral perfect transfer.

## References

* [Christandl et al., 2004][ChristandlEtAl2004]
-/

namespace Qatlib.Papers.StateTransfer03.MainResults.Source

open scoped BigOperators
open Qatlib.Papers.StateTransfer03.MainResults.Defs

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

/-- The sine of `2π / 3` is `sqrt 3 / 2`. -/
private lemma sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
    Real.sin_pi_div_three]

/-- The sine of `4π / 3` is `-sqrt 3 / 2`. -/
private lemma sin_four_pi_div_three : Real.sin (4 * Real.pi / 3) = -Real.sqrt 3 / 2 := by
  rw [show 4 * Real.pi / 3 = Real.pi / 3 + Real.pi by ring, Real.sin_add_pi,
    Real.sin_pi_div_three]
  ring

/-- The sine of `3π / 4` is `sqrt 2 / 2`. -/
private lemma sin_three_pi_div_four : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
  rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.sin_pi_sub,
    Real.sin_pi_div_four]

/-- The sine of `9π / 4` is `sqrt 2 / 2`. -/
private lemma sin_nine_pi_div_four : Real.sin (9 * Real.pi / 4) = Real.sqrt 2 / 2 := by
  rw [show 9 * Real.pi / 4 = Real.pi / 4 + 2 * Real.pi by ring, Real.sin_add_two_pi,
    Real.sin_pi_div_four]

/-- The cosine of `2π / 3` is `-1 / 2`. -/
private lemma cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]
  norm_num

/-- The cosine of `3π / 4` is `-sqrt 2 / 2`. -/
private lemma cos_three_pi_div_four : Real.cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
  rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_four]
  ring

/-- The sine of `3π / 2` is `-1`. -/
private lemma sin_three_pi_div_two : Real.sin (3 * Real.pi / 2) = -1 := by
  rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi,
    Real.sin_pi_div_two]

/-- The endpoint weight at index zero for the two-vertex path is `1 / 2`. -/
private lemma pathWeight_two_zero : pathWeight 2 0 = 1 / 2 := by
  unfold pathWeight
  norm_num
  rw [sin_two_pi_div_three]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

/-- The endpoint weight at index one for the two-vertex path is `-1 / 2`. -/
private lemma pathWeight_two_one : pathWeight 2 1 = -1 / 2 := by
  unfold pathWeight
  norm_num
  rw [sin_two_pi_div_three, sin_four_pi_div_three]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

/-- The eigenvalue at index zero for the two-vertex path is one. -/
private lemma pathEigenvalue_two_zero : pathEigenvalue 2 0 = 1 := by
  unfold pathEigenvalue
  norm_num [Real.cos_pi_div_three]

/-- The eigenvalue at index one for the two-vertex path is minus one. -/
private lemma pathEigenvalue_two_one : pathEigenvalue 2 1 = -1 := by
  unfold pathEigenvalue
  norm_num
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]
  norm_num

/-- The endpoint weight at index zero for the three-vertex path is `1 / 4`. -/
private lemma pathWeight_three_zero : pathWeight 3 0 = 1 / 4 := by
  unfold pathWeight
  norm_num
  rw [sin_three_pi_div_four]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The endpoint weight at index one for the three-vertex path is `-1 / 2`. -/
private lemma pathWeight_three_one : pathWeight 3 1 = -1 / 2 := by
  unfold pathWeight
  norm_num
  rw [show 2 * Real.pi / 4 = Real.pi / 2 by ring, Real.sin_pi_div_two,
    show 6 * Real.pi / 4 = 3 * Real.pi / 2 by ring, sin_three_pi_div_two]
  norm_num

/-- The endpoint weight at index two for the three-vertex path is `1 / 4`. -/
private lemma pathWeight_three_two : pathWeight 3 2 = 1 / 4 := by
  unfold pathWeight
  norm_num
  rw [sin_three_pi_div_four, sin_nine_pi_div_four]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The eigenvalue at index zero for the three-vertex path is `sqrt 2`. -/
private lemma pathEigenvalue_three_zero : pathEigenvalue 3 0 = Real.sqrt 2 := by
  unfold pathEigenvalue
  norm_num [Real.cos_pi_div_four]
  ring

/-- The eigenvalue at index one for the three-vertex path is zero. -/
private lemma pathEigenvalue_three_one : pathEigenvalue 3 1 = 0 := by
  unfold pathEigenvalue
  norm_num
  rw [show 2 * Real.pi / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two]

/-- The eigenvalue at index two for the three-vertex path is `-sqrt 2`. -/
private lemma pathEigenvalue_three_two : pathEigenvalue 3 2 = -Real.sqrt 2 := by
  unfold pathEigenvalue
  norm_num
  rw [cos_three_pi_div_four]
  ring

/-- The phase at real energy `E` equals `cos (E * t) - i sin (E * t)`. -/
private lemma phase_of_real (E t : ℝ) :
    phase E t = (Real.cos (E * t) : ℂ) - (Real.sin (E * t) : ℂ) * Complex.I := by
  unfold phase
  have h : -((Complex.I) * (t : ℂ) * ((E : ℝ) : ℂ)) = ((-(E * t) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Real.cos_neg, Real.sin_neg]
  ring

/-- The phase at energy one equals `cos t - i sin t`. -/
private lemma phase_one (t : ℝ) :
    phase 1 t = (Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I := by
  simpa using phase_of_real 1 t

/-- The phase at energy minus one equals `cos t + i sin t`. -/
private lemma phase_neg_one (t : ℝ) :
    phase (-1) t = (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := by
  have h := phase_of_real (-1) t
  rw [show (-1 : ℝ) * t = -t by ring] at h
  rw [h]
  simp [Real.cos_neg, Real.sin_neg]

/-- The phase at energy `sqrt 2` equals `cos (sqrt 2 * t) - i sin (sqrt 2 * t)`. -/
private lemma phase_sqrt_two (t : ℝ) :
    phase (Real.sqrt 2) t =
      (Real.cos (Real.sqrt 2 * t) : ℂ) - (Real.sin (Real.sqrt 2 * t) : ℂ) * Complex.I := by
  simpa using phase_of_real (Real.sqrt 2) t

/-- The phase at energy `-sqrt 2` equals `cos (sqrt 2 * t) + i sin (sqrt 2 * t)`. -/
private lemma phase_neg_sqrt_two (t : ℝ) :
    phase (-Real.sqrt 2) t =
      (Real.cos (Real.sqrt 2 * t) : ℂ) + (Real.sin (Real.sqrt 2 * t) : ℂ) * Complex.I := by
  have h := phase_of_real (-Real.sqrt 2) t
  rw [show (-Real.sqrt 2) * t = -(Real.sqrt 2 * t) by ring] at h
  rw [h]
  simp [Real.cos_neg, Real.sin_neg]

/-- The phase at zero energy is one for every time. -/
private lemma phase_zero (t : ℝ) : phase 0 t = 1 := by
  unfold phase
  simp

/-- The endpoint spectral amplitude of the two-vertex path is `-i sin t`. See
[ChristandlEtAl2004]. -/
theorem pathSpectralAmplitude_two (t : ℝ) :
    pathSpectralAmplitude 2 t = -Complex.I * (Real.sin t : ℂ) := by
  rw [pathSpectralAmplitude, spectralAmplitude, Fin.sum_univ_two]
  rw [pathWeight_two_zero, pathWeight_two_one, pathEigenvalue_two_zero,
    pathEigenvalue_two_one, phase_one, phase_neg_one]
  push_cast
  ring

/-- The endpoint spectral amplitude of the three-vertex path is `-sin² (t / sqrt 2)`. See
[ChristandlEtAl2004]. -/
theorem pathSpectralAmplitude_three (t : ℝ) :
    pathSpectralAmplitude 3 t = -(((Real.sin (t / Real.sqrt 2)) ^ 2 : ℝ) : ℂ) := by
  rw [pathSpectralAmplitude, spectralAmplitude, Fin.sum_univ_three]
  rw [pathWeight_three_zero, pathWeight_three_one, pathWeight_three_two,
    pathEigenvalue_three_zero, pathEigenvalue_three_one, pathEigenvalue_three_two,
    phase_sqrt_two, phase_zero, phase_neg_sqrt_two]
  have hc : Real.cos (Real.sqrt 2 * t) =
      1 - 2 * Real.sin (Real.sqrt 2 * t / 2) ^ 2 := by
    have h := Real.cos_two_mul_eq_one_sub (Real.sqrt 2 * t / 2)
    rwa [show 2 * (Real.sqrt 2 * t / 2) = Real.sqrt 2 * t by ring] at h
  have harg : Real.sqrt 2 * t / 2 = t / Real.sqrt 2 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [div_eq_div_iff (by positivity) (by positivity)]
    calc Real.sqrt 2 * t * Real.sqrt 2 = (Real.sqrt 2 * Real.sqrt 2) * t := by ring
      _ = 2 * t := by rw [h2]
      _ = t * 2 := by ring
  rw [hc, harg]
  push_cast
  ring

/-- The two-vertex path spectral amplitude at time `π / 2` is `-i`. -/
theorem pathSpectralAmplitude_two_perfect_time :
    pathSpectralAmplitude 2 (Real.pi / 2) = -Complex.I := by
  rw [pathSpectralAmplitude_two, Real.sin_pi_div_two]
  simp

/-- The three-vertex path spectral amplitude at time `π / sqrt 2` is `-1`. -/
theorem pathSpectralAmplitude_three_perfect_time :
    pathSpectralAmplitude 3 (Real.pi / Real.sqrt 2) = -1 := by
  rw [pathSpectralAmplitude_three]
  have ht : Real.pi / Real.sqrt 2 / Real.sqrt 2 = Real.pi / 2 := by
    rw [div_div, Real.mul_self_sqrt (by norm_num)]
  rw [ht, Real.sin_pi_div_two]
  norm_num

/-- The two-vertex path endpoint spectral data possess perfect transfer. See
[ChristandlEtAl2004]. -/
theorem perfect_transfer_two_spectral :
    SpectralPerfectTransfer (pathEigenvalue 2) (fun k => (pathWeight 2 k : ℂ)) := by
  refine ⟨Real.pi / 2, by positivity, ?_⟩
  change ‖pathSpectralAmplitude 2 (Real.pi / 2)‖ = 1
  rw [pathSpectralAmplitude_two_perfect_time]
  simp

/-- The three-vertex path endpoint spectral data possess perfect transfer. See
[ChristandlEtAl2004]. -/
theorem perfect_transfer_three_spectral :
    SpectralPerfectTransfer (pathEigenvalue 3) (fun k => (pathWeight 3 k : ℂ)) := by
  refine ⟨Real.pi / Real.sqrt 2, by positivity, ?_⟩
  change ‖pathSpectralAmplitude 3 (Real.pi / Real.sqrt 2)‖ = 1
  rw [pathSpectralAmplitude_three_perfect_time]
  norm_num

/-- The two- and three-vertex path endpoint spectral data both possess perfect transfer. See
[ChristandlEtAl2004]. -/
theorem chain_perfect_transfer_two_three :
    SpectralPerfectTransfer (pathEigenvalue 2) (fun k => (pathWeight 2 k : ℂ)) ∧
      SpectralPerfectTransfer (pathEigenvalue 3) (fun k => (pathWeight 3 k : ℂ)) :=
  ⟨perfect_transfer_two_spectral, perfect_transfer_three_spectral⟩

end

end Qatlib.Papers.StateTransfer03.MainResults.Source
