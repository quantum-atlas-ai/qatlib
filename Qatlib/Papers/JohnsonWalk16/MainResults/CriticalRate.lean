/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.WalkReduction.CubicSpectrum.FourBlock

/-!
# Candidate critical rate and a nearby leading eigenvalue

This module verifies arithmetic and spectral properties of the candidate rate `gammaC` for
Johnson-graph search in [Wong2016]. It evaluates the rate at `100`, gives the exact value of
`Er` at that rate, and bounds the distance from a real eigenvalue of `leadingFour` to `-1 - 1 /
(2 * n)`.

## Main statements

* `candidate_rate_100`: evaluates the candidate rate as `69 / 20000`.
* `candidate_r_value`: gives the exact scalar value at the candidate rate.
* `candidate_native_spectrum`: provides an eigenvalue within `54 / n ^ 2` of the stated center
  for `n ≥ 6`.

## References

* [Wong, 2016][Wong2016]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.JohnsonWalk16.MainResults.CriticalRate
open Qatlib.Foundations.WalkReduction.CubicSpectrum

/-- The candidate critical rate at `n = 100` equals `69 / 20000`, evaluating the rate proposed
in [Wong2016]. -/
theorem candidate_rate_100 : gammaC 100 = 69/20000 := gammaC_100

/-- For nonzero `n`, the scalar `Er (gammaC n) n` equals `-1 - 1 / (2 * n) + 21 / (2 * n ^ 2)`. -/
theorem candidate_r_value {n : ℝ} (hn : n ≠ 0) :
    Er (gammaC n) n = -1-1/(2*n)+21/(2*n^2) := Er_at_critical hn

/-- For `n ≥ 6`, the real linear map represented by `leadingFour (gammaC n) n` has an eigenvalue
within `54 / n ^ 2` of `-1 - 1 / (2 * n)`, with a corresponding nonzero eigenvector. See
[Wong2016]. -/
theorem candidate_native_spectrum {n : ℝ} (hn : 6 ≤ n) :
    ∃ lam : ℝ, |lam-(-1-1/(2*n))| ≤ 54/n^2 ∧
      ∃ v : Fin 4 → ℝ, Module.End.HasEigenvector (leadingFour (gammaC n) n).toLin' lam v :=
  leadingFour_nearby hn

end Qatlib.Papers.JohnsonWalk16.MainResults.CriticalRate
