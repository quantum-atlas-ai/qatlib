/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic

/-!
# Specification of the amplified Fourier sine bound

`expected` states the geometric quotient identity and its `M^2` bound for a Fourier dimension
`2^n`. The quotient is evaluated at positive progression length and period with a nonzero
Fourier residue. See [Cornwell2014] for background.

## Main statements

* `expected`: The proposition equating the geometric quotient squared norm to its sine quotient
  and bounding it by `M^2` under the nonzero residue hypotheses.

## References

* [Cornwell, 2014][Cornwell2014]
-/

namespace Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma18Spec
/-- The proposition equating the geometric quotient squared norm to its sine quotient and
bounding it by `M^2` under the nonzero residue hypotheses. -/
def expected : Prop :=
  (∀ (n : ℕ),
  let N : ℕ := 2 ^ n;
  ∀ (M P : ℕ) (y : Fin N),
    0 < M →
    0 < P →
    (P * y.val) % N ≠ 0 →
    let ω : ℂ := Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I);
    ‖(1 - ω ^ (M * P * y.val)) / (1 - ω ^ (P * y.val))‖ ^ 2 =
      (Real.sin (Real.pi * (M : ℝ) * (P : ℝ) * (y.val : ℝ) / (N : ℝ))) ^ 2 /
        (Real.sin (Real.pi * (P : ℝ) * (y.val : ℝ) / (N : ℝ))) ^ 2 ∧
    (Real.sin (Real.pi * (M : ℝ) * (P : ℝ) * (y.val : ℝ) / (N : ℝ))) ^ 2 /
        (Real.sin (Real.pi * (P : ℝ) * (y.val : ℝ) / (N : ℝ))) ^ 2 ≤
      (M : ℝ) ^ 2)
end Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma18Spec
