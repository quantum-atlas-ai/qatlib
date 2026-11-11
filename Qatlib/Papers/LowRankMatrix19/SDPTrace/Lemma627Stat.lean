/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic

/-!
# Specification of the normalized trace ratio bound

This module packages the scalar normalized-ratio estimate as the proposition `expected`. It
records the numerator norm and relative approximation hypotheses needed for the trace-estimation
step of [ChiaEtAl2022].

## Main statements

* `expected`: States the universally quantified ratio-error bound with numerator and denominator
  errors at most `(θ / 3) * Z`.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

namespace Qatlib.Papers.LowRankMatrix19.SDPTrace.Lemma627Spec
/-- The proposition that, for `0 ≤ θ ≤ 1`, a numerator bounded in norm by `Z` and numerator and
denominator errors at most `(θ / 3) * Z` yield ratio error at most `θ`. -/
def expected : Prop :=
  (∀ (θ : ℝ) (a a_tilde : ℂ) (Z : ℝ) (Z_tilde : ℂ),
  0 ≤ θ →
  θ ≤ 1 →
  ‖a‖ ≤ Z →
  ‖a - a_tilde‖ ≤ (θ / 3) * Z →
  ‖(Z : ℂ) - Z_tilde‖ ≤ (θ / 3) * Z →
  ‖a_tilde / Z_tilde - a / (Z : ℂ)‖ ≤ θ)
end Qatlib.Papers.LowRankMatrix19.SDPTrace.Lemma627Spec
