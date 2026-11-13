/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.NumericError.RatioError
import Qatlib.Papers.LowRankMatrix19.SDPTrace.Lemma627Stat

/-!
# Stability of normalized trace estimates

This module proves `sampling_based_low_rank_lemma_6_27`, the scalar ratio estimate used to
normalize approximate trace quantities in [ChiaEtAl2022]. Relative numerator and denominator
errors of at most `θ / 3`, together with the numerator norm bound, give an absolute ratio error
of at most `θ`.

## Main statements

* `sampling_based_low_rank_lemma_6_27`: Controls the error in a complex ratio for `0 ≤ θ ≤ 1`.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

open Qatlib.Papers.LowRankMatrix19.SDPTrace.Lemma627Spec

namespace Qatlib.Papers.LowRankMatrix19.SDPTrace

/-- For `0 ≤ θ ≤ 1`, a numerator with norm at most `Z` and numerator and denominator errors at
most `(θ / 3) * Z` give a normalized complex ratio error at most `θ` [ChiaEtAl2022]. -/
theorem sampling_based_low_rank_lemma_6_27 :
    ∀ (θ : ℝ) (a a_tilde : ℂ) (Z : ℝ) (Z_tilde : ℂ),
    0 ≤ θ →
    θ ≤ 1 →
    ‖a‖ ≤ Z →
    ‖a - a_tilde‖ ≤ (θ / 3) * Z →
    ‖(Z : ℂ) - Z_tilde‖ ≤ (θ / 3) * Z →
    ‖a_tilde / Z_tilde - a / (Z : ℂ)‖ ≤ θ := by
  exact Qatlib.Foundations.NumericError.RatioError.quotient_error_of_third_budgets

example :
    Lemma627Spec.expected :=
  sampling_based_low_rank_lemma_6_27

end Qatlib.Papers.LowRankMatrix19.SDPTrace
