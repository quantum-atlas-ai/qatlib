/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.NumericError.RatioError
import Qatlib.Papers.LowRankMatrix19.SDPTrace.Lemma627Stat
set_option warningAsError false

open Qatlib.Papers.LowRankMatrix19.SDPTrace.Lemma627Spec

namespace Qatlib.Papers.LowRankMatrix19.SDPTrace

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
