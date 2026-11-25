/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SearchStopping.RestartLaw.Section3RestartExpectedSubgoal

@[expose] public section

/-!
# Mean iteration count in the random-search model

Section 4 draws a fresh parameter vector on each independent trial. A trial
lands in the acceptable region with probability `γ`. The first successful
trial is one-based, and each trial contributes one iteration to the cost.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMLBoolean13.MainResults

open Qatlib.Concepts.SearchStopping.RestartLaw

/-- Random search with independent per-trial success probability `γ` has mean `1 / γ`. -/
theorem random_mean (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ((1 - γ)^n * γ)) = 1 / γ := by
  simpa only [mul_one] using geometric_restart_expectation γ 1 hγ hγ1

end Qatlib.Papers.QMLBoolean13.MainResults
