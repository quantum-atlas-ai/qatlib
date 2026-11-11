/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.Sqrt

/-!
# Specification of the amplitude error bound

`expected` relates two squared sine amplitudes to their phase difference. A phase approximation
within `ε` gives the usual linear plus quadratic amplitude error bound. See [BrassardEtAl2002]
for background.

## Main statements

* `expected`: The proposition that phase error at most nonnegative `ε` gives amplitude error at
  most `2 * ε * sqrt (a * (1 - a)) + ε^2` under the stated phase range assumptions.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

namespace Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma7Spec
/-- The proposition that phase error at most nonnegative `ε` gives amplitude error at most `2 *
ε * sqrt (a * (1 - a)) + ε^2` under the stated phase range assumptions. -/
def expected : Prop :=
  (∀ (a a_tilde theta theta_tilde ε : ℝ),
  a = Real.sin theta ^ 2 →
  a_tilde = Real.sin theta_tilde ^ 2 →
  0 ≤ theta → theta ≤ 2 * Real.pi →
  0 ≤ theta_tilde → theta_tilde ≤ 2 * Real.pi →
  0 ≤ ε →
  |theta_tilde - theta| ≤ ε →
  |a_tilde - a| ≤ 2 * ε * Real.sqrt (a * (1 - a)) + ε ^ 2)
end Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma7Spec
