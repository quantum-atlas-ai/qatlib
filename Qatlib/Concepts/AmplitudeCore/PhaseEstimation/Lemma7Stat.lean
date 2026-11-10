/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.Sqrt

namespace Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma7Spec
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
