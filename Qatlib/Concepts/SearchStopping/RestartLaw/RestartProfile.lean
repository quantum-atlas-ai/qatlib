/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal

/-!
# Continuous Grover restart cost profile

Defines `restartExpectedIterations`, the real-valued profile `j / sin²((2j + 1)θ)` used to study
Grover restart costs. This profile permits differentiation with respect to a real iteration
parameter. For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `restartExpectedIterations`: The real-valued restart cost profile `j / Real.sin ((2 * j + 1) *
  θ) ^ 2`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.SearchStopping.RestartLaw

open Qatlib.Concepts.SearchStopping.KnownCount

/-- The real-valued restart cost profile `j / Real.sin ((2 * j + 1) * θ) ^ 2`. -/
noncomputable def restartExpectedIterations (θ j : ℝ) : ℝ :=
  j / (Real.sin ((2 * j + 1) * θ)) ^ 2

end Qatlib.Concepts.SearchStopping.RestartLaw
