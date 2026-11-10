/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.SearchStopping.RestartLaw

open Qatlib.Concepts.SearchStopping.KnownCount

noncomputable def restartExpectedIterations (θ j : ℝ) : ℝ :=
  j / (Real.sin ((2 * j + 1) * θ)) ^ 2

end Qatlib.Concepts.SearchStopping.RestartLaw
