/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.RestartLaw.RestartProfile
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.SearchStopping.RestartLaw

open Qatlib.Concepts.SearchStopping.KnownCount

def Section3OptimalConstantsSubgoal : Prop :=
  ∀ z : ℝ, Real.tan (z / 2) = z → 233112 / 100000 < z → z < 233113 / 100000 →
    8445 / 10000 < Real.sin (z / 2) ^ 2 ∧ Real.sin (z / 2) ^ 2 < 8446 / 10000 ∧
    58278 / 100000 < z / 4 ∧ z / 4 < 58279 / 100000 ∧
    69002 / 100000 < z / (4 * Real.sin (z / 2) ^ 2) ∧
      z / (4 * Real.sin (z / 2) ^ 2) < 69003 / 100000 ∧
    87 / 100 * (Real.pi / 4) < z / (4 * Real.sin (z / 2) ^ 2) ∧
      z / (4 * Real.sin (z / 2) ^ 2) < 22 / 25 * (Real.pi / 4)

end Qatlib.Concepts.SearchStopping.RestartLaw
