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

def Section3OptimalAngleSubgoal : Prop :=
  ∃! z : ℝ, Real.tan (z / 2) = z ∧ 233112 / 100000 < z ∧ z < 233113 / 100000

end Qatlib.Concepts.SearchStopping.RestartLaw
