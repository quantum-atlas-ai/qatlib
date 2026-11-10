/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.Phi3Universal.Phi3UniversalityTheorem1Quan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.CircuitImpl.Phi3Universal.Theorem1Universality

open Qatlib.Concepts.CircuitImpl.Phi3Universal

theorem theorem1_phi3_universality : Phi3UniversalityTheorem1 :=
  phi3UniversalityTheorem1

end Qatlib.Concepts.CircuitImpl.Phi3Universal.Theorem1Universality
