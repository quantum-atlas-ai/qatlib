/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.GateSynthesis.GateCountsDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.CircuitImpl.GateSynthesis

open Qatlib
open Qatlib.Concepts.CircuitImpl.GateSynthesis

set_option autoImplicit false

def instructionBudget (n : ℕ) : ℕ := section8InstructionCost n

def twoLevelCount (n : ℕ) : ℕ := section8TwoLevelCount n

def primitiveBudget (n : ℕ) : ℕ := section8PrimitiveBudget n

end Qatlib.Concepts.CircuitImpl.GateSynthesis
