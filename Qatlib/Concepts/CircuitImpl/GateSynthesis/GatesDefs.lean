/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.GateSynthesis.GateCountsDefs

/-!
# Gate-synthesis budget definitions

This module defines the public numerical interfaces `instructionBudget`, `twoLevelCount`, and
`primitiveBudget` by reusing the corresponding Section 8 accounting quantities. These counts
organize the elementary-gate synthesis budgets associated with [BarencoEtAl1995].

## Main definitions

* `instructionBudget`: the per-instruction operation cost.
* `twoLevelCount`: the Section 8 two-level count.
* `primitiveBudget`: the product budget for primitive operations.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.CircuitImpl.GateSynthesis

open Qatlib
open Qatlib.Concepts.CircuitImpl.GateSynthesis

set_option autoImplicit false

/-- The public instruction-budget interface, defined as `section8InstructionCost n`. -/
def instructionBudget (n : ℕ) : ℕ := section8InstructionCost n

/-- The public two-level count interface, defined as `section8TwoLevelCount n`. -/
def twoLevelCount (n : ℕ) : ℕ := section8TwoLevelCount n

/-- The public primitive-budget interface, defined as `section8PrimitiveBudget n`. -/
def primitiveBudget (n : ℕ) : ℕ := section8PrimitiveBudget n

end Qatlib.Concepts.CircuitImpl.GateSynthesis
