/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.Basic
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Expanded Grover circuit definitions

`DiffusionCircuit` expresses diffusion as Hadamard, zero-phase reflection, and Hadamard.
`ExpandedStep` adds a preceding oracle query, and `ExpandedCircuit` repeats this expanded step.

For the mathematical background, see [Grover1997].

## Main statements

* `ExpandedCircuit`: The circuit repeating `ExpandedStep n` exactly j times.

## References

* [Grover, 1997][Grover1997]
-/

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- The three-gate circuit consisting of Hadamard, zero-phase reflection, and Hadamard on an
n-qubit register. -/
noncomputable def DiffusionCircuit (n : ℕ) : Circuit (Reg n) :=
  [Step.gate (HadamardN n), Step.gate (ZeroPhaseReflection n), Step.gate (HadamardN n)]

/-- One expanded Grover step, comprising an oracle query followed by `DiffusionCircuit n`. -/
noncomputable def ExpandedStep (n : ℕ) : Circuit (Reg n) :=
  Step.query :: DiffusionCircuit n

/-- The circuit repeating `ExpandedStep n` exactly j times. -/
noncomputable def ExpandedCircuit (n j : ℕ) : Circuit (Reg n) :=
  RepeatCircuit (ExpandedStep n) j
end Qatlib.Concepts.SearchStopping.KnownCount
