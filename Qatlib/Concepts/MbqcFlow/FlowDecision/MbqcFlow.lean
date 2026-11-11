/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteGatePhaseBoundary

/-!
# MBQC flow definitions and finite gate boundaries

This import module exposes the definitions in `MbqcFlowCoreDefs` together with the finite gate
phase boundary interface. The available MBQC definitions include `MbqcGraph`, `MbqcHasFlow`, and
`mbqcPatternInstrument`, providing graph and branch semantics for the one-way model
[DanosKashefi2006].

The module contains no additional declarations; its imports make the flow definitions and finite
gate interface available together.

## Main declarations from imports

* `MbqcHasFlow`: existence of a causal flow on an open graph.
* `mbqcFlowDecide`: finite search over flow maps and rank assignments.
* `mbqcPatternInstrument`: an instrument built from pattern branches and a supplied
  trace-preservation proof.

## References

* [Danos and Kashefi, 2006][DanosKashefi2006]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Qatlib
open Qatlib
open Matrix
open scoped Classical ComplexOrder

set_option autoImplicit false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000

open Qatlib
open scoped Classical
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

end Qatlib.Concepts.MbqcFlow.FlowDecision
