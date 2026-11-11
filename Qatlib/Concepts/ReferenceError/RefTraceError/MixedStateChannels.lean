/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel

/-!
# Mixed states and quantum channels

This module brings together mixed-state operators and bundled quantum channels as a common
import for reference-error developments. The imported `IsDensityOperator` predicate describes
positive semidefinite unit-trace matrices, while `QuantumChannel` packages completely positive
trace-preserving maps, following the finite-dimensional framework of [Watrous2018].

## Main definitions

* `IsDensityOperator`: the imported density operator predicate.
* `QuantumChannel`: the imported bundled channel type.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
