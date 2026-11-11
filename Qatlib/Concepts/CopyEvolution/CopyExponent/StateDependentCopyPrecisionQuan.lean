/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.CopyExponent.StateDependentCopyPrecisionStat
import Qatlib.Concepts.CopyEvolution.CopyExponent.CopyStateDependentPrecision

/-!
# State-dependent copy-precision guarantee

`stateDependentCopyPrecision` combines the state-dependent fresh-copy error estimate with the
resource counts for equal-angle steps. The error depends on the distance of the positive input
from ρ tensored with its reference marginal.

This strengthens the precision accounting for density-matrix exponentiation
[LloydMohseniRebentrost2014].

## Main statements

* `stateDependentCopyPrecision`: proves the state-dependent precision and resource
  specification.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.FreshCopyExec.QpeConsumers

namespace Qatlib.Concepts.CopyEvolution.CopyExponent
open Matrix
open scoped ComplexOrder
set_option autoImplicit false

/-- Proves the reset-distance trace-norm error bound and the resource tuple `(n, n, n, 0)` for
equal-angle fresh-copy evolution. The underlying partial-swap method is
[LloydMohseniRebentrost2014]. -/
theorem stateDependentCopyPrecision : StateDependentCopyPrecision := by
  intro D r ρ t n X hρ hX hn
  exact ⟨copy_state_dependent_fresh_global_error D r ρ t n X hρ hX hn,
    by rw [freshCopyResourceCounts_eq, List.length_replicate]⟩
end Qatlib.Concepts.CopyEvolution.CopyExponent
