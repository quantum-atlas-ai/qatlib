/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolution

/-!
# Copy-evolution resource measures

This module defines two resource measures used for copy-evolution consumers. `qpePeakSpace`
counts the finite basis size of the label, Boolean, and system registers, while `sourceBitTime`
sums instruction-description lengths.

The mathematical background is described in [LloydMohseniRebentrost2014].

## Main statements

* `qpePeakSpace`: the phase-estimation basis size.
* `sourceBitTime`: total source-description bit length.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.WalkFind.SearchAlgorithm

namespace Qatlib.Concepts.RandCompile.ChannelBudget

open Matrix
open Qatlib
open scoped ComplexOrder BigOperators Classical Matrix.Norms.L2Operator

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- The phase-estimation workspace basis size `M * 2 * D`. -/
def qpePeakSpace (D M : ℕ) : ℕ := M * 2 * D

/-- The sum of the bit lengths of the source descriptions of all instructions in a program. -/
noncomputable def sourceBitTime (cs : List SourceCode) : ℕ :=
  (cs.map (fun g => (sourceDescription g).length)).sum

end Qatlib.Concepts.RandCompile.ChannelBudget
