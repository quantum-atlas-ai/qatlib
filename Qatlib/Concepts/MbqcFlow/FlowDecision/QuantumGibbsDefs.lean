/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed

/-!
# Kraus blocks for ancilla readout

Defines `readoutKraus` by fixing the input and output ancilla labels of a joint ancilla-system
matrix. The resulting system operator is the block used to construct ancilla-readout
instruments.

The block representation is part of the standard operator-sum description of measurements in
[NielsenChuang2010].

## Main statements

* `readoutKraus`: the system matrix with entries `U (o, i) (a, j)`.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

/-- The system matrix block obtained by fixing the joint matrix's input ancilla label to `a` and
output ancilla label to `o`. -/
def readoutKraus {D M : ℕ}
    (U : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ) (a o : Fin M) : Operator D :=
  fun i j => U (o,i) (a,j)

end Qatlib.Concepts.MbqcFlow.FlowDecision
