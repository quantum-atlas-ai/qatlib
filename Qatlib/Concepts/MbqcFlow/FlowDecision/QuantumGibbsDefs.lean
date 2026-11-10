/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

def readoutKraus {D M : ℕ}
    (U : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ) (a o : Fin M) : Operator D :=
  fun i j => U (o,i) (a,j)

end Qatlib.Concepts.MbqcFlow.FlowDecision
