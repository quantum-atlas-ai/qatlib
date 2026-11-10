/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.ChannelTheory.Stinespring

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

theorem densityOperatorEquivMState_apply {D E : ℕ}
    (T : QuantumChannel D E) (ρ : DensityOperator D) :
    densityOperatorEquivMState E ⟨T.map ρ.val, T.preservesDensity ρ.property⟩ =
      toPhyslib T (densityOperatorEquivMState D ρ) := by
  apply MState.ext_m
  rfl

end Qatlib.Concepts.MbqcFlow.FlowDecision
