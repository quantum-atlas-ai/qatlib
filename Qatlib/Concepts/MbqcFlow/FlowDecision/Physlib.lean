/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels

/-!
# Compatibility of density states and Physlib channels

Proves that the density-state equivalence `densityOperatorEquivMState` commutes with
quantum-channel application through `toPhyslib`. This connects Qatlib's matrix-based channel
action with Physlib's mixed-state representation.

The underlying density-operator and channel formalism is described in [Watrous2018].

## Main statements

* `densityOperatorEquivMState_apply`: compatibility of state conversion with channel action.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.ChannelTheory.Stinespring

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

/-- Converting the output of a Qatlib quantum channel to a Physlib mixed state equals applying
the converted channel to the converted input state. -/
theorem densityOperatorEquivMState_apply {D E : ℕ}
    (T : QuantumChannel D E) (ρ : DensityOperator D) :
    densityOperatorEquivMState E ⟨T.map ρ.val, T.preservesDensity ρ.property⟩ =
      toPhyslib T (densityOperatorEquivMState D ρ) := by
  apply MState.ext_m
  rfl

end Qatlib.Concepts.MbqcFlow.FlowDecision
