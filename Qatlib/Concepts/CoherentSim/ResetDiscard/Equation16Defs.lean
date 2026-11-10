/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation15Stat
import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

noncomputable def ReducedState {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (A : Matrix (J × I) (J × I) ℂ) : Matrix I I ℂ :=
  Matrix.of fun i i' => ∑ a : J, A (a, i) (a, i')

noncomputable def vecOuter {I : Type*} [Fintype I] [DecidableEq I] (v : QState I) : Matrix I I ℂ :=
  Matrix.of fun i i' => v i * (starRingEnd ℂ) (v i')
end Qatlib.Concepts.CoherentSim.ResetDiscard
