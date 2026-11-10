/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DiamondQdrift.FairQdrift.MixtureExpectationSubgoalStat
set_option warningAsError false

open Qatlib.Concepts.ReferenceError.RefTraceError

namespace Qatlib.Concepts.DiamondQdrift.FairQdrift

open Qatlib

theorem mixtureExpectationSubgoal : MixtureExpectationSubgoal :=
  fun _J _ _ _D d U hU _ρ hρ => Qatlib.Concepts.ReferenceError.RefTraceError.channelMixture_maps_density d U hU hρ

end Qatlib.Concepts.DiamondQdrift.FairQdrift
