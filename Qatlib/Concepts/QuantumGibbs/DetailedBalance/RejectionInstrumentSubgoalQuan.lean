/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.DetailedBalance.RejectionInstrumentSubgoalStat
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.QuantumGibbs.DetailedBalance

open Qatlib

theorem rejectionInstrumentSubgoal : RejectionInstrumentSubgoal :=
  fun I _ _ P hP π hπ =>
    ⟨fun x y => Qatlib.Concepts.WalkSearch.TwoLevelLower.metropolisAcceptance_detailed_balance P hP hπ x y,
     fun a h0 h1 => ⟨Qatlib.Concepts.WalkSearch.TwoLevelLower.metropolisCoin_unitary h0 h1,
       Qatlib.Concepts.WalkSearch.TwoLevelLower.metropolisCoin_accept_prob h0⟩⟩

end Qatlib.Concepts.QuantumGibbs.DetailedBalance
