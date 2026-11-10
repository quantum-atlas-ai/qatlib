/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.StationaryFixpointSubgoalStat
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Qatlib

theorem stationaryFixpointSubgoal : StationaryFixpointSubgoal :=
  fun I _ _ P hP π hπ hsum hrev =>
    ⟨Qatlib.Concepts.WalkSearch.TwoLevelLower.normalized_szegedyEmbedState P hP hπ hsum,
      Qatlib.Concepts.WalkSearch.TwoLevelLower.szegedyWalk_fixes_stationary P hP hrev⟩

end Qatlib.Concepts.WalkSearch.FrameSpectral
