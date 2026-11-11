/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.StationaryFixpointSubgoalStat

/-!
# Reversible states fixed by the Szegedy walk

The theorem `stationaryFixpointSubgoal` proves that embedding a nonnegative normalized
reversible distribution produces a normalized state fixed by the Szegedy walk. The result
connects classical detailed balance with a quantum walk fixed state. The quantum walk spectral
framework is developed in [Szegedy2004].

## Main statements

* `stationaryFixpointSubgoal`: Normalization and invariance of a reversible embedded state.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Qatlib

/-- For a transition matrix and a nonnegative normalized reversible distribution, the Szegedy
embedded state is normalized and fixed by the walk [Szegedy2004]. -/
theorem stationaryFixpointSubgoal : StationaryFixpointSubgoal :=
  fun I _ _ P hP π hπ hsum hrev =>
    ⟨Qatlib.Concepts.WalkSearch.TwoLevelLower.normalized_szegedyEmbedState P hP hπ hsum,
      Qatlib.Concepts.WalkSearch.TwoLevelLower.szegedyWalk_fixes_stationary P hP hrev⟩

end Qatlib.Concepts.WalkSearch.FrameSpectral
