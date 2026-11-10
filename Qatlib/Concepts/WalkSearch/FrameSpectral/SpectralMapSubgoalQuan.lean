/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralMapSubgoalStat
set_option warningAsError false

open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Qatlib

theorem spectralMapSubgoal : SpectralMapSubgoal :=
  fun I _ _ P hP v hv θ hs hvD => Qatlib.Concepts.WalkSearch.Spectral.szegedy_spectral_map P hP v hv θ hs hvD

end Qatlib.Concepts.WalkSearch.FrameSpectral
