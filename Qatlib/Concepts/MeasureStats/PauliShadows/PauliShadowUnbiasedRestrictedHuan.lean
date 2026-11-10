/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MeasureStats.PauliShadows.PauliShadowUnbiasedRestrictedStat

open Qatlib.Concepts.ChannelTheory.Stinespring

namespace Qatlib.Concepts.MeasureStats.PauliShadows

open Qatlib

theorem pauliShadowUnbiasedRestrictedSubgoal : PauliShadowUnbiasedRestrictedSubgoal :=
  fun ρ hρ => Qatlib.Concepts.ChannelTheory.Stinespring.pauliShadow_unbiased ρ hρ

end Qatlib.Concepts.MeasureStats.PauliShadows
