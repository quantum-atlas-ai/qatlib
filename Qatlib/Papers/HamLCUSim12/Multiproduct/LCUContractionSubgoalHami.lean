/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.LCUContractionSubgoalStat
set_option warningAsError false

open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

open Qatlib

theorem lcuContractionSubgoal : LCUContractionSubgoal :=
  fun J I _ _ _ _ U w hw _ P j0 hP ψ => Qatlib.Concepts.BlockEncoding.LinearCombination.lcu_corner_apply U hw hP ψ

end Qatlib.Papers.HamLCUSim12.Multiproduct
