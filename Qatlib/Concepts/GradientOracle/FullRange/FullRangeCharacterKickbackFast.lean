/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.FullRangeCharacterKickbackStat
import Qatlib.Concepts.GradientOracle.FullRange.FullRangeCharacterLaws
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HspRecovery.CyclicRecovery

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.FullRange
open Qatlib

theorem fullRangeCharacterKickback : FullRangeCharacterKickback := by
  intro K k
  refine ⟨full_range_character_normalized K k,full_range_character_preparation K k,?_⟩
  intro X _ _ v
  refine ⟨?_,full_range_query_kickback K k v⟩
  rw [full_range_value_oracle_eq_addOracle]
  exact addOracle_unitary v
end Qatlib.Concepts.GradientOracle.FullRange
