/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.FullRangeCharacterKickbackStat
import Qatlib.Concepts.GradientOracle.FullRange.FullRangeCharacterLaws

/-!
# Full-range Fourier-character kickback

`fullRangeCharacterKickback` proves the combined normalization, inverse-QFT preparation,
value-oracle unitarity, and phase-kickback contract. It supplies the Fourier-character step for
coherent full-range value-oracle constructions. See [Jordan2005Gradient] for background.

## Main statements

* `fullRangeCharacterKickback`: The full-range kickback state is normalized and prepared by the
  inverse QFT, and the unitary value oracle applies the specified phase to the input while
  preserving that state. [Jordan2005Gradient]

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HspRecovery.CyclicRecovery

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.FullRange
open Qatlib

/-- The full-range kickback state is normalized and prepared by the inverse QFT, and the unitary
value oracle applies the specified phase to the input while preserving that state.
[Jordan2005Gradient] -/
theorem fullRangeCharacterKickback : FullRangeCharacterKickback := by
  intro K k
  refine ⟨full_range_character_normalized K k,full_range_character_preparation K k,?_⟩
  intro X _ _ v
  refine ⟨?_,full_range_query_kickback K k v⟩
  rw [full_range_value_oracle_eq_addOracle]
  exact addOracle_unitary v
end Qatlib.Concepts.GradientOracle.FullRange
