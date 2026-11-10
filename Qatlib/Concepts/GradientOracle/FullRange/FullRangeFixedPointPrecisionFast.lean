/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.FullRangeFixedPointPrecisionStat
import Qatlib.Concepts.GradientOracle.FullRange.FullRangeValueLabels
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.FullRange
open Qatlib

theorem fullRangeFixedPointPrecision : FullRangeFixedPointPrecision := by
  intro X _ _ K k f lo s R hs hR hguard hf x
  obtain ⟨h0,hL,hval⟩ := full_range_integer_bounds K k f lo s R hs hR hguard hf x
  exact ⟨h0,hL,hval,full_range_decoding_precision K k f lo s R hs hR hguard hf x,
    full_range_basis_value_query K k f lo s x⟩
end Qatlib.Concepts.GradientOracle.FullRange
