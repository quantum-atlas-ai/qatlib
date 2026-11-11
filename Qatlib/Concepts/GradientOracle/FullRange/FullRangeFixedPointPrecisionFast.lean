/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.FullRangeFixedPointPrecisionStat
import Qatlib.Concepts.GradientOracle.FullRange.FullRangeValueLabels

/-!
# Full-range fixed-point precision

This module proves `fullRangeFixedPointPrecision`, combining range bounds, decoding error, and
basis-state evaluation for the dyadic value table. The guard on the scaled value range prevents
modular wraparound in the precision model associated with [Jordan2005Gradient].

## Main statements

* `fullRangeFixedPointPrecision`: the fixed-point value label decodes with error less than `1 /
  (s * 2^k)` and is produced by a basis-state query.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.FullRange
open Qatlib

/-- Proves the guarded full-range encoding specification: canonical value labels, one-sided
decoding precision, and exact basis-state evaluation by the value oracle. This supplies the
fixed-point precision component of [Jordan2005Gradient]. -/
theorem fullRangeFixedPointPrecision : FullRangeFixedPointPrecision := by
  intro X _ _ K k f lo s R hs hR hguard hf x
  obtain ⟨h0,hL,hval⟩ := full_range_integer_bounds K k f lo s R hs hR hguard hf x
  exact ⟨h0,hL,hval,full_range_decoding_precision K k f lo s R hs hR hguard hf x,
    full_range_basis_value_query K k f lo s x⟩
end Qatlib.Concepts.GradientOracle.FullRange
