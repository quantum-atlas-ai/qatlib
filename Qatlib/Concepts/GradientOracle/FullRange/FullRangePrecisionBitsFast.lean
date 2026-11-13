/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.FullRangePrecisionBitsStat
import Qatlib.Concepts.GradientOracle.FullRange.FullRangeGradientReadoutFast
import Qatlib.Concepts.GradientOracle.FullRange.FullRangeBitLaws

/-!
# Precision bits for full-range readout

This module proves `fullRangePrecisionBits` by choosing a guarded register width from the scaled
rational value range. It connects logarithmic bit counts to decoding and measurement precision
in the comparison studied in [Jordan2005Gradient].

## Main statements

* `fullRangePrecisionBits`: the chosen width satisfies the range guard, logarithmic bounds, and
  one-query readout guarantees.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.GradientOracle.FullRange
open Matrix
open scoped Classical

/-- Proves that the selected range width satisfies the guard and logarithmic bit bounds,
together with decoding precision and one-query readout guarantees. This supplies the dyadic
bit comparison associated with [Jordan2005Gradient]. -/
theorem fullRangePrecisionBits : FullRangePrecisionBits := by
  intro s R hs hR
  let K := fullRangeClassicalBits (s*R)
  have hg := full_range_classical_bits_guard (s*R)
  have hsr : (0:ℝ)<s := by exact_mod_cast hs
  have hRr : (0:ℝ)≤R := by exact_mod_cast hR
  have hgr : (s:ℝ)*(R:ℝ)<(2:ℝ)^K := by exact_mod_cast hg
  refine ⟨hg,full_range_classical_bits_log (s*R),?_⟩
  intro d M hM k f lo hk hf
  have hr := fullRangeGradientReadout d M hM K k f lo (s:ℝ) (R:ℝ) hk hsr hRr hgr hf
  refine ⟨?_,hr.2.1,hr.2.2.1,hr.2.2.2.2.2.1⟩
  intro x
  exact full_range_decoding_precision K k f lo (s:ℝ) (R:ℝ) hsr hRr hgr hf x

end Qatlib.Concepts.GradientOracle.FullRange
