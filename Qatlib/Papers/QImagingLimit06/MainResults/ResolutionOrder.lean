/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QImagingLimit06.MainResults.Comparison

@[expose] public section

/-!
# Ordering the two imaging resolution bounds

For unit noise scale, the coherent field and intensity Fisher bounds
share the same photon-number denominator. The finite field data put
their two scale parameters in the order needed for comparison.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QImagingLimit06.MainResults

open scoped BigOperators
open Qatlib.Papers.QImagingLimit06.MainResults

/-- The finite-data field resolution bound is no larger than the intensity resolution bound. -/
theorem field_crb_le {ι : Type} [Fintype ι] {N a b : ℝ}
    (hN : 0 < N) (ha : 0 < a) (hb : 0 < b) (uRe uIm duRe duIm : ι → ℝ)
    (hn : ∀ k, uRe k ^ 2 + uIm k ^ 2 ≠ 0)
    (ha_def : 1 / a ^ 2 = ∑ k,
      ((uRe k * duRe k + uIm k * duIm k) / Real.sqrt (uRe k ^ 2 + uIm k ^ 2)) ^ 2)
    (hb_def : 1 / b ^ 2 = ∑ k, (duRe k ^ 2 + duIm k ^ 2)) :
    cramerRaoResolution (4 * N / b ^ 2) ≤ cramerRaoResolution (4 * N / a ^ 2) := by
  rw [resolution_intensity_fisher hN hb, resolution_intensity_fisher hN ha]
  exact div_le_div_of_nonneg_right (a_ge_b_of_field ha hb uRe uIm duRe duIm hn ha_def hb_def)
    (by positivity)

end Qatlib.Papers.QImagingLimit06.MainResults
