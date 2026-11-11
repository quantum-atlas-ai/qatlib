/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The arcsine perturbation statement

This module defines `MontanaroClaim17`, the unit-interval arcsine perturbation statement from
[Montanaro2015]. It expresses angle stability in terms of the square root of the absolute
difference of squared amplitudes.

## Main statements

* `MontanaroClaim17`: states the perturbation inequality for two inputs in the unit interval.

## References

* [Montanaro, 2015, Claim 17][Montanaro2015]
-/

namespace Qatlib.Concepts.AEMeanReadout.AELawStability

/-- The proposition that for `x, y ∈ [0, 1]`, the absolute arcsine difference is bounded by `π /
2` times `√|x² - y²|` [Montanaro2015]. -/
def MontanaroClaim17 : Prop :=
  ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
    |Real.arcsin x - Real.arcsin y| ≤ (Real.pi / 2) * Real.sqrt |x ^ 2 - y ^ 2|

end Qatlib.Concepts.AEMeanReadout.AELawStability
