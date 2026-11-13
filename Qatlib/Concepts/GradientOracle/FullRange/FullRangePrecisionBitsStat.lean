/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.FullRangeGradientReadoutStat

/-!
# Specification of full-range precision bits

`FullRangePrecisionBits` expresses how the integer range width and fractional precision combine
in a dyadic value register. It packages the logarithmic bit comparison, decoding error, and
readout resources relevant to [Jordan2005Gradient].

## Main statements

* `FullRangePrecisionBits`: the selected range width is within one bit of the stated ceiling
  logarithms when the scaled range is at least one.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SignalPrimitive.GridGradient

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.FullRange
open Matrix
open scoped Classical

/-- The proposition combining a guarded range-bit choice, ceiling-logarithm comparisons,
fixed-point decoding precision, and resource and event-error bounds for full-range readout. -/
def FullRangePrecisionBits : Prop :=
  ∀ (s R : ℚ), 0 < s → 0 ≤ R →
    let K := fullRangeClassicalBits (s*R)
    (s*R : ℚ) < (2^K : ℕ) ∧
    ((1 : ℚ) ≤ s*R →
      let C := Nat.ceil (Real.logb 2 (s*R : ℚ))
      C ≤ K ∧ K ≤ C+1 ∧
      ∀ k : ℕ,
        Nat.ceil (Real.logb 2 ((s*R : ℚ)*(2 : ℝ)^k)) ≤ K+k ∧
        K+k ≤ Nat.ceil (Real.logb 2 ((s*R : ℚ)*(2 : ℝ)^k))+1) ∧
    (∀ (d M : ℕ) (hM : 0 < M) (k : ℕ) (f : GradientGrid d M → ℝ) (lo : ℝ),
      2 ≤ k → (∀ x, lo ≤ f x ∧ f x ≤ lo+(R : ℝ)) →
      (∀ x, 0 ≤ f x-(lo+((fullRangeValueTable K k f lo (s : ℝ) x).val : ℝ)/((s : ℝ)*(2 : ℝ)^k)) ∧
        f x-(lo+((fullRangeValueTable K k f lo (s : ℝ) x).val : ℝ)/((s : ℝ)*(2 : ℝ)^k)) <
          1/((s : ℝ)*(2 : ℝ)^k)) ∧
      QueryCount (fullRangeGradientProgram d M K k) = 1 ∧
      GateCount (fullRangeGradientProgram d M K k) = 2*d+1 ∧
      ∀ E : Finset (GradientGrid d M),
        |MeasureProb (fullRangeGradientOutput d M hM K k f lo (s : ℝ)) (E ×ˢ Finset.univ) -
          MeasureProb (gradientReadout d M hM (fun x => (s : ℝ)*(f x-lo))) E|
          ≤ 4*Real.pi/(2 : ℝ)^k)

end Qatlib.Concepts.GradientOracle.FullRange
