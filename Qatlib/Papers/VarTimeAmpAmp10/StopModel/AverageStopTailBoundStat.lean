/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.StructuralProgram

/-!
# Average stopping-time tail contract

`AverageStopTailBound` states a tail-mass identity and a weighted running-mass bound for legal,
supported growing-history runs that finish with no running mass. The weighted sum is bounded by
the square root of the number of stages times `reachedTav`.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `AverageStopTailBound`: running-tail identity and average stopping-time estimate.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel

/-- The proposition that complete, supported growing-history runs have running mass equal to the
tail of stopping increments and satisfy the weighted square-root tail bound. -/
def AverageStopTailBound : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C]
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C),
    GrowingVtLegal stages history →
    ∀ (j₀ : VtSpace C), j₀.1 = vtRunningFlag →
    GrowingVtSupported stages history j₀ →
    MeasureProb (vtState stages stages.length (Ket j₀)) (runningSet C) = 0 →
    (∀ i, i ≤ stages.length →
      MeasureProb (vtState stages i (Ket j₀)) (runningSet C) =
        ∑ j ∈ Finset.range stages.length,
          if i ≤ j then reachedPstop stages history (Ket j₀) j else 0) ∧
    (∑ i ∈ Finset.range stages.length,
      (2 : ℝ) ^ i * Real.sqrt (MeasureProb (vtState stages i (Ket j₀)) (runningSet C))) ≤
        Real.sqrt (stages.length : ℝ) * reachedTav stages history j₀

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
