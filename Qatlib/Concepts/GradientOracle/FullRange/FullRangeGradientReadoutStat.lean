/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.FullRangeFixedPointPrecisionStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SignalPrimitive.GridGradient

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.FullRange
open Matrix
open scoped Classical BigOperators

def FullRangeGradientReadout : Prop :=
  ∀ (d M : ℕ) (hM : 0 < M) (K k : ℕ) (f : GradientGrid d M → ℝ) (lo s R : ℝ),
    2 ≤ k → 0 < s → 0 ≤ R → s*R < (2 : ℝ)^K →
    (∀ x, lo ≤ f x ∧ f x ≤ lo+R) →
    IsUnitaryCircuit (fullRangeGradientProgram d M K k) ∧
    QueryCount (fullRangeGradientProgram d M K k) = 1 ∧
    GateCount (fullRangeGradientProgram d M K k) = 2*d+1 ∧
    Normalized (fullRangeGradientOutput d M hM K k f lo s) ∧
    fullRangeGradientOutput d M hM K k f lo s =
      TensorState (gradientReadout d M hM (fullRangePhase K k (fullRangeValueTable K k f lo s)))
        (fullRangeKickState K k) ∧
    (∀ E : Finset (GradientGrid d M),
      |MeasureProb (fullRangeGradientOutput d M hM K k f lo s) (E ×ˢ Finset.univ) -
        MeasureProb (gradientReadout d M hM (fun x => s*(f x-lo))) E| ≤ 4*Real.pi/(2 : ℝ)^k) ∧
    (∀ (q : GradientGrid d M) (c : ℝ),
      (∀ x, s*(f x-lo) = c+∑ j, (q j).val*(x j).val/(M : ℝ)) →
      Real.cos (2*Real.pi/(2 : ℝ)^k)^2 ≤
        MeasureProb (fullRangeGradientOutput d M hM K k f lo s) ({q} ×ˢ Finset.univ))

end Qatlib.Concepts.GradientOracle.FullRange
