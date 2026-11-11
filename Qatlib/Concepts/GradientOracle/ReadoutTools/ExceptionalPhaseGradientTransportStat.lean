/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ReadoutTools.PureStateEventLipschitzStat

/-!
# Specification of exceptional phase transport

`ExceptionalPhaseGradientTransport` states stability of normalized gradient readout under a
bounded phase discrepancy on a large subset of the grid. Its state and event estimates provide
the robustness input used in [GilyenArunachalamWiebe2019].

## Main statements

* `ExceptionalPhaseGradientTransport`: squared state distance is at most `(2*π*B)^2+4*η`, and
  every event changes by at most its square root.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree

open Qatlib.Concepts.SignalPrimitive.GridGradient

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.ReadoutTools
open Qatlib
open scoped Classical

/-- The proposition that phase discrepancy at most `B` outside an exceptional fraction `η` gives
normalized readouts, squared state distance at most `(2*π*B)^2+4*η`, and the corresponding
square-root event bound. -/
def ExceptionalPhaseGradientTransport : Prop :=
  ∀ (d M : ℕ) (hM : 0 < M) (φ ψ : GradientGrid d M → ℝ)
    (S : Finset (GradientGrid d M)) (B η : ℝ),
    0 ≤ B → 0 ≤ η →
    ((Finset.univ \ S).card : ℝ) ≤ η*(M : ℝ)^d →
    (∀ x ∈ S, |φ x-ψ x| ≤ B) →
    Normalized (gradientReadout d M hM φ) ∧ Normalized (gradientReadout d M hM ψ) ∧
    ‖toEuclidean_fromVec (gradientReadout d M hM φ-gradientReadout d M hM ψ)‖^2
      ≤ (2*Real.pi*B)^2+4*η ∧
    ∀ E : Finset (GradientGrid d M),
      |MeasureProb (gradientReadout d M hM φ) E -
        MeasureProb (gradientReadout d M hM ψ) E| ≤ Real.sqrt ((2*Real.pi*B)^2+4*η)

end Qatlib.Concepts.GradientOracle.ReadoutTools
