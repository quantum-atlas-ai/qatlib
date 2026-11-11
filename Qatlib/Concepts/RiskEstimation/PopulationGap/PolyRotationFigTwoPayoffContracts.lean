/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationFigTwoDefs
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.QuantumPayoffEstimation

/-!
# Polynomial rotation payoff contract

This module defines `PolyRotationFigTwoPayoff`, a specification relating the compiled polynomial
angle program to a payoff rotation with a squared sine payoff. For angles in `[0, π / 2]`, it
requires equality of the embedded basis state outputs, supporting the payoff encoding used in
[WoernerEgger2019].

## Main definition

* `PolyRotationFigTwoPayoff`: equality between the compiled negative angle program and the
  embedded payoff rotation on an initially false flag.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.RiskEstimation.PolyReadout
open Qatlib.Concepts.RiskEstimation.PolyRotation

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PopulationGap

open Matrix

/-- Specifies that, when the Taylor based payoff angle lies in `[0, π / 2]`, the compiled
negative angle program acts on the embedded basis input exactly as the corresponding squared
sine payoff rotation. -/
def PolyRotationFigTwoPayoff : Prop :=
  ∀ (u n : ℕ) (c : ℝ) (fp : Polynomial ℝ) (x : Reg n),
    let φ : ℝ := c*riskSinTaylor u c (fp.eval (figTwoRegEval x : ℝ)) + Real.pi/4
    let g : Reg n → ℝ :=
      fun y => Real.sin (c*riskSinTaylor u c (fp.eval (figTwoRegEval y : ℝ)) + Real.pi/4)^2
    let embed : Reg n → Bool → Reg (n+1+(n-1)) :=
      fun z b => (multiKnownSplit n).symm ((z, b), fun _ => false)
    0 ≤ φ → φ ≤ Real.pi/2 →
    Run (1 : Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ)
      (reflectionCompile (figTwoProgram (n := n) (fp.natDegree*(2*u+1))
        (fun y => -(riskFigTwoAnglePoly u c fp).eval (figTwoRegEval y : ℝ))))
      (Ket (embed x false)) =
    ∑ b : Bool,
      ((payoffRotation g : Matrix (Reg n × Bool) (Reg n × Bool) ℂ) *ᵥ
        Ket (x, false)) (x, b) • Ket (embed x b)

end Qatlib.Concepts.RiskEstimation.PopulationGap
