/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.GridGradient.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Qatlib.Concepts.HhlAlgorithms.Postselection.FreshTrials
import Qatlib.Concepts.NativeNumerics.LayeredMean.NativeSignedMeanConsumers
import Qatlib.Concepts.ShadowModels.SampleBudget.RationalLinearSelection

/-!
# Repeated gradient readout and counted medians

This module defines rational signed decoding, coordinatewise counted medians, and fresh-register
repetitions of a gradient circuit. These definitions make the sampling and classical
postprocessing costs explicit for median amplification in [GilyenArunachalamWiebe2019].

## Main definitions

* `gradientMedianCounted`: the selected rational median and comparison count.
* `gradientFreshOutput`: the coherent output of repeated fresh-register readout.
* `gradientFreshMass`: the Born mass of a tuple of recorded outcomes.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.ShadowModels.SampleBudget
open Qatlib.Concepts.HhlAlgorithms.Postselection

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.ReadoutTools
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators

/-- The rational signed decoding of a grid index, equal to `z/M` when `2*z ≤ M` and `z/M-1`
otherwise. -/
def gradientSignedValueQ (M : ℕ) (z : Fin M) : ℚ :=
  if 2*z.val ≤ M then (z.val : ℚ)/M else (z.val : ℚ)/M-1

/-- The repetition parameter `100*(clog₂(max 1 d) + clog₂(max 1 (ceil (1/δ))) + 1)` used for
coordinate-median amplification. -/
def gradientMedianRepetitions (d : ℕ) (δ : ℚ) : ℕ :=
  100*(Nat.clog 2 (max 1 d) + Nat.clog 2 (max 1 (Nat.ceil (1/δ))) + 1)

/-- The rational median and comparison count returned by `qSelect` at rank `r` on the `2*r+1`
signed outcomes for coordinate `j`. -/
def gradientMedianCounted {d M : ℕ} (r : ℕ)
    (ω : Fin (2*r+1) → GradientGrid d M) (j : Fin d) : ℚ × ℕ :=
  qSelect (List.ofFn fun t => gradientSignedValueQ M (ω t j)) r

/-- The midpoint coordinate `z/2^n - 1/2 + 1/(2*2^n)` in the centered dyadic unit grid. -/
noncomputable def sourceGradientGridPoint (n : ℕ) (z : Fin (2^n)) : ℝ :=
  (z.val : ℝ)/(2 : ℝ)^n - 1/2 + 1/(2*(2 : ℝ)^n)

noncomputable section
open scoped Classical Matrix.Norms.L2Operator

/-- The reversed gradient word translated into prepared steps, with each query represented as a
forward data query. -/
def gradientPreparedWord (d M : ℕ) : List (PreparedStep (GradientGrid d M)) :=
  (gradientWord d M).reverse.map fun s => match s with
    | .gate U => .gate U
    | .query => .dataForward

/-- The fresh-register compilation of the prepared gradient word for `R` repetitions. -/
def gradientFreshWord (d M R : ℕ) : List (FreshStep (GradientGrid d M) R) :=
  compileFresh (gradientPreparedWord d M) R

/-- The coherent state obtained by evaluating the repeated fresh-register gradient word from the
fresh zero basis state. -/
def gradientFreshOutput (d M : ℕ) (hM : 0 < M)
    (φ : GradientGrid d M → ℝ) (R : ℕ) : QState (FreshRegister (GradientGrid d M) R) :=
  ApplyGate (evaluateFresh (gradientPhase d M φ) 1 (gradientFreshWord d M R))
    (Ket (freshZero (gradientZero d M hM) R))

/-- The recursive encoding of a tuple of `R` outcomes as a basis label of `FreshRegister H R`. -/
def gradientFreshRecord {H : Type} : {R : ℕ} → (Fin R → H) → FreshRegister H R
  | 0, _ => PUnit.unit
  | _+1, ω => (ω 0, gradientFreshRecord (fun i => ω i.succ))

/-- The Born probability of the recorded outcome tuple in `gradientFreshOutput`. -/
def gradientFreshMass (d M : ℕ) (hM : 0 < M)
    (φ : GradientGrid d M → ℝ) {R : ℕ} (ω : Fin R → GradientGrid d M) : ℝ :=
  BornProb (gradientFreshOutput d M hM φ R) (gradientFreshRecord ω)

end
end Qatlib.Concepts.GradientOracle.ReadoutTools
