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
set_option warningAsError false
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

def gradientSignedValueQ (M : ℕ) (z : Fin M) : ℚ :=
  if 2*z.val ≤ M then (z.val : ℚ)/M else (z.val : ℚ)/M-1

def gradientMedianRepetitions (d : ℕ) (δ : ℚ) : ℕ :=
  100*(Nat.clog 2 (max 1 d) + Nat.clog 2 (max 1 (Nat.ceil (1/δ))) + 1)

def gradientMedianCounted {d M : ℕ} (r : ℕ)
    (ω : Fin (2*r+1) → GradientGrid d M) (j : Fin d) : ℚ × ℕ :=
  qSelect (List.ofFn fun t => gradientSignedValueQ M (ω t j)) r

noncomputable def sourceGradientGridPoint (n : ℕ) (z : Fin (2^n)) : ℝ :=
  (z.val : ℝ)/(2 : ℝ)^n - 1/2 + 1/(2*(2 : ℝ)^n)

noncomputable section
open scoped Classical Matrix.Norms.L2Operator

def gradientPreparedWord (d M : ℕ) : List (PreparedStep (GradientGrid d M)) :=
  (gradientWord d M).reverse.map fun s => match s with
    | .gate U => .gate U
    | .query => .dataForward

def gradientFreshWord (d M R : ℕ) : List (FreshStep (GradientGrid d M) R) :=
  compileFresh (gradientPreparedWord d M) R

def gradientFreshOutput (d M : ℕ) (hM : 0 < M)
    (φ : GradientGrid d M → ℝ) (R : ℕ) : QState (FreshRegister (GradientGrid d M) R) :=
  ApplyGate (evaluateFresh (gradientPhase d M φ) 1 (gradientFreshWord d M R))
    (Ket (freshZero (gradientZero d M hM) R))

def gradientFreshRecord {H : Type} : {R : ℕ} → (Fin R → H) → FreshRegister H R
  | 0, _ => PUnit.unit
  | _+1, ω => (ω 0, gradientFreshRecord (fun i => ω i.succ))

def gradientFreshMass (d M : ℕ) (hM : 0 < M)
    (φ : GradientGrid d M → ℝ) {R : ℕ} (ω : Fin R → GradientGrid d M) : ℝ :=
  BornProb (gradientFreshOutput d M hM φ R) (gradientFreshRecord ω)

end
end Qatlib.Concepts.GradientOracle.ReadoutTools
