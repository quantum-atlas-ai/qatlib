/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.ExactResampling.ExactResamplingProgram
import Qatlib.Concepts.Waterfill.LevelSearch.WaterFillingOptimization
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.QueryDistanceLowerBound
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.NativeNumerics.WaterFilling
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.Waterfill.LevelSearch

namespace Qatlib.Concepts.WaterLevel.WaterPrecision

set_option autoImplicit false

open Matrix
open Qatlib.Concepts.Waterfill.ExactResampling
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators ComplexOrder ENNReal

variable {m : ℕ}

def realFill (π σ : Fin m → ℝ) (γ : ℝ) (i : Fin m) : ℝ := min (π i) (γ * σ i)

noncomputable def realRatio (π σ : Fin m → ℝ) (γ : ℝ) (i : Fin m) : ℝ :=
  if π i = 0 then 0 else realFill π σ γ i / π i

def realMass (π σ : Fin m → ℝ) (γ : ℝ) : ℝ := ∑ i, realFill π σ γ i ^ 2

def realDot (π σ : Fin m → ℝ) (γ : ℝ) : ℝ := ∑ i, σ i * realFill π σ γ i

noncomputable def realFidelity (π σ : Fin m → ℝ) (γ : ℝ) : ℝ :=
  if realMass π σ γ = 0 then 0 else (realDot π σ γ) ^ 2 / realMass π σ γ

def realPmin (π σ : Fin m → ℝ) : ℝ := (∑ i, π i * σ i) ^ 2

noncomputable def realPmax (π σ : Fin m → ℝ) : ℝ := ∑ i, if 0 < π i then σ i ^ 2 else 0

def SourceBox (π v : Fin m → ℝ) : Prop := ∀ i, 0 ≤ v i ∧ v i ≤ π i

noncomputable def realWaterMatrix (π σ : Fin m → ℝ) (γ : ℝ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => (realFill π σ γ i : ℂ) * (realFill π σ γ j : ℂ)

def BracketLow (π σ : Fin m → ℝ) (γ : ℝ) : Prop :=
  ∀ i, 0 < π i → γ * σ i ≤ π i

def BracketLowTight (π σ : Fin m → ℝ) (γ : ℝ) : Prop :=
  ∃ i, 0 < π i ∧ γ * σ i = π i

def BracketHigh (π σ : Fin m → ℝ) (γ : ℝ) : Prop :=
  ∀ i, 0 < σ i → π i ≤ γ * σ i

def BracketHighTight (π σ : Fin m → ℝ) (γ : ℝ) : Prop :=
  ∃ i, 0 < σ i ∧ 0 < π i ∧ π i = γ * σ i

def TightBracket (π σ : Fin m → ℝ) (γlo γhi : ℝ) : Prop :=
  γlo < γhi ∧ BracketLow π σ γlo ∧ BracketLowTight π σ γlo ∧
    BracketHigh π σ γhi ∧ BracketHighTight π σ γhi

def ClosedBracket (π σ : Fin m → ℝ) (γlo γhi : ℝ) : Prop :=
  γlo ≤ γhi ∧ BracketLow π σ γlo ∧ BracketHigh π σ γhi

def computedMass (π σ : Fin m → ℚ) (γ : ℚ) : ℚ := computedWaterEnergy π σ γ

def computedDot (π σ : Fin m → ℚ) (γ : ℚ) : ℚ := ∑ i, σ i * waterFill π σ γ i

def computedFidelity (π σ : Fin m → ℚ) (γ : ℚ) : ℚ :=
  if computedMass π σ γ = 0 then 0
  else computedDot π σ γ ^ 2 / computedMass π σ γ

def fidelityReaches (π σ : Fin m → ℚ) (p γ : ℚ) : Prop :=
  computedDot π σ γ ^ 2 ≥ p * computedMass π σ γ

def computedPmax (π σ : Fin m → ℚ) : ℚ := ∑ i, if 0 < π i then σ i ^ 2 else 0

def fidelityBracket (π σ : Fin m → ℚ) (p : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0, computedWaterHigh π σ)
  | k + 1 =>
    let b := fidelityBracket π σ p k
    let mid := (b.1 + b.2) / 2
    if computedDot π σ mid ^ 2 ≥ p * computedMass π σ mid
    then (mid, b.2) else (b.1, mid)

def selectedLevel (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ) : ℚ :=
  (fidelityBracket π σ p k).2

structure SearchWorkLedger where
  divisions : ℕ
  energyEvaluations : ℕ
  comparisons : ℕ

def searchWork (m k : ℕ) : SearchWorkLedger :=
  ⟨m, m * k, k⟩

noncomputable def selectedBeta (π σ : Fin m → ℚ) (γ : ℚ) : ℝ :=
  Real.sqrt (computedMass π σ γ)

noncomputable def selectedSchedule (π σ : Fin m → ℚ) (γ : ℚ) : ℕ × ℝ × ℝ :=
  let β := selectedBeta π σ γ
  (resamplingExactRounds β, resamplingExactAngle β, resamplingExactScale β)

variable {D : ℕ}

def ReweightingSuccess (j₀ : Fin m × Fin D) (π σ : Fin m → ℚ) (γ : ℝ) (p : ℝ)
    (W : List (PreparedStep ((Fin m × Fin D) × Bool))) : Prop :=
  0 < levelMass π σ γ ∧
    p = levelDot π σ γ ^ 2 / levelMass π σ γ ∧
    ∀ (ξ : Fin m → QState (Fin D))
      (U : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ),
      (∀ i, Normalized (ξ i)) →
      U ∈ Matrix.unitaryGroup (Fin m × Fin D) ℂ →
      U *ᵥ Ket j₀ = waterSource π ξ →
      let out := ApplyGate
        (evaluatePrepared 1 (resamplingEmbeddedOracle U) W) (Ket (j₀, false))
      Normalized out ∧
        MeasureProb out (waterEvent m D) = 0 ∧
        p ≤ Complex.normSq
          (Inner (resamplingFamily (fun i => (σ i : ℝ)) ξ) out)

structure SourceCostLedger where
  sourceCalls : ℕ
  knownMacros : ℕ
  dataQueries : ℕ

def wordLedger {H : Type} (W : List (PreparedStep H)) : SourceCostLedger :=
  ⟨preparedInputQueries W, preparedFixedGates W, preparedDataQueries W⟩

noncomputable def exactResamplingProgram (π σ : Fin m → ℚ) (γ : ℝ)
    (j₀ : Fin m × Fin D) :
    List (PreparedStep ((Fin m × Fin D) × Bool)) × SourceCostLedger :=
  (resamplingExactWord π σ γ j₀, wordLedger (resamplingExactWord π σ γ j₀))

def ReweightingEmbeds (π σ : Fin m → ℚ) (γ : ℝ) (p : ℝ)
    {X : Type} [Fintype X] [DecidableEq X] {n R : ℕ}
    (input : X → Fin n → Bool) (ρ τ : X → QState ((Fin n × Bool) × Fin R)) :
    Prop :=
  (∀ x, Normalized (ρ x)) ∧
    (∀ x, Normalized (τ x)) ∧
    ∀ (j₀ : Fin m × Fin D)
      (W : List (PreparedStep ((Fin m × Fin D) × Bool))),
      ReweightingSuccess j₀ π σ γ p W →
      ∃ (C : Circuit ((Fin n × Bool) × Fin R)) (T : ℕ),
        QueryCount C = T ∧ T ≤ preparedInputQueries W ∧
          IsUnitaryCircuit C ∧
          (∀ x y, Inner (Run (workspaceBitOracle (W := Fin R) (input x)) C (ρ x))
            (Run (workspaceBitOracle (W := Fin R) (input y)) C (ρ y)) =
            Inner (τ x) (τ y))

def FilteredGamma2LowerConsumer (π σ : Fin m → ℚ) (γ : ℝ) (p δ c cδ : ℝ) : Prop :=
  0 < levelMass π σ γ ∧
    0 < c ∧ 0 < cδ ∧ 0 ≤ δ ∧
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (n R : ℕ)
        (input : X → Fin n → Bool) (ρ τ : X → QState ((Fin n × Bool) × Fin R)),
      ReweightingEmbeds (D := D) π σ γ p input ρ τ ∧
        ENNReal.ofReal (c / Real.sqrt (levelMass π σ γ)) ≤
          filteredGamma2 (gramStateMatrix ρ - gramStateMatrix τ)
            (gramFilterDelta input) ∧
        ENNReal.ofReal (cδ / Real.sqrt (levelMass π σ γ)) ≤
          stateConversionSDP input δ (gramStateMatrix ρ) (gramStateMatrix τ)

def SourceQueryLowerBound (π σ : Fin m → ℚ) (γ : ℝ) (p c C : ℝ) : Prop :=
  0 < c ∧ 0 ≤ C ∧
    ∀ (j₀ : Fin m × Fin D)
      (W : List (PreparedStep ((Fin m × Fin D) × Bool))),
      ReweightingSuccess j₀ π σ γ p W →
      c / Real.sqrt (levelMass π σ γ) - C ≤ (preparedInputQueries W : ℝ)

end Qatlib.Concepts.WaterLevel.WaterPrecision
