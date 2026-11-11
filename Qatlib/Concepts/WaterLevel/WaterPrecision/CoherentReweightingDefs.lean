/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.ExactResampling.ExactResamplingProgram
import Qatlib.Concepts.Waterfill.LevelSearch.WaterFillingOptimization
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.QueryDistanceLowerBound

/-!
# Water-level reweighting data and access contracts

This module defines real and rational clipped fills, fidelity endpoints, source boxes, and level
brackets. `fidelityBracket` and `searchWork` describe rational bisection and its arithmetic
ledger, while `ReweightingSuccess`, `ReweightingEmbeds`, and `FilteredGamma2LowerConsumer`
express output and query-reduction obligations.

The reweighting construction is motivated by quantum rejection sampling
[OzolsRoettelerRoland2013]; see [Ozols et al., 2013][OzolsRoettelerRoland2013] for the
surrounding algorithmic setting.
-/

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

/-- The clipped real fill at coordinate `i`, defined as `min (π i) (γ * σ i)`. -/
def realFill (π σ : Fin m → ℝ) (γ : ℝ) (i : Fin m) : ℝ := min (π i) (γ * σ i)

/-- The fill-to-source ratio at a coordinate, with value zero when the source coordinate is
zero. -/
noncomputable def realRatio (π σ : Fin m → ℝ) (γ : ℝ) (i : Fin m) : ℝ :=
  if π i = 0 then 0 else realFill π σ γ i / π i

/-- The squared Euclidean mass of the real clipped-fill vector, summed over all coordinates. -/
def realMass (π σ : Fin m → ℝ) (γ : ℝ) : ℝ := ∑ i, realFill π σ γ i ^ 2

/-- The overlap of the target table `σ` with the real clipped-fill vector. -/
def realDot (π σ : Fin m → ℝ) (γ : ℝ) : ℝ := ∑ i, σ i * realFill π σ γ i

/-- The squared target overlap divided by the clipped-fill mass, with value zero when that mass
vanishes. -/
noncomputable def realFidelity (π σ : Fin m → ℝ) (γ : ℝ) : ℝ :=
  if realMass π σ γ = 0 then 0 else (realDot π σ γ) ^ 2 / realMass π σ γ

/-- The squared overlap of the source and target tables, used as the lower fidelity endpoint for
normalized nonnegative data. -/
def realPmin (π σ : Fin m → ℝ) : ℝ := (∑ i, π i * σ i) ^ 2

/-- The sum of target-coordinate squares over coordinates where the source is strictly positive. -/
noncomputable def realPmax (π σ : Fin m → ℝ) : ℝ := ∑ i, if 0 < π i then σ i ^ 2 else 0

/-- Requires every coordinate of `v` to lie between zero and the corresponding source coordinate
`π i`. -/
def SourceBox (π v : Fin m → ℝ) : Prop := ∀ i, 0 ≤ v i ∧ v i ≤ π i

/-- The complex matrix whose `(i, j)` entry is the product of the two real clipped-fill
coordinates, viewed as complex numbers. -/
noncomputable def realWaterMatrix (π σ : Fin m → ℝ) (γ : ℝ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => (realFill π σ γ i : ℂ) * (realFill π σ γ j : ℂ)

/-- Requires the scaled target coordinate to be at most the source coordinate wherever the
source is strictly positive. -/
def BracketLow (π σ : Fin m → ℝ) (γ : ℝ) : Prop :=
  ∀ i, 0 < π i → γ * σ i ≤ π i

/-- Requires at least one strictly positive source coordinate to equal its scaled target
coordinate at the given level. -/
def BracketLowTight (π σ : Fin m → ℝ) (γ : ℝ) : Prop :=
  ∃ i, 0 < π i ∧ γ * σ i = π i

/-- Requires the source coordinate to be at most the scaled target coordinate wherever the
target is strictly positive. -/
def BracketHigh (π σ : Fin m → ℝ) (γ : ℝ) : Prop :=
  ∀ i, 0 < σ i → π i ≤ γ * σ i

/-- Requires a coordinate with positive source and target values at which the source equals the
scaled target. -/
def BracketHighTight (π σ : Fin m → ℝ) (γ : ℝ) : Prop :=
  ∃ i, 0 < σ i ∧ 0 < π i ∧ π i = γ * σ i

/-- A strictly ordered pair of levels satisfying the lower and upper bracket conditions, each
with an equality witness. -/
def TightBracket (π σ : Fin m → ℝ) (γlo γhi : ℝ) : Prop :=
  γlo < γhi ∧ BracketLow π σ γlo ∧ BracketLowTight π σ γlo ∧
    BracketHigh π σ γhi ∧ BracketHighTight π σ γhi

/-- A weakly ordered pair of levels satisfying the lower and upper bracket inequalities, without
requiring equality witnesses. -/
def ClosedBracket (π σ : Fin m → ℝ) (γlo γhi : ℝ) : Prop :=
  γlo ≤ γhi ∧ BracketLow π σ γlo ∧ BracketHigh π σ γhi

/-- The rational clipped-fill mass, given by `computedWaterEnergy` at the selected level. -/
def computedMass (π σ : Fin m → ℚ) (γ : ℚ) : ℚ := computedWaterEnergy π σ γ

/-- The rational overlap of the target table with the clipped-fill vector. -/
def computedDot (π σ : Fin m → ℚ) (γ : ℚ) : ℚ := ∑ i, σ i * waterFill π σ γ i

/-- The rational squared overlap divided by the clipped-fill mass, with value zero when the mass
vanishes. -/
def computedFidelity (π σ : Fin m → ℚ) (γ : ℚ) : ℚ :=
  if computedMass π σ γ = 0 then 0
  else computedDot π σ γ ^ 2 / computedMass π σ γ

/-- The division-free threshold test `computedDot^2 ≥ p * computedMass` at a rational level.
This condition also holds when both mass and overlap are zero. -/
def fidelityReaches (π σ : Fin m → ℚ) (p γ : ℚ) : Prop :=
  computedDot π σ γ ^ 2 ≥ p * computedMass π σ γ

/-- The rational sum of target-coordinate squares over the strictly positive source support. -/
def computedPmax (π σ : Fin m → ℚ) : ℚ := ∑ i, if 0 < π i then σ i ^ 2 else 0

/-- Iterates rational bisection from `(0, computedWaterHigh π σ)`. Each step moves the lower
endpoint to the midpoint when `fidelityReaches` holds there, and otherwise moves the upper
endpoint. -/
def fidelityBracket (π σ : Fin m → ℚ) (p : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0, computedWaterHigh π σ)
  | k + 1 =>
    let b := fidelityBracket π σ p k
    let mid := (b.1 + b.2) / 2
    if computedDot π σ mid ^ 2 ≥ p * computedMass π σ mid
    then (mid, b.2) else (b.1, mid)

/-- The upper endpoint of the rational fidelity bracket after `k` bisection steps. -/
def selectedLevel (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ) : ℚ :=
  (fidelityBracket π σ p k).2

/-- Records the numbers of divisions, energy evaluations, and comparisons assigned to a rational
level search. -/
structure SearchWorkLedger where
  divisions : ℕ
  energyEvaluations : ℕ
  comparisons : ℕ

/-- Assigns `m` divisions, `m * k` energy evaluations, and `k` comparisons to a search with `m`
coordinates and `k` steps. -/
def searchWork (m k : ℕ) : SearchWorkLedger :=
  ⟨m, m * k, k⟩

/-- The real square root of the rational clipped-fill mass at the selected level. -/
noncomputable def selectedBeta (π σ : Fin m → ℚ) (γ : ℚ) : ℝ :=
  Real.sqrt (computedMass π σ γ)

/-- The exact-resampling triple of rounds, angle, and scale obtained from the square root of the
selected mass. -/
noncomputable def selectedSchedule (π σ : Fin m → ℚ) (γ : ℚ) : ℕ × ℝ × ℝ :=
  let β := selectedBeta π σ γ
  (resamplingExactRounds β, resamplingExactAngle β, resamplingExactScale β)

variable {D : ℕ}

/-- Requires positive mass, the stated fidelity ratio, and a normalized output with zero
marked-coin probability and target squared overlap at least `p`. The output condition must
hold for every normalized ancillary family and unitary realizing the source preparation. -/
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

/-- Records source-oracle calls, known fixed-gate macros, and data queries for a prepared word. -/
structure SourceCostLedger where
  sourceCalls : ℕ
  knownMacros : ℕ
  dataQueries : ℕ

/-- Extracts source calls, fixed gates, and data queries from a prepared word into a
`SourceCostLedger`. -/
def wordLedger {H : Type} (W : List (PreparedStep H)) : SourceCostLedger :=
  ⟨preparedInputQueries W, preparedFixedGates W, preparedDataQueries W⟩

/-- Pairs the exact resampling word for the given tables, level, and starting basis index with
its source-cost ledger. -/
noncomputable def exactResamplingProgram (π σ : Fin m → ℚ) (γ : ℝ)
    (j₀ : Fin m × Fin D) :
    List (PreparedStep ((Fin m × Fin D) × Bool)) × SourceCostLedger :=
  (resamplingExactWord π σ γ j₀, wordLedger (resamplingExactWord π σ γ j₀))

/-- Requires normalized source and target state families and a reduction of every successful
reweighting word to a unitary bit-query circuit. The circuit uses no more queries than the
word's source calls and produces exactly the target Gram matrix. -/
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

/-- Requires positive mass and constants together with a reweighting embedding whose filtered
gamma-two value and state-conversion semidefinite value have the stated inverse-square-root
mass lower bounds. -/
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

/-- Requires positive `c`, nonnegative `C`, and at least `c / sqrt(levelMass) - C` source
queries for every successful reweighting word at the given instance. -/
def SourceQueryLowerBound (π σ : Fin m → ℚ) (γ : ℝ) (p c C : ℝ) : Prop :=
  0 < c ∧ 0 ≤ C ∧
    ∀ (j₀ : Fin m × Fin D)
      (W : List (PreparedStep ((Fin m × Fin D) × Bool))),
      ReweightingSuccess j₀ π σ γ p W →
      c / Real.sqrt (levelMass π σ γ) - C ≤ (preparedInputQueries W : ℝ)

end Qatlib.Concepts.WaterLevel.WaterPrecision
