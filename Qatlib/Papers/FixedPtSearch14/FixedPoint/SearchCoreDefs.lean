/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.SearchDefs
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadout
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.QuantumPayoffEstimation
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryLowerBounds
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QueryComplexity.AdversarySearch

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Matrix
open scoped BigOperators Classical
open Qatlib
open Qatlib.Papers.FixedPtSearch14.FixedPoint

variable {I : Type} [Fintype I] [DecidableEq I]

inductive AEOracleResource where

  | phaseMark

  | bitKickback
  deriving DecidableEq, Repr

structure RelativeEndpointContract where

  a₀ : ℝ

  a₀_pos : 0 < a₀

  a₀_le_one : a₀ ≤ 1

  ε : ℝ

  ε_pos : 0 < ε

  δ : ℝ

  δ_nonneg : 0 ≤ δ

  δ_lt_one : δ < 1

  resource : AEOracleResource

  budget : ℕ

noncomputable def tightGridArgument (a₀ ε : ℝ) : ℝ :=
  4 * Real.pi * Real.sqrt ((1 - a₀) / a₀) / ε + 2 * Real.pi / Real.sqrt (a₀ * ε)

noncomputable def tightRelativeGrid (a₀ ε : ℝ) : ℕ :=
  Nat.ceil (tightGridArgument a₀ ε) + 1

noncomputable def refinedPromise (M : ℕ) (a₀ : ℝ) (z : Fin M) : ℝ :=
  max a₀ (aeEstimate M z - 2 * Real.pi / (M : ℝ))

noncomputable def phaseMarkPeakRounds (θ : ℝ) : ℕ :=
  Nat.floor (Real.pi / (4 * θ))

noncomputable def phaseMarkCrossingRounds (θ : ℝ) : ℕ :=
  Nat.ceil (Real.pi / (4 * θ) - 1 / 2)

structure AECostLedger where

  queries : ℕ

  gates : ℕ

  decodeBits : ℕ

  workspaceBits : ℕ

noncomputable def aeWorkspaceBits (M : ℕ) : ℕ :=
  M * (Fintype.card I) * 2

structure VarianceOnlyEndpoint where

  V : ℝ

  V_nonneg : 0 ≤ V

  σ : ℝ

  σ_pos : 0 < σ

  τ : ℝ

  τ_pos : 0 < τ

noncomputable def truncatedCentredPayoff (f : I → ℝ) (μ τ : ℝ) (i : I) : ℝ :=
  truncatedPayoff f μ τ i

inductive AEAccessModel where

  | dataCall

  | thresholdMacro
  deriving DecidableEq, Repr

def aeRoundAccessSteps : ℕ := 6

def aeRoundDataCalls : ℕ := 1

noncomputable def multiLayerMedian (M k r : ℕ) (ω : Fin (2 * r + 1) → Fin M) : ℝ :=
  sortedBlockMedian r (fun l => (nativeAEDecode M k (ω l) : ℝ))

structure SearchComplexity where

  model : AccessModel

  success : ℝ

  queries : ℕ

  sensitivity : ℝ

noncomputable def phaseMarkComplexity (k : ℕ) (θ : ℝ) : SearchComplexity where
  model := .phaseMark
  success := (Real.sin ((2 * k + 1) * θ)) ^ 2
  queries := k
  sensitivity := Real.sin θ

noncomputable def tableLoadBits (t : DatabaseTable) : ℕ :=
  t.rows * t.width

noncomputable def rowCompareBits (r₁ r₂ : List Bool) : ℕ :=
  let common := (r₁.zip r₂).takeWhile (fun p => p.1 = p.2)
  common.length + 1

noncomputable def gridTightening (a₀ ε : ℝ) : ℝ :=
  relativeAESamplingError (relativeAEGrid a₀ ε) a₀

def workspaceDataDecoder {n : ℕ} {W : Type} : ((Reg n × Bool) × W) → Option (Reg n) :=
  fun p => some p.1.1

structure MinimalSearchComplexity where

  model : AccessModel

  success : ℝ

  sensitivity : ℝ

  queries : ℝ

def minimalComplexityOf (c : SearchComplexity) : MinimalSearchComplexity where
  model := c.model
  success := c.success
  sensitivity := c.sensitivity
  queries := (c.queries : ℝ)

noncomputable def bitModelSensitivity (N : ℕ) : ℝ := 1 / Real.sqrt N

noncomputable def bitModelProgramComplexity (n : ℕ) : SearchComplexity where
  model := .bitKickback
  success := 1 - 1 / (Fintype.card (Reg n) : ℝ)
  queries := singletonSearchIterations n
  sensitivity := Real.sin (singletonSearchAngle n)

noncomputable def bitModelMinimalComplexity (N : ℕ) : MinimalSearchComplexity where
  model := .bitKickback
  success := 2 / 3
  sensitivity := bitModelSensitivity N
  queries := Real.sqrt N / 8

noncomputable def bitModelActualComplexity (n : ℕ) : MinimalSearchComplexity :=
  minimalComplexityOf (bitModelProgramComplexity n)

end Qatlib.Papers.FixedPtSearch14.FixedPoint
