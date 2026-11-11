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

/-!
# Contracts for relative estimation and search

This module defines the endpoint contracts, refined grids, and complexity records used with the
fixed-point-search development [YoderLowChuang2014]. `RelativeEndpointContract` stores the
promise, accuracy, failure parameter, resource model, and budget; `SearchComplexity` and
`MinimalSearchComplexity` retain access-model tags when comparing query costs.

The numerical definitions include peak-round choices, median readout, table-access costs, and
the bit-kickback lower-bound record.

## Main statements

* `tightRelativeGrid`: A ceiling-based grid selected from the relative-error parameters.
* `refinedPromise`: A lower-bound update from an amplitude-estimation record.
* `bitModelProgramComplexity`: The resource record for the workspace search program.
* `bitModelMinimalComplexity`: The comparison record with query value `√N / 8`.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

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

/-- The resource tags for phase-mark and bit-kickback oracle access. -/
inductive AEOracleResource where

  | phaseMark

  | bitKickback
  deriving DecidableEq, Repr

/-- A relative-estimation contract storing a positive promise at most one, positive accuracy, a
failure parameter in `[0, 1)`, an oracle resource, and a natural budget. -/
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

/-- The real grid argument `4π√((1 - a₀) / a₀) / ε + 2π / √(a₀ε)`. -/
noncomputable def tightGridArgument (a₀ ε : ℝ) : ℝ :=
  4 * Real.pi * Real.sqrt ((1 - a₀) / a₀) / ε + 2 * Real.pi / Real.sqrt (a₀ * ε)

/-- The natural ceiling of `tightGridArgument a₀ ε`, plus one. -/
noncomputable def tightRelativeGrid (a₀ ε : ℝ) : ℕ :=
  Nat.ceil (tightGridArgument a₀ ε) + 1

/-- The maximum of the original promise and the ideal estimate minus `2π / M`. -/
noncomputable def refinedPromise (M : ℕ) (a₀ : ℝ) (z : Fin M) : ℝ :=
  max a₀ (aeEstimate M z - 2 * Real.pi / (M : ℝ))

/-- The natural floor of `π / (4θ)` used to select a phase-mark amplification peak. -/
noncomputable def phaseMarkPeakRounds (θ : ℝ) : ℕ :=
  Nat.floor (Real.pi / (4 * θ))

/-- The natural ceiling of `π / (4θ) - 1/2` used to select a phase-mark crossing. -/
noncomputable def phaseMarkCrossingRounds (θ : ℝ) : ℕ :=
  Nat.ceil (Real.pi / (4 * θ) - 1 / 2)

/-- A record of query, gate, decoding-bit, and workspace-bit counts. -/
structure AECostLedger where

  queries : ℕ

  gates : ℕ

  decodeBits : ℕ

  workspaceBits : ℕ

/-- The workspace-size expression `2 * M * Fintype.card I`. -/
noncomputable def aeWorkspaceBits (M : ℕ) : ℕ :=
  M * (Fintype.card I) * 2

/-- A record of a nonnegative variance parameter, a positive scale, and a positive truncation
radius. -/
structure VarianceOnlyEndpoint where

  V : ℝ

  V_nonneg : 0 ≤ V

  σ : ℝ

  σ_pos : 0 < σ

  τ : ℝ

  τ_pos : 0 < τ

/-- The payoff obtained by applying `truncatedPayoff` with center `μ` and radius `τ`. -/
noncomputable def truncatedCentredPayoff (f : I → ℝ) (μ τ : ℝ) (i : I) : ℝ :=
  truncatedPayoff f μ τ i

/-- The tags distinguishing an individual data call from a threshold macro. -/
inductive AEAccessModel where

  | dataCall

  | thresholdMacro
  deriving DecidableEq, Repr

/-- The assigned number of access steps in an amplitude-estimation round, equal to six. -/
def aeRoundAccessSteps : ℕ := 6

/-- The assigned number of data calls per amplitude-estimation round, equal to one. -/
def aeRoundDataCalls : ℕ := 1

/-- The sorted median of `2 * r + 1` native amplitude-estimation decodings. -/
noncomputable def multiLayerMedian (M k r : ℕ) (ω : Fin (2 * r + 1) → Fin M) : ℝ :=
  sortedBlockMedian r (fun l => (nativeAEDecode M k (ω l) : ℝ))

/-- A search-resource record storing the access model, success value, natural query count, and
sensitivity. -/
structure SearchComplexity where

  model : AccessModel

  success : ℝ

  queries : ℕ

  sensitivity : ℝ

/-- The phase-mark record with `k` queries, success value `sin² ((2k + 1)θ)`, and sensitivity
`sin θ`. -/
noncomputable def phaseMarkComplexity (k : ℕ) (θ : ℝ) : SearchComplexity where
  model := .phaseMark
  success := (Real.sin ((2 * k + 1) * θ)) ^ 2
  queries := k
  sensitivity := Real.sin θ

/-- The product of the table row count and row width. -/
noncomputable def tableLoadBits (t : DatabaseTable) : ℕ :=
  t.rows * t.width

/-- One plus the length of the equal common prefix of the zipped rows. -/
noncomputable def rowCompareBits (r₁ r₂ : List Bool) : ℕ :=
  let common := (r₁.zip r₂).takeWhile (fun p => p.1 = p.2)
  common.length + 1

/-- The relative sampling-error expression evaluated at `relativeAEGrid a₀ ε`. -/
noncomputable def gridTightening (a₀ ε : ℝ) : ℝ :=
  relativeAESamplingError (relativeAEGrid a₀ ε) a₀

/-- The decoder that returns the data-register component of a workspace basis label as `some`. -/
def workspaceDataDecoder {n : ℕ} {W : Type} : ((Reg n × Bool) × W) → Option (Reg n) :=
  fun p => some p.1.1

/-- A search-comparison record storing the access model, success value, sensitivity, and a
real-valued query count. -/
structure MinimalSearchComplexity where

  model : AccessModel

  success : ℝ

  sensitivity : ℝ

  queries : ℝ

/-- The conversion of a search-resource record to a comparison record by casting its natural
query count to the reals. -/
def minimalComplexityOf (c : SearchComplexity) : MinimalSearchComplexity where
  model := c.model
  success := c.success
  sensitivity := c.sensitivity
  queries := (c.queries : ℝ)

/-- The bit-model sensitivity expression `1 / √N`. -/
noncomputable def bitModelSensitivity (N : ℕ) : ℝ := 1 / Real.sqrt N

/-- The bit-kickback record using the singleton-search iteration count, success value `1 - 1/N`,
and singleton-angle sensitivity. -/
noncomputable def bitModelProgramComplexity (n : ℕ) : SearchComplexity where
  model := .bitKickback
  success := 1 - 1 / (Fintype.card (Reg n) : ℝ)
  queries := singletonSearchIterations n
  sensitivity := Real.sin (singletonSearchAngle n)

/-- The bit-kickback comparison record with success value `2/3`, sensitivity `1 / √N`, and query
value `√N / 8`. -/
noncomputable def bitModelMinimalComplexity (N : ℕ) : MinimalSearchComplexity where
  model := .bitKickback
  success := 2 / 3
  sensitivity := bitModelSensitivity N
  queries := Real.sqrt N / 8

/-- The real-query comparison record obtained from `bitModelProgramComplexity`. -/
noncomputable def bitModelActualComplexity (n : ℕ) : MinimalSearchComplexity :=
  minimalComplexityOf (bitModelProgramComplexity n)

end Qatlib.Papers.FixedPtSearch14.FixedPoint
