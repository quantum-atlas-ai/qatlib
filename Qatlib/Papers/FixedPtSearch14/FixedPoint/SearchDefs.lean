/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Search
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchCoreDefs
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceSearchBounds
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.QuantumPayoffEstimation
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Concepts.StoppingCore.InterruptBridge.StoppingExt
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryLowerBounds

/-!
# Definitions for search readout and resource accounting

This module defines relative amplitude-estimation errors, compiled rounds, interruption
receipts, and variance contracts used alongside fixed-point search [YoderLowChuang2014].
`multiLayerReadout` packages measured records with native rational decodings, while
`matchedModel` restricts resource comparisons to identical access-model tags.

The table definitions supply a lexicographic row relation and comparison ledgers.
`linearScanMinimum` records the scan costs and returns the initial row index for a nonempty
table.

## Main statements

* `relativeAEError`: Sampling error together with finite decoding error.
* `compiledRound`: The six-step round after compilation to circuit instructions.
* `RelativeVarianceContract`: Nonnegativity, positive mean, and a relative variance bound.
* `scanMinRow_comps`: Exact comparison-count increment for the recursive scan.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Matrix
open scoped BigOperators Classical

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The marked-set measurement probability of the state prepared by `A` from `Ket j`. -/
noncomputable def unknownAmplitude (A : Matrix I I ℂ) (j : I) (S : Finset I) : ℝ :=
  MeasureProb (preparedAAState A j) S

/-- A positive lower-bound parameter `a₀` constrained to be at most one. -/
structure RelativeAEPromise where

  a₀ : ℝ

  a₀_pos : 0 < a₀

  a₀_le_one : a₀ ≤ 1

/-- The relative sampling-error expression `2π√((1 - a₀) / a₀) / M + π² / (a₀M²)`. -/
noncomputable def relativeAESamplingError (M a₀ : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt ((1 - a₀) / a₀) / M + Real.pi ^ 2 / (a₀ * M ^ 2)

/-- The relative sampling error plus the finite-decoding contribution `2⁻ᵏ / a₀`. -/
noncomputable def relativeAEError (M : ℝ) (k : ℕ) (a₀ : ℝ) : ℝ :=
  relativeAESamplingError M a₀ + ((2 : ℝ)⁻¹) ^ k / a₀

/-- The ceiling-based grid selected from the lower-bound promise `a₀` and relative accuracy `ε`. -/
noncomputable def relativeAEGrid (a₀ ε : ℝ) : ℕ :=
  Nat.ceil (2 * Real.pi * Real.sqrt ((1 - a₀) / a₀) / ε
    + Real.pi * Real.sqrt (2 / (a₀ * ε))) + 1

/-- The six access steps comprising threshold flips, a mark call, backward preparation, source
reflection, and forward preparation. -/
noncomputable def aeRoundSteps (M k : ℕ) :
    List (AEAccessStep (Fin M × (Bool × I))) :=
  [.fixed (permMatrix (phaseThresholdFlip M k)),
   .mark, .prepareBackward, .sourceReflection, .prepareForward,
   .fixed (permMatrix (phaseThresholdFlip M k))]

/-- The amplitude-estimation round length, equal to six. -/
def aeRoundLength : ℕ := 6

/-- The assigned oracle-call count per amplitude-estimation round, equal to one. -/
def aeRoundOracleCalls : ℕ := 1

/-- The circuit instructions obtained by compiling each access step of an amplitude-estimation
round. -/
noncomputable def compiledRound (M : ℕ) (A : Matrix I I ℂ) (j : I) (k : ℕ) :
    List (Step (Fin M × (Bool × I))) :=
  (aeRoundSteps M k).map (aeAccessInstruction M A j)

/-- An interruption receipt containing completed rounds, an offset within a round, workspace
memory, and an instruction log. -/
structure AEReceipt (I : Type) (M : ℕ) where

  completedRounds : ℕ

  roundOffset : ℕ

  memory : QState (Fin M × (Bool × I))

  log : List (Step (Fin M × (Bool × I)))

/-- The completed-oracle-call count read from the receipt as its number of completed rounds. -/
def AEReceipt.completedOracleCalls {I : Type} {M : ℕ} (rc : AEReceipt I M) : ℕ :=
  rc.completedRounds

/-- The natural subtraction of completed calls from the total `M - 1`. -/
def AEReceipt.remainingOracleCalls {I : Type} {M : ℕ} (rc : AEReceipt I M) : ℕ :=
  (M - 1) - rc.completedOracleCalls

/-- A record storing a nonnegative variance parameter and a positive scale. -/
structure VarianceCertificate where

  V : ℝ

  V_nonneg : 0 ≤ V

  σ : ℝ

  σ_pos : 0 < σ

/-- The payoff formed by clipping `f i - c` with `boundedClip τ` and adding the center `c`. -/
noncomputable def truncatedPayoff (f : I → ℝ) (c τ : ℝ) (i : I) : ℝ :=
  c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c)

/-- The condition that the variance parameter is nonnegative and the scale is positive. -/
def varianceOnlyExtraInput (V σ : ℝ) : Prop := 0 ≤ V ∧ 0 < σ

/-- The truncation-bias expression `V / (4 * τ)`. -/
noncomputable def truncationBias (V τ : ℝ) : ℝ := V / (4 * τ)

/-- The variance-tail expression `V / τ²`. -/
noncomputable def varianceOnlyTail (V τ : ℝ) : ℝ := V / (τ ^ 2)

/-- The assigned extra-round count for the variance-only interface, equal to one. -/
def varianceOnlyExtraRounds : ℕ := 1

/-- The requirement that a payoff is nonnegative, has positive expectation, and has variance at
most `B` times its squared expectation. -/
def RelativeVarianceContract (p : FinDist I) (f : I → ℝ) (B : ℕ) : Prop :=
  (∀ i, 0 ≤ f i) ∧ 0 < p.expect f ∧ p.variance f ≤ (B : ℝ) * (p.expect f)^2

/-- The requirement that the second moment about the payoff expectation is at most `V`. -/
def VarianceOnlyContract (p : FinDist I) (f : I → ℝ) (V : ℝ) : Prop :=
  (∑ i, p.prob i * (f i - p.expect f)^2) ≤ V

/-- The uniform probability distribution on `Fin 2`. -/
noncomputable def twoPointSource : FinDist (Fin 2) where
  prob _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by norm_num

/-- The two-point payoff taking value zero at index zero and `2 * t` at the other index. -/
noncomputable def twoPointPayoff (t : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then 0 else 2 * t

/-- A record storing a layer index, a measured `Fin M` record, and a rational decoded value. -/
structure MultiLayerReadout (M : ℕ) where

  layer : ℕ

  record : Fin M

  decoded : ℚ

/-- A record of layer count, distinct-record count, and oracle-call count. -/
structure MultiLayerLedger where

  layers : ℕ

  distinctRecords : ℕ

  oracleCalls : ℕ

/-- The list of measured records and native rational decodings from the `L` indexed layers. -/
noncomputable def multiLayerReadout (M k L : ℕ) (ω : Fin L → Fin M) :
    List (MultiLayerReadout M) :=
  (List.finRange L).map (fun l =>
    ⟨l.val, ω l, nativeAEDecode M k (ω l)⟩)

/-- The assigned oracle-call count `L * (M - 1)` for `L` layers. -/
def multiLayerOracleCalls (L M : ℕ) : ℕ := L * (M - 1)

/-- The access-model tags for phase marking, bit kickback, and adaptive feedback. -/
inductive AccessModel where

  | phaseMark

  | bitKickback

  | adaptiveFeedback
  deriving DecidableEq, Repr

/-- The proposition that two access-model tags are the same. -/
def matchedModel (m₁ m₂ : AccessModel) : Prop :=
  match m₁, m₂ with
  | .phaseMark, .phaseMark => True
  | .bitKickback, .bitKickback => True
  | .adaptiveFeedback, .adaptiveFeedback => True
  | _, _ => False

/-- The constant `c` returned unchanged for every access-model tag. -/
def modelConstant (m : AccessModel) (c : ℝ) : ℝ :=
  match m with
  | .phaseMark => c
  | .bitKickback => c
  | .adaptiveFeedback => c

/-- The sensitivity `sin θ` assigned to every access-model tag. -/
noncomputable def modelSensitivity (m : AccessModel) (θ : ℝ) : ℝ :=
  match m with
  | .phaseMark => Real.sin θ
  | .bitKickback => Real.sin θ
  | .adaptiveFeedback => Real.sin θ

/-- Strict lexicographic order on Boolean lists, with `false < true` and a proper prefix smaller
than its extension. -/
def BitRowLt : List Bool → List Bool → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | true :: xs, true :: ys => BitRowLt xs ys
  | false :: xs, false :: ys => BitRowLt xs ys
  | true :: _, false :: _ => False
  | false :: _, true :: _ => True

/-- A finite table of Boolean rows with a common specified width. -/
structure DatabaseTable where

  rows : ℕ

  entry : Fin rows → List Bool

  width : ℕ

  entry_width : ∀ i, (entry i).length = width

/-- A record of row loads, comparisons, and a stored bits-read count. -/
structure ComparisonLedger where

  loads : ℕ

  comparisons : ℕ

  bitsRead : ℕ

/-- The sum of loads and comparisons multiplied by the row width. -/
def ComparisonLedger.bitCost (l : ComparisonLedger) (width : ℕ) : ℕ :=
  (l.loads + l.comparisons) * width

/-- The sum of the row-bit parameter and the number of recorded loads. -/
def ComparisonLedger.spaceBits (l : ComparisonLedger) (rowBits : ℕ) : ℕ :=
  rowBits + l.loads

/-- The list of table entries in increasing row-index order. -/
noncomputable def tableRows (t : DatabaseTable) : List (List Bool) :=
  (List.finRange t.rows).map t.entry

/-- A recursive lexicographic minimum scan that updates the current best row and increments the
comparison counter once per visited row. -/
noncomputable def scanMinRow : List (List Bool) → List Bool → ℕ → List Bool × ℕ
  | [], best, comps => (best, comps)
  | r :: rs, best, comps =>
      scanMinRow rs (if BitRowLt r best then r else best) (comps + 1)

/-- Scanning a list increases the comparison counter by exactly the list length. -/
theorem scanMinRow_comps : ∀ (l : List (List Bool)) (best : List Bool) (comps : ℕ),
    (scanMinRow l best comps).2 = comps + l.length := by
  intro l
  induction l with
  | nil => simp [scanMinRow]
  | cons r rs ih =>
    simp [scanMinRow, ih]
    omega

/-- For a nonempty table, return index zero with a ledger counting all row loads and the
recursive scan comparisons; for an empty table, return `none` with zero counts. -/
noncomputable def linearScanMinimum (t : DatabaseTable) :
    Option (Fin t.rows) × ComparisonLedger :=
  if hr : 0 < t.rows then
    (some ⟨0, hr⟩,
      { loads := t.rows,
        comparisons := (scanMinRow (List.drop 1 (tableRows t)) (t.entry ⟨0, hr⟩) 0).2,
        bitsRead := t.rows + (scanMinRow (List.drop 1 (tableRows t)) (t.entry ⟨0, hr⟩) 0).2 })
  else
    (none, { loads := 0, comparisons := 0, bitsRead := 0 })

end Qatlib.Papers.FixedPtSearch14.FixedPoint
