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
set_option warningAsError false
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

noncomputable def unknownAmplitude (A : Matrix I I ℂ) (j : I) (S : Finset I) : ℝ :=
  MeasureProb (preparedAAState A j) S

structure RelativeAEPromise where

  a₀ : ℝ

  a₀_pos : 0 < a₀

  a₀_le_one : a₀ ≤ 1

noncomputable def relativeAESamplingError (M a₀ : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt ((1 - a₀) / a₀) / M + Real.pi ^ 2 / (a₀ * M ^ 2)

noncomputable def relativeAEError (M : ℝ) (k : ℕ) (a₀ : ℝ) : ℝ :=
  relativeAESamplingError M a₀ + ((2 : ℝ)⁻¹) ^ k / a₀

noncomputable def relativeAEGrid (a₀ ε : ℝ) : ℕ :=
  Nat.ceil (2 * Real.pi * Real.sqrt ((1 - a₀) / a₀) / ε
    + Real.pi * Real.sqrt (2 / (a₀ * ε))) + 1

noncomputable def aeRoundSteps (M k : ℕ) :
    List (AEAccessStep (Fin M × (Bool × I))) :=
  [.fixed (permMatrix (phaseThresholdFlip M k)),
   .mark, .prepareBackward, .sourceReflection, .prepareForward,
   .fixed (permMatrix (phaseThresholdFlip M k))]

def aeRoundLength : ℕ := 6

def aeRoundOracleCalls : ℕ := 1

noncomputable def compiledRound (M : ℕ) (A : Matrix I I ℂ) (j : I) (k : ℕ) :
    List (Step (Fin M × (Bool × I))) :=
  (aeRoundSteps M k).map (aeAccessInstruction M A j)

structure AEReceipt (I : Type) (M : ℕ) where

  completedRounds : ℕ

  roundOffset : ℕ

  memory : QState (Fin M × (Bool × I))

  log : List (Step (Fin M × (Bool × I)))

def AEReceipt.completedOracleCalls {I : Type} {M : ℕ} (rc : AEReceipt I M) : ℕ :=
  rc.completedRounds

def AEReceipt.remainingOracleCalls {I : Type} {M : ℕ} (rc : AEReceipt I M) : ℕ :=
  (M - 1) - rc.completedOracleCalls

structure VarianceCertificate where

  V : ℝ

  V_nonneg : 0 ≤ V

  σ : ℝ

  σ_pos : 0 < σ

noncomputable def truncatedPayoff (f : I → ℝ) (c τ : ℝ) (i : I) : ℝ :=
  c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c)

def varianceOnlyExtraInput (V σ : ℝ) : Prop := 0 ≤ V ∧ 0 < σ

noncomputable def truncationBias (V τ : ℝ) : ℝ := V / (4 * τ)

noncomputable def varianceOnlyTail (V τ : ℝ) : ℝ := V / (τ ^ 2)

def varianceOnlyExtraRounds : ℕ := 1

def RelativeVarianceContract (p : FinDist I) (f : I → ℝ) (B : ℕ) : Prop :=
  (∀ i, 0 ≤ f i) ∧ 0 < p.expect f ∧ p.variance f ≤ (B : ℝ) * (p.expect f)^2

def VarianceOnlyContract (p : FinDist I) (f : I → ℝ) (V : ℝ) : Prop :=
  (∑ i, p.prob i * (f i - p.expect f)^2) ≤ V

noncomputable def twoPointSource : FinDist (Fin 2) where
  prob _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by norm_num

noncomputable def twoPointPayoff (t : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then 0 else 2 * t

structure MultiLayerReadout (M : ℕ) where

  layer : ℕ

  record : Fin M

  decoded : ℚ

structure MultiLayerLedger where

  layers : ℕ

  distinctRecords : ℕ

  oracleCalls : ℕ

noncomputable def multiLayerReadout (M k L : ℕ) (ω : Fin L → Fin M) :
    List (MultiLayerReadout M) :=
  (List.finRange L).map (fun l =>
    ⟨l.val, ω l, nativeAEDecode M k (ω l)⟩)

def multiLayerOracleCalls (L M : ℕ) : ℕ := L * (M - 1)

inductive AccessModel where

  | phaseMark

  | bitKickback

  | adaptiveFeedback
  deriving DecidableEq, Repr

def matchedModel (m₁ m₂ : AccessModel) : Prop :=
  match m₁, m₂ with
  | .phaseMark, .phaseMark => True
  | .bitKickback, .bitKickback => True
  | .adaptiveFeedback, .adaptiveFeedback => True
  | _, _ => False

def modelConstant (m : AccessModel) (c : ℝ) : ℝ :=
  match m with
  | .phaseMark => c
  | .bitKickback => c
  | .adaptiveFeedback => c

noncomputable def modelSensitivity (m : AccessModel) (θ : ℝ) : ℝ :=
  match m with
  | .phaseMark => Real.sin θ
  | .bitKickback => Real.sin θ
  | .adaptiveFeedback => Real.sin θ

def BitRowLt : List Bool → List Bool → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | true :: xs, true :: ys => BitRowLt xs ys
  | false :: xs, false :: ys => BitRowLt xs ys
  | true :: _, false :: _ => False
  | false :: _, true :: _ => True

structure DatabaseTable where

  rows : ℕ

  entry : Fin rows → List Bool

  width : ℕ

  entry_width : ∀ i, (entry i).length = width

structure ComparisonLedger where

  loads : ℕ

  comparisons : ℕ

  bitsRead : ℕ

def ComparisonLedger.bitCost (l : ComparisonLedger) (width : ℕ) : ℕ :=
  (l.loads + l.comparisons) * width

def ComparisonLedger.spaceBits (l : ComparisonLedger) (rowBits : ℕ) : ℕ :=
  rowBits + l.loads

noncomputable def tableRows (t : DatabaseTable) : List (List Bool) :=
  (List.finRange t.rows).map t.entry

noncomputable def scanMinRow : List (List Bool) → List Bool → ℕ → List Bool × ℕ
  | [], best, comps => (best, comps)
  | r :: rs, best, comps =>
      scanMinRow rs (if BitRowLt r best then r else best) (comps + 1)

theorem scanMinRow_comps : ∀ (l : List (List Bool)) (best : List Bool) (comps : ℕ),
    (scanMinRow l best comps).2 = comps + l.length := by
  intro l
  induction l with
  | nil => simp [scanMinRow]
  | cons r rs ih =>
    simp [scanMinRow, ih]
    omega

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
