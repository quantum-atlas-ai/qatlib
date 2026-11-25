/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.BinHistoryUncompute
public import Qatlib.Concepts.QRAM.SignedReadout.Calibration
public import Qatlib.Concepts.QRAM.SignedReadout.EmbeddedReference
public import Qatlib.Concepts.QRAM.SignedReadout.BornReadoutStability
public import Qatlib.Concepts.QRAM.SignedReadout.InterferenceStability

@[expose] public section

/-!
# Signed interference on the decoded stencil workspace

The physical solution labels of [ChenXueChenEtAl2022], Section 3.3, are
in the right-hand stencil frame with clean phase and reciprocal tapes.
The empirical reference is loaded on those same labels. The target branch
marks the actual stencil success predicate before running the existing
inverse history word. The resulting conditional interference amplitude uses
the decoded solution coordinate and the empirical QRAM amplitude. This
interface accepts a coherent target gate on the stencil workspace.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds (tvDist)
open Qatlib.Foundations.InstrumentCore.Measurement (PostMeasure normalized_postMeasure)
open Qatlib.Foundations.PureStateMath (ApplyGate Ket MeasureProb Normalized QState normalized_applyGate)
open Qatlib.Foundations.PureStateMath.BornBridge (toEuclidean_fromVec)
open Qatlib.Foundations.QueryWordCore.Circuit (Run conjTranspose_mem_unitaryGroup)
open Qatlib.Concepts.QRAM.AmplitudeAccess (pathAmplitude)
open Qatlib.Concepts.QRAM.SignedReadout
open Qatlib.Foundations.QramData.SquaredNormTree (Address)
open scoped BigOperators

variable {n depth rows columns : ℕ}

/-- Each physical address has its own right-frame basis label with both tapes clean. -/
def stencilSolutionAddress (rowScratch : Fin rows) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition : Fin n → ℝ) (precision : ℝ) :
    Address depth ↪ BinStageWorkspace width condition precision (StencilWorkspace depth rows columns) where
  toFun a := (cleanPhaseTape width hWidth, (cleanReciprocalTape condition precision,
    stencilFrameLabel rowScratch columnScratch (Sum.inr a)))
  inj' := by
    intro a b h
    exact Sum.inl.inj (congrArg (fun p => p.2.2.2.1) h)

/-- The successful, calibrated interference at a physical address contains the decoded
stencil amplitude and the reference amplitude obtained from the first measurement record. -/
theorem stencil_signed_interference_entry {N : Type} [Fintype N] [DecidableEq N]
    (rowScratch : Fin rows) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ) (hWidth : ∀ t, 0 < width t)
    (C : Matrix (StencilWorkspace depth rows columns) N ℂ)
    (U : Matrix (StencilWorkspace depth rows columns) (StencilWorkspace depth rows columns) ℂ)
    (hC : Cᴴ * C = 1) (hU : Uᴴ = U) (hSq : U * U = 1)
    (target : Matrix (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns))
      (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns)) ℂ)
    (seed : BinStageWorkspace width condition precision (StencilWorkspace depth rows columns))
    (samples : List (Address depth)) (hSamples : samples ≠ []) (q : ℝ) (hq : 0 ≤ q)
    (hp : 0 < MeasureProb (ApplyGate target (Ket seed))
      (stencilBinSuccess rowScratch columnScratch width condition precision)) (b : Bool) (a : Address depth) :
    let place := stencilSolutionAddress (depth := depth) rowScratch columnScratch width hWidth condition precision
    let raw := ApplyGate target (Ket seed)
    let S := stencilBinSuccess rowScratch columnScratch width condition precision
    let p := MeasureProb raw S
    let D := (stencilBinPhasePreparation width condition threshold precision C U)ᴴ
    let B := embeddedReferencePreparation place seed samples
    let ψ := Run 1 (stencilBinHistoryUncompute width condition threshold precision C U) (PostMeasure raw S)
    let c := (Real.sqrt q : ℂ) * (pathAmplitude (empiricalTree samples) a : ℂ)
    heraldedInterferenceReadout target D B S q seed (b, true, place a) =
      (if b then (Real.sqrt p : ℂ) * ψ (place a) - c else (Real.sqrt p : ℂ) * ψ (place a) + c) /
        (2 * (Real.sqrt ((p + q) / 2) : ℂ)) := by
  intro place raw S p D B ψ c
  have hD : D ∈ Matrix.unitaryGroup _ ℂ := conjTranspose_mem_unitaryGroup
    (stencil_bin_phase_preparation_unitary width condition threshold precision C U hC hU hSq hWidth)
  have hB : B ∈ Matrix.unitaryGroup _ ℂ := embedded_reference_preparation_unitary place seed samples
  have hDecoder : ApplyGate D (PostMeasure (ApplyGate target (Ket seed)) S) = ψ :=
    (stencil_bin_history_uncompute_apply width condition threshold precision C U (PostMeasure raw S)).symm
  have hReference : ApplyGate B (Ket seed) (place a) = (pathAmplitude (empiricalTree samples) a : ℂ) :=
    embedded_reference_preparation_entry place seed samples hSamples a
  have hCircuit := heralded_interference_calibrated_entry target D B S q seed hD hB hq hp b (place a)
  dsimp only at hCircuit; rw [hDecoder, hReference] at hCircuit
  exact hCircuit

set_option synthInstance.maxSize 512 in
/-- Reversing the phase history of a positive-probability success branch
preserves the normalization of its conditional state. -/
theorem stencil_bin_decoded_success_normalized {N : Type} [Fintype N] [DecidableEq N]
    (rowScratch : Fin rows) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hWidth : ∀ t, 0 < width t)
    (C : Matrix (StencilWorkspace depth rows columns) N ℂ)
    (U : Matrix (StencilWorkspace depth rows columns) (StencilWorkspace depth rows columns) ℂ)
    (hC : Cᴴ * C = 1) (hU : Uᴴ = U) (hSq : U * U = 1)
    (raw : QState
      (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns)))
    (hp : 0 < MeasureProb raw (stencilBinSuccess rowScratch columnScratch width condition precision)) :
    Normalized (Run 1 (stencilBinHistoryUncompute width condition threshold precision C U)
      (PostMeasure raw (stencilBinSuccess rowScratch columnScratch width condition precision))) := by
  rw [stencil_bin_history_uncompute_apply]
  exact normalized_applyGate
    (conjTranspose_mem_unitaryGroup
      (stencil_bin_phase_preparation_unitary width condition threshold precision C U hC hU hSq hWidth))
    (normalized_postMeasure hp)

set_option synthInstance.maxSize 512 in
/-- The decoded success state gives the actual basis-shot law. Its distance
from the clean embedded real direction bounds the error of that law.
Measurements outside the clean address labels use a fixed fallback. -/
theorem stencil_basis_shot_tv_le {N : Type} [Fintype N] [DecidableEq N]
    (rowScratch : Fin rows) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ) (hWidth : ∀ t, 0 < width t)
    (C : Matrix (StencilWorkspace depth rows columns) N ℂ)
    (U : Matrix (StencilWorkspace depth rows columns) (StencilWorkspace depth rows columns) ℂ)
    (hC : Cᴴ * C = 1) (hU : Uᴴ = U) (hSq : U * U = 1)
    (target : Matrix (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns))
      (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns)) ℂ)
    (seed : BinStageWorkspace width condition precision (StencilWorkspace depth rows columns))
    (hp : 0 < MeasureProb (ApplyGate target (Ket seed))
      (stencilBinSuccess rowScratch columnScratch width condition precision))
    (direction : Address depth → ℝ) (hDirection : ∑ a, direction a ^ 2 = 1)
    (fallback : Address depth) :
    let place := stencilSolutionAddress (depth := depth) rowScratch columnScratch width hWidth condition precision
    let S := stencilBinSuccess rowScratch columnScratch width condition precision
    let ψ := Run 1 (stencilBinHistoryUncompute width condition threshold precision C U)
      (PostMeasure (ApplyGate target (Ket seed)) S)
    ∃ hψ, tvDist (bornReadoutLaw ψ hψ (readPlacedAddress place fallback))
        (basisSampleLaw direction hDirection) ≤
      ‖toEuclidean_fromVec (ψ - embeddedDirection place direction)‖ := by
  intro place S ψ
  have hψ : Normalized ψ :=
    stencil_bin_decoded_success_normalized rowScratch columnScratch width condition threshold precision
      hWidth C U hC hU hSq (ApplyGate target (Ket seed)) hp
  exact ⟨hψ, measured_basis_shot_tv_le place ψ hψ direction hDirection
    (readPlacedAddress place fallback) (read_placed_address place fallback)⟩

set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 800000 in
/-- For each basis record, the actual conditioned stencil interference shot
approximates the ideal signed law. The bound uses the whole decoded state,
including any amplitude outside the physical labels, and the calibration
imbalance of the experiment. -/
theorem stencil_interference_shot_tv_le {N : Type} [Fintype N] [DecidableEq N]
    (rowScratch : Fin rows) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ) (hWidth : ∀ t, 0 < width t)
    (C : Matrix (StencilWorkspace depth rows columns) N ℂ)
    (U : Matrix (StencilWorkspace depth rows columns) (StencilWorkspace depth rows columns) ℂ)
    (hC : Cᴴ * C = 1) (hU : Uᴴ = U) (hSq : U * U = 1)
    (target : Matrix (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns))
      (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns)) ℂ)
    (seed : BinStageWorkspace width condition precision (StencilWorkspace depth rows columns))
    (q : ℝ) (hq : 0 ≤ q) (hp : 0 < MeasureProb (ApplyGate target (Ket seed))
      (stencilBinSuccess rowScratch columnScratch width condition precision))
    (direction : Address depth → ℝ) (hDirection : ∑ a, direction a ^ 2 = 1)
    (samples : List (Address depth)) (hSamples : samples ≠ []) (fallback : Address depth) :
    let place := stencilSolutionAddress (depth := depth) rowScratch columnScratch width hWidth condition precision
    let raw := ApplyGate target (Ket seed)
    let S := stencilBinSuccess rowScratch columnScratch width condition precision
    let p := MeasureProb raw S
    let D := (stencilBinPhasePreparation width condition threshold precision C U)ᴴ
    let ref := embeddedReferencePreparation place seed samples
    let ψ := Run 1 (stencilBinHistoryUncompute width condition threshold precision C U) (PostMeasure raw S)
    let state := heraldedInterferenceReadout target D ref S q seed
    ∃ hState, tvDist (bornReadoutLaw state hState (placedInterferenceLabel place fallback))
      (interferenceSampleLaw direction hDirection samples hSamples) ≤
      ‖toEuclidean_fromVec (ψ - embeddedDirection place direction)‖ + 2 * (|p - q| / (p + q)) := by
  intro place raw S p D ref ψ state
  have hD : D ∈ Matrix.unitaryGroup _ ℂ := conjTranspose_mem_unitaryGroup
    (stencil_bin_phase_preparation_unitary width condition threshold precision C U hC hU hSq hWidth)
  have hDecoder : ApplyGate D (PostMeasure raw S) = ψ :=
    (stencil_bin_history_uncompute_apply width condition threshold precision C U (PostMeasure raw S)).symm
  have hBound := embedded_heralded_interference_shot_tv_le place fallback target D S q seed
    hD hq hp direction hDirection samples hSamples
  dsimp only at hBound
  rw [hDecoder] at hBound
  exact hBound

end Qatlib.Papers.QFVMChen22.TimeStep
