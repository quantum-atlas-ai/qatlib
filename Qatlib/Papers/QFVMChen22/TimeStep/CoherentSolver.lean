/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.SolverTomography

@[expose] public section

/-!
# Coherent preparation of the staged stencil output

The raw staged solver of [ChenXueChenEtAl2022], Sections 3.2–3.3, can be
run from a basis seed. Load the signed residual tree on the left stencil
addresses with the tapes clean, then apply the same ordered stage word as
`Qatlib.Papers.QFVMChen22.TimeStep.stencilBinOutput`. This supplies the
controlled target for the calibrated signed interference on the right
stencil addresses. The circuit in this file implements the unamplified
word and uses exact QRAM amplitudes.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 100000

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Foundations.InstrumentCore.Measurement (PostMeasure)
open Qatlib.Foundations.PureStateMath
  (ApplyGate Ket MeasureProb TensorState ZeroStr applyGate_mul ket_apply)
open Qatlib.Foundations.PureStateMath.BornBridge (relabelState_apply)
open Qatlib.Foundations.QueryWordCore.Circuit (Run)
open Qatlib.Concepts.QRAM.AmplitudeAccess (pathAmplitude)
open Qatlib.Concepts.QRAM.SignedReadout
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry)
open scoped BigOperators

variable {n depth rows columns : ℕ}

/-- Each residual address has a left-frame label on the clean phase and reciprocal tapes. -/
def stencilResidualAddress (rowScratch : Fin rows) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition : Fin n → ℝ) (precision : ℝ) :
    Address depth ↪ BinStageWorkspace width condition precision (StencilWorkspace depth rows columns) where
  toFun a := (cleanPhaseTape width hWidth, (cleanReciprocalTape condition precision,
    stencilFrameLabel rowScratch columnScratch (Sum.inl a)))
  inj' := by
    intro a b h
    exact Sum.inl.inj (congrArg (fun p => p.2.2.2.2.1) h)

/-- The clean solver input contains the signed residual exactly on the placed left labels. -/
private theorem stencil_bin_input_entry (rowScratch : Fin rows) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition : Fin n → ℝ) (precision : ℝ)
    (p : BinStageWorkspace width condition precision (StencilWorkspace depth rows columns)) :
    stencilBinInput rowScratch columnScratch residual width hWidth condition precision p =
      ∑ a, if p = stencilResidualAddress rowScratch columnScratch width hWidth condition precision a then
        (pathAmplitude residual a : ℂ) else 0 := by
  rcases p with ⟨phase, tape, signal⟩
  simp only [stencilBinInput, TensorState, ket_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    liftedResidual, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  simp_rw [stencil_walk_frame_apply]
  by_cases hPhase : phase = cleanPhaseTape width hWidth <;>
    by_cases hTape : tape = cleanReciprocalTape condition precision <;>
    simp [stencilResidualAddress, hPhase, hTape, ite_mul]

/-- The embedded signed QRAM residual preparation yields the staged solver's actual input. -/
theorem stencil_bin_input_preparation_apply (rowScratch : Fin rows) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (hValid : Valid residual) (hMass : 0 < mass residual)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition : Fin n → ℝ) (precision : ℝ) :
    let place := stencilResidualAddress (depth := depth) rowScratch columnScratch width hWidth condition precision
    let seed := place (ZeroStr depth)
    ApplyGate (embeddedTreePreparation place seed residual) (Ket seed) =
      stencilBinInput rowScratch columnScratch residual width hWidth condition precision := by
  intro place seed
  rw [embedded_tree_preparation_apply place seed residual hValid hMass]
  funext p
  let e := referenceWorkspaceEquiv place
  obtain ⟨v, rfl⟩ := e.surjective p
  rw [relabelState_apply, show (referenceWorkspaceEquiv place).symm (e v) = v from e.symm_apply_apply v,
    stencil_bin_input_entry]
  change (Sum.elim (fun a => (pathAmplitude residual a : ℂ)) 0) v =
    ∑ a, if e v = place a then (pathAmplitude residual a : ℂ) else 0
  rcases v with a | k
  · rw [show e (Sum.inl a) = place a from reference_workspace_inl place a]
    symm
    rw [Finset.sum_eq_single a]
    · simp
    · intro j _ hj
      exact ite_eq_right (fun h => hj (place.injective h).symm)
    · simp
  · have hNe (a : Address depth) : e (Sum.inr k) ≠ place a := by
      intro he
      have h := e.injective (he.trans (reference_workspace_inl place a).symm)
      cases h
    simp [hNe]

/-- Prepare the signed residual in the actual workspace and run all raw bin stages. -/
def stencilBinTargetPreparation (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns) (residual : Tree ℝ depth)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ) :
    Matrix (BinStageWorkspace width condition precision (StencilWorkspace depth geometry.stencilSize columns))
      (BinStageWorkspace width condition precision (StencilWorkspace depth geometry.stencilSize columns)) ℂ :=
  let place := stencilResidualAddress (depth := depth) rowScratch columnScratch width hWidth condition precision
  let gates := encodedStencilBinGates geometry coefficients entryScale rowScratch columnScratch
    width condition threshold precision
  gates.reverse.prod * embeddedTreePreparation place (place (ZeroStr depth)) residual

/-- The coherent target is a product of unitary gates on the same stencil workspace. -/
theorem stencil_bin_target_preparation_unitary (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns) (residual : Tree ℝ depth)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hValid : Valid residual) (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columns) :
    stencilBinTargetPreparation geometry coefficients entryScale rowScratch columnScratch residual
      width hWidth condition threshold precision ∈ Matrix.unitaryGroup _ ℂ := by
  have hProgram := encoded_stencil_bin_program_unitary geometry coefficients entryScale rowScratch columnScratch
    width condition threshold precision hScale hEntry hColumns hWidth
  dsimp only [stencilBinTargetPreparation]
  apply (Matrix.unitaryGroup (BinStageWorkspace width condition precision (StencilWorkspace depth geometry.stencilSize columns)) ℂ).mul_mem
  · apply (Matrix.unitaryGroup (BinStageWorkspace width condition precision (StencilWorkspace depth geometry.stencilSize columns)) ℂ).list_prod_mem
    intro V hV
    apply hProgram V
    unfold encodedStencilBinProgram
    exact List.mem_map_of_mem (List.mem_reverse.mp hV)
  · exact embedded_tree_preparation_unitary _ _ _ hValid

/-- Running the coherent target from its left zero-address seed is exactly the existing
unamplified solver output, including the decision history and reciprocal workspace. -/
theorem stencil_bin_target_preparation_apply (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns) (residual : Tree ℝ depth)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hValid : Valid residual) (hMass : 0 < mass residual) :
    let place := stencilResidualAddress (depth := depth) rowScratch columnScratch width hWidth condition precision
    let A := stencilBinTargetPreparation geometry coefficients entryScale rowScratch columnScratch residual
      width hWidth condition threshold precision
    ApplyGate A (Ket (place (ZeroStr depth))) =
      stencilBinOutput geometry coefficients entryScale rowScratch columnScratch residual
        width hWidth condition threshold precision := by
  intro place A
  dsimp only [A, place, stencilBinTargetPreparation]
  unfold stencilBinOutput encodedStencilBinProgram
  rw [applyGate_mul, stencil_bin_input_preparation_apply rowScratch columnScratch residual hValid hMass,
    ← run_gate_list_eq_apply_reverse_product]

/-- The interference of the raw staged solver with its empirical reference uses the decoded
solution amplitude of the same solver run and the calibrated reference amplitude. -/
theorem stencil_bin_signed_interference_entry (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns) (residual : Tree ℝ depth)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hValid : Valid residual) (hMass : 0 < mass residual) (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columns)
    (samples : List (Address depth)) (hSamples : samples ≠ []) (q : ℝ) (hq : 0 ≤ q)
    (hp : 0 < MeasureProb (stencilBinOutput geometry coefficients entryScale rowScratch columnScratch residual
      width hWidth condition threshold precision) (stencilBinSuccess rowScratch columnScratch width condition precision))
    (b : Bool) (a : Address depth) :
    let seed := stencilResidualAddress rowScratch columnScratch width hWidth condition precision (ZeroStr depth)
    let place := stencilSolutionAddress (depth := depth) rowScratch columnScratch width hWidth condition precision
    let C := stencilWalkFrame depth rowScratch columnScratch
    let U := stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch
    let A := stencilBinTargetPreparation geometry coefficients entryScale rowScratch columnScratch residual
      width hWidth condition threshold precision
    let raw := stencilBinOutput geometry coefficients entryScale rowScratch columnScratch residual
      width hWidth condition threshold precision
    let S := stencilBinSuccess rowScratch columnScratch width condition precision
    let p := MeasureProb raw S
    let D := (stencilBinPhasePreparation width condition threshold precision C U)ᴴ
    let B := embeddedReferencePreparation place seed samples
    let ψ := Run 1 (stencilBinHistoryUncompute width condition threshold precision C U) (PostMeasure raw S)
    let c := (Real.sqrt q : ℂ) * (pathAmplitude (empiricalTree samples) a : ℂ)
    heraldedInterferenceReadout A D B S q seed (b, true, place a) =
      (if b then (Real.sqrt p : ℂ) * ψ (place a) - c else (Real.sqrt p : ℂ) * ψ (place a) + c) /
        (2 * (Real.sqrt ((p + q) / 2) : ℂ)) := by
  intro seed place C U A raw S p D B ψ c
  obtain ⟨hC, hU, hSq, _⟩ :=
    stencil_walk_encoding geometry coefficients entryScale rowScratch columnScratch hScale hEntry hColumns
  have hRaw : ApplyGate A (Ket seed) = raw := stencil_bin_target_preparation_apply geometry coefficients entryScale
    rowScratch columnScratch residual width hWidth condition threshold precision hValid hMass
  have hPos : 0 < MeasureProb (ApplyGate A (Ket seed)) S := hRaw.symm ▸ hp
  have hCircuit := stencil_signed_interference_entry rowScratch columnScratch width condition threshold precision hWidth
    C U hC hU hSq A seed samples hSamples q hq hPos b a
  dsimp only at hCircuit
  rw [hRaw] at hCircuit
  exact hCircuit

end Qatlib.Papers.QFVMChen22.TimeStep
