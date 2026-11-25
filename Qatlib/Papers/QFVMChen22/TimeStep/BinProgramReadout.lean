/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.BinStage
public import Qatlib.Concepts.SketchArith.GramAction.PostMeasurePerturbation

@[expose] public section

/-!
# Cached residual input and success register of the staged solver

[ChenXueChenEtAl2022], Section 3.3, prepares the signed residual from its
QRAM tree and reads a solution from a marked branch. The staged solver
starts with the entire decision tape and all coefficient registers clean.
The stencil frame occupies an explicit set of basis labels. The event
for reading a raw right-register solution requires an accepted bin and
clean coefficient labels. Its definition retains the phase histories.
The clean coefficient slice of a selected stage agrees with its compressed
reciprocal. A sequence of per-stage reference errors controls the error of the
raw output and its normalized successful branch, given a reference success
gap. A concrete success bound requires estimates for a spectral reference.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Foundations.MatrixAlgebra.HermitianLift (embedding nativeEmbedding qubitSplit)
open Qatlib.Foundations.PureStateMath
  (ApplyGate BornProb Ket MeasureProb Normalized QState TensorState ZeroStr
    ket_apply normalized_ket normalized_tensorState)
open Qatlib.Foundations.PureStateMath.BornBridge (toEuclidean_fromVec)
open Qatlib.Foundations.InstrumentCore.Measurement (PostMeasure)
open Qatlib.Foundations.QueryWordCore.Circuit (Run Step run_append run_gate run_nil)
open Qatlib.Concepts.BlockEncoding.LCU (prepareLift)
open Qatlib.Concepts.Execution.WorkspaceCP (IsIsometry compress)
open Qatlib.Concepts.LchsSimulation.StaticLchs (norm_applyGate_of_mem_unitaryGroup)
open Qatlib.Concepts.QsvtCore.PhaseExistence (leftFrame rightFrame)
open Qatlib.Concepts.SketchArith.GramAction (postMeasure_error_of_gap)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry)
open scoped BigOperators Classical

variable {n depth rows columns : ℕ}

/-- The basis location of each input or output column of the lifted stencil frame. -/
def stencilFrameLabel (rowScratch : Fin rows) (columnScratch : Fin columns) :
    Address depth ⊕ Address depth → StencilWorkspace depth rows columns :=
  Sum.elim
    (fun row => (0, (Sum.inr rowScratch, (Sum.inl row, false))))
    (fun column => (1, (Sum.inl column, (Sum.inr columnScratch, false))))

/-- Each column of the actual stencil isometry is the ket at its assigned basis location. -/
theorem stencil_walk_frame_apply (rowScratch : Fin rows) (columnScratch : Fin columns)
    (p : StencilWorkspace depth rows columns) (i : Address depth ⊕ Address depth) :
    stencilWalkFrame depth rowScratch columnScratch p i =
      if p = stencilFrameLabel rowScratch columnScratch i then 1 else 0 := by
  obtain ⟨side, p⟩ := p
  fin_cases side <;> cases i <;>
    simp [stencilWalkFrame, nativeEmbedding, embedding, qubitSplit, leftFrame, rightFrame,
      stencilFrameLabel, Matrix.submatrix_apply]

/-- All stage counters, the internal flags, and the decision bits start clean. -/
def cleanPhaseTape (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) : PhaseTape width :=
  fun t => (false, (⟨0, hWidth t⟩, false))

/-- The coefficient tape starts at the preparation label of every reciprocal stage. -/
def cleanReciprocalTape (condition : Fin n → ℝ) (precision : ℝ) : ReciprocalTape condition precision :=
  fun _ => Sum.inl 0

section ReciprocalReadout

variable {M N J : Type} [Fintype M] [DecidableEq M] [Fintype N] [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
/-- Multiplication by the preparation lift appends the preparation state. -/
private theorem prepare_lift_apply (a : J → ℂ) (ψ : QState M) :
    prepareLift a *ᵥ ψ = TensorState a ψ := by
  funext p
  rcases p with ⟨j, m⟩
  simp [Matrix.mulVec, dotProduct, prepareLift, TensorState, ite_mul]

/-- The adjoint of a basis preparation lift reads the corresponding register slice. -/
private theorem prepare_lift_ket_adjoint_apply (j : J) (ψ : QState (J × M)) :
    (prepareLift (Ket j))ᴴ *ᵥ ψ = fun m => ψ (j, m) := by
  funext m
  simp [Matrix.mulVec, dotProduct, prepareLift, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, ket_apply, ite_mul, apply_ite]

set_option maxHeartbeats 500000 in
/-- With the coefficient tape initially clean, the selected stage's clean output slice is
the clean corner of its reciprocal on the physical signal at that phase history. -/
theorem conditional_bin_reciprocal_clean_signal (width : Fin n → ℕ) (condition : Fin n → ℝ)
    (precision mass : ℝ) (t : Fin n) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (phase : PhaseTape width) (hAccept : firstBinAcceptance (width := width) t phase)
    (packet : PhaseTape width → QState M) :
    let clean := cleanReciprocalTape condition precision
    let frame := prepareLift (I := M) (Ket (clean t))
    (fun m => ApplyGate (conditionalBinReciprocal width condition precision mass t C U)
      (fun p => Ket clean p.2.1 * packet p.1 p.2.2) (phase, (clean, m))) =
      compress frame (binReciprocalUnitary (condition t) precision mass C U) frame *ᵥ packet phase := by
  intro clean frame
  let e := focusBinReciprocal (M := M) width condition precision t
  let spectators : BinStageSpectators width condition precision t :=
    (phase, fun s => clean s.val)
  let input : QState (BinStageWorkspace width condition precision M) :=
    fun p => Ket clean p.2.1 * packet p.1 p.2.2
  have hSlice : (fun q => input (e.symm (spectators, q))) =
      TensorState (Ket (clean t)) (packet phase) := by
    funext q
    let p := e.symm (spectators, q)
    have hPhase : p.1 = phase := rfl
    have hSignal : p.2.2 = q.2 := rfl
    have hClean : p.2.1 = clean ↔ q.1 = clean t := by
      have hShape : p = (phase, (clean, q.2)) ↔ q.1 = clean t := by
        change e.symm (spectators, q) = (phase, (clean, q.2)) ↔ _
        rw [Equiv.symm_apply_eq]
        change (spectators, q) = (spectators, (clean t, q.2)) ↔ _
        exact ⟨fun h => congrArg (fun x => x.2.1) h, fun h => Prod.ext rfl (Prod.ext h rfl)⟩
      exact ⟨fun h => hShape.mp (Prod.ext hPhase (Prod.ext h hSignal)),
        fun h => congrArg (fun x => x.2.1) (hShape.mpr h)⟩
    change Ket clean p.2.1 * packet p.1 p.2.2 = _
    by_cases hq : q.1 = clean t
    · simp [TensorState, hClean.mpr hq, hq, hPhase, hSignal]
    · simp [TensorState, ket_apply, mt hClean.mp hq, hq]
  funext m
  rw [conditional_bin_reciprocal_action]
  change ApplyGate (if firstBinAcceptance (width := width) t phase then
      binReciprocalUnitary (condition t) precision mass C U else 1)
    (fun q => input (e.symm (spectators, q))) (clean t, m) = _
  rw [ite_eq_left hAccept, hSlice]
  change _ = (((prepareLift (I := M) (Ket (clean t)))ᴴ *
    binReciprocalUnitary (condition t) precision mass C U *
    prepareLift (I := M) (Ket (clean t))) *ᵥ packet phase) m
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, prepare_lift_apply,
    prepare_lift_ket_adjoint_apply]
  rfl

/-- Encoding the input in the stencil frame and decoding the clean signal slice identifies
the selected bin of the staged circuit with the compressed reciprocal. -/
theorem conditional_bin_reciprocal_compressed (width : Fin n → ℕ) (condition : Fin n → ℝ)
    (precision mass : ℝ) (t : Fin n) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (phase : PhaseTape width) (hAccept : firstBinAcceptance (width := width) t phase)
    (packet : PhaseTape width → QState N) :
    let clean := cleanReciprocalTape condition precision
    Cᴴ *ᵥ (fun m => ApplyGate (conditionalBinReciprocal width condition precision mass t C U)
      (fun p => Ket clean p.2.1 * (C *ᵥ packet p.1) p.2.2) (phase, (clean, m))) =
      compressedBinReciprocal (condition t) precision mass C U *ᵥ packet phase := by
  intro clean
  rw [conditional_bin_reciprocal_clean_signal width condition precision mass t C U phase hAccept
    (fun history => C *ᵥ packet history),
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [compressedBinReciprocal, cleanReciprocalTape]

end ReciprocalReadout

/-- Initialize the actual staged program with the signed QRAM residual in the stencil frame. -/
def stencilBinInput (rowScratch : Fin rows) (columnScratch : Fin columns) (residual : Tree ℝ depth)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition : Fin n → ℝ) (precision : ℝ) :
    QState (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns)) :=
  TensorState (Ket (cleanPhaseTape width hWidth))
    (TensorState (Ket (cleanReciprocalTape condition precision))
      (stencilWalkFrame depth rowScratch columnScratch *ᵥ liftedResidual residual))

/-- The staged input uses the result of the actual signed residual preparation at the
zero address in the left half of the lift. -/
theorem stencil_bin_input_from_qram (rowScratch : Fin rows) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (hValid : Valid residual) (hMass : 0 < mass residual)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition : Fin n → ℝ) (precision : ℝ) :
    stencilBinInput rowScratch columnScratch residual width hWidth condition precision =
      TensorState (Ket (cleanPhaseTape width hWidth))
        (TensorState (Ket (cleanReciprocalTape condition precision))
          (stencilWalkFrame depth rowScratch columnScratch *ᵥ
            ApplyGate (liftedResidualPreparation residual) (Ket (Sum.inl (ZeroStr depth))))) := by
  unfold stencilBinInput
  rw [lifted_residual_preparation_apply residual hValid hMass]

/-- A positive valid residual produces a normalized input when the stencil frame is isometric. -/
theorem stencil_bin_input_normalized (rowScratch : Fin rows) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (hValid : Valid residual) (hMass : 0 < mass residual)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition : Fin n → ℝ) (precision : ℝ)
    (hFrame : IsIsometry (stencilWalkFrame depth rowScratch columnScratch)) :
    Normalized (stencilBinInput rowScratch columnScratch residual width hWidth condition precision) := by
  have hSignal := Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.normalized_mulVec
    hFrame (lifted_residual_normalized residual hValid hMass)
  exact normalized_tensorState (normalized_ket _) (normalized_tensorState (normalized_ket _) hSignal)

/-- Run the actual stencil stage word on the clean tape and cached residual. -/
def stencilBinOutput (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns) (residual : Tree ℝ depth)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ) :
    QState (BinStageWorkspace width condition precision (StencilWorkspace depth geometry.stencilSize columns)) :=
  Run 1 (encodedStencilBinProgram geometry coefficients entryScale rowScratch columnScratch
    width condition threshold precision) (stencilBinInput rowScratch columnScratch residual
      width hWidth condition precision)

/-- Legality of the encoded stencil and consistency of the residual tree make the raw program
output a normalized state on all its registers. -/
theorem stencil_bin_output_normalized (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (hValid : Valid residual) (hMass : 0 < mass residual)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columns) :
    Normalized (stencilBinOutput geometry coefficients entryScale rowScratch columnScratch
      residual width hWidth condition threshold precision) := by
  have hC := (stencil_walk_encoding geometry coefficients entryScale rowScratch columnScratch
    hScale hEntry hColumns).1
  have hWord := encoded_stencil_bin_program_unitary geometry coefficients entryScale rowScratch columnScratch
    width condition threshold precision hScale hEntry hColumns hWidth
  let H := BinStageWorkspace width condition precision (StencilWorkspace depth geometry.stencilSize columns)
  have hOracle : (1 : Matrix H H ℂ) ∈ Matrix.unitaryGroup H ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_one, Matrix.one_mul]
  exact hWord.normalized_run hOracle
    (stencil_bin_input_normalized rowScratch columnScratch residual hValid hMass width hWidth condition precision hC)

/-- Select the raw branch with an accepted bin, clean coefficient labels, and a physical
address in the right stencil register. -/
def stencilBinSuccess (rowScratch : Fin rows) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision : ℝ) :
    Finset (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns)) :=
  Finset.univ.filter fun p =>
    (∃ t, (p.1 t).1 = true) ∧
      p.2.1 = cleanReciprocalTape condition precision ∧
      ∃ column : Address depth, p.2.2 = stencilFrameLabel rowScratch columnScratch (Sum.inr column)

/-- The raw success mass sums the right-register probabilities over the distinct accepted
phase histories at the clean coefficient labels. -/
theorem stencil_bin_success_mass (rowScratch : Fin rows) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision : ℝ)
    (ψ : QState (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns))) :
    MeasureProb ψ (stencilBinSuccess rowScratch columnScratch width condition precision) =
      ∑ phase ∈ Finset.univ.filter (fun (phase : PhaseTape width) => ∃ t, (phase t).1 = true),
        ∑ column : Address depth, BornProb ψ (phase, (cleanReciprocalTape condition precision,
          stencilFrameLabel rowScratch columnScratch (Sum.inr column))) := by
  let clean := cleanReciprocalTape condition precision
  let phases := Finset.univ.filter fun (phase : PhaseTape width) => ∃ t, (phase t).1 = true
  let label (p : PhaseTape width × Address depth) :
      BinStageWorkspace width condition precision (StencilWorkspace depth rows columns) :=
    (p.1, (clean, stencilFrameLabel rowScratch columnScratch (Sum.inr p.2)))
  have hInjective : Function.Injective label := by
    intro p q h
    have hPhase : (label p).1 = (label q).1 := congrArg Prod.fst h
    have hColumn : (Sum.inl p.2 : Address depth ⊕ Fin rows) = Sum.inl q.2 :=
      congrArg (fun i => i.2.2.2.1) h
    exact Prod.ext hPhase (Sum.inl.inj hColumn)
  have hEvent : stencilBinSuccess rowScratch columnScratch width condition precision =
      (phases ×ˢ (Finset.univ : Finset (Address depth))).image label := by
    ext p
    constructor
    · intro hp
      obtain ⟨hPhase, hClean, column, hColumn⟩ := (Finset.mem_filter.mp hp).2
      refine Finset.mem_image.mpr ⟨(p.1, column), Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPhase⟩
      · exact Prod.ext rfl (Prod.ext hClean.symm hColumn.symm)
    · intro hp
      obtain ⟨⟨phase, column⟩, hPair, rfl⟩ := Finset.mem_image.mp hp
      have hPhase := (Finset.mem_filter.mp (Finset.mem_product.mp hPair).1).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPhase, rfl, column, rfl⟩
  rw [hEvent, MeasureProb, Finset.sum_image (fun _ _ _ _ h => hInjective h), Finset.sum_product]

/-- Errors along a reference sequence of states add when each actual stage is unitary. -/
theorem ordered_stage_error {H : Type} [Fintype H] [DecidableEq H]
    (gates : Fin n → Matrix H H ℂ) (reference : Fin (n + 1) → QState H) (error : Fin n → ℝ)
    (hUnitary : ∀ t, gates t ∈ Matrix.unitaryGroup H ℂ)
    (hLocal : ∀ t, ‖toEuclidean_fromVec (ApplyGate (gates t) (reference t.castSucc) - reference t.succ)‖ ≤ error t) :
    ‖toEuclidean_fromVec
      (Run 1 ((List.finRange n).map fun t => Step.gate (gates t)) (reference 0) - reference (Fin.last n))‖ ≤
        ∑ t, error t := by
  induction n with
  | zero =>
    have hLast : Fin.last 0 = 0 := Fin.ext rfl
    simp [hLast, toEuclidean_fromVec]
  | succ n ih =>
    rw [List.finRange_succ_last, List.map_append, List.map_map, List.map_singleton, run_append, run_gate, run_nil,
      Fin.sum_univ_castSucc]
    let before := Run (1 : Matrix H H ℂ)
      ((List.finRange n).map fun t => Step.gate (gates t.castSucc)) (reference 0)
    let last := Fin.last n
    let mid := reference last.castSucc
    let final := reference last.succ
    let gate := gates last
    have hPrefix : ‖toEuclidean_fromVec (before - mid)‖ ≤ ∑ t : Fin n, error t.castSucc :=
      ih (fun t => gates t.castSucc) (fun t => reference t.castSucc) (fun t => error t.castSucc)
        (fun t => hUnitary t.castSucc) (fun t => hLocal t.castSucc)
    have hDistance :
        ‖toEuclidean_fromVec (ApplyGate gate before - ApplyGate gate mid)‖ =
          ‖toEuclidean_fromVec (before - mid)‖ := by
      rw [show ApplyGate gate before - ApplyGate gate mid = ApplyGate gate (before - mid) by
        simp only [ApplyGate, Matrix.mulVec_sub]]
      exact norm_applyGate_of_mem_unitaryGroup (hUnitary last) _
    change ‖toEuclidean_fromVec (ApplyGate gate before - final)‖ ≤
      (∑ t : Fin n, error t.castSucc) + error last
    calc
      _ ≤ ‖toEuclidean_fromVec (ApplyGate gate before - ApplyGate gate mid)‖ +
          ‖toEuclidean_fromVec (ApplyGate gate mid - final)‖ := by
        change ‖toEuclidean_fromVec (ApplyGate gate before) - toEuclidean_fromVec final‖ ≤
          ‖toEuclidean_fromVec (ApplyGate gate before) - toEuclidean_fromVec (ApplyGate gate mid)‖ +
          ‖toEuclidean_fromVec (ApplyGate gate mid) - toEuclidean_fromVec final‖
        rw [← sub_add_sub_cancel (toEuclidean_fromVec (ApplyGate gate before))
          (toEuclidean_fromVec (ApplyGate gate mid)) (toEuclidean_fromVec final)]
        exact norm_add_le _ _
      _ ≤ _ := by
        rw [hDistance]
        exact add_le_add hPrefix (hLocal last)

set_option maxHeartbeats 700000 in
/-- Compare the actual QRAM-initialized stencil output with the final state of a reference
sequence using errors on each reference input under the actual bin stage. -/
theorem stencil_bin_output_error (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns) (residual : Tree ℝ depth)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columns)
    (reference : Fin (n + 1) → QState
      (BinStageWorkspace width condition precision (StencilWorkspace depth geometry.stencilSize columns)))
    (error : Fin n → ℝ)
    (hInput : reference 0 = stencilBinInput rowScratch columnScratch residual width hWidth condition precision)
    (hLocal : ∀ t, ‖toEuclidean_fromVec (ApplyGate
      (stencilBinStage width condition precision (commonBinMass condition precision) t (threshold t)
        (stencilWalkFrame depth rowScratch columnScratch)
        (stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch))
      (reference t.castSucc) - reference t.succ)‖ ≤ error t) :
    ‖toEuclidean_fromVec (stencilBinOutput geometry coefficients entryScale rowScratch columnScratch
      residual width hWidth condition threshold precision - reference (Fin.last n))‖ ≤ ∑ t, error t := by
  let gates t := stencilBinStage width condition precision (commonBinMass condition precision) t (threshold t)
    (stencilWalkFrame depth rowScratch columnScratch)
    (stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch)
  have hWord := encoded_stencil_bin_program_unitary geometry coefficients entryScale rowScratch columnScratch
    width condition threshold precision hScale hEntry hColumns hWidth
  have hGate (t : Fin n) : gates t ∈ Matrix.unitaryGroup _ ℂ := by
    apply hWord
    exact List.mem_map.mpr ⟨gates t, List.mem_map.mpr ⟨t, List.mem_finRange t, rfl⟩, rfl⟩
  unfold stencilBinOutput encodedStencilBinProgram encodedStencilBinGates
  rw [← hInput, List.map_map]
  exact ordered_stage_error gates reference error hGate hLocal

set_option maxHeartbeats 700000 in
/-- A reference success amplitude larger than the sum of the stage errors certifies positive
success for the actual QRAM-initialized circuit and bounds its conditional readout error. -/
theorem stencil_bin_postmeasure_error (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns) (residual : Tree ℝ depth)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columns)
    (reference : Fin (n + 1) → QState
      (BinStageWorkspace width condition precision (StencilWorkspace depth geometry.stencilSize columns)))
    (error : Fin n → ℝ)
    (hInput : reference 0 = stencilBinInput rowScratch columnScratch residual width hWidth condition precision)
    (hLocal : ∀ t, ‖toEuclidean_fromVec (ApplyGate
      (stencilBinStage width condition precision (commonBinMass condition precision) t (threshold t)
        (stencilWalkFrame depth rowScratch columnScratch)
        (stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch))
      (reference t.castSucc) - reference t.succ)‖ ≤ error t)
    (hGap : (∑ t, error t) < Real.sqrt (MeasureProb (reference (Fin.last n))
      (stencilBinSuccess rowScratch columnScratch width condition precision))) :
    let output := stencilBinOutput geometry coefficients entryScale rowScratch columnScratch
      residual width hWidth condition threshold precision
    let success := stencilBinSuccess rowScratch columnScratch width condition precision
    0 < MeasureProb output success ∧
      ‖toEuclidean_fromVec (PostMeasure output success - PostMeasure (reference (Fin.last n)) success)‖ ≤
        2 * (∑ t, error t) / Real.sqrt (MeasureProb (reference (Fin.last n)) success) := by
  intro output success
  exact postMeasure_error_of_gap _ _ _
    (stencil_bin_output_error geometry coefficients entryScale rowScratch columnScratch residual
      width hWidth condition threshold precision hScale hEntry hColumns reference error hInput hLocal) hGap

end Qatlib.Papers.QFVMChen22.TimeStep
