/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.CoherentSolver
public import Qatlib.Papers.QFVMChen22.TimeStep.BinClock
public import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification

@[expose] public section

/-!
# Coherent preparation of the amplified stencil output

The nested amplification word for [ChenXueChenEtAl2022], Section 3.3,
acts on a data space with a single clock value. Its matrix can be
viewed on the data space itself by removing that singleton factor.
Compose it with the same left-frame QRAM residual loader used for the
raw word. The resulting target gate inherits the amplified success
probability, conditional solution state, and weighted oracle ledger.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 100000

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Concepts.BlockEncoding.EncodingCore (relabelGate_mem_unitary)
open Qatlib.Concepts.LchsSimulation.StaticLchs (prepared_aa_reflection_and_access)
open Qatlib.Concepts.QlsReadoutSpec.Amplification
  (Word legal wordMatrix clean run clockState nestedWord extendClock plainAmplitude quasinorm23 seedProjector weightedCost)
open Qatlib.Concepts.QlsReadoutSpec.ProgramModel (wordMatrix_unitary)
open Qatlib.Foundations.InstrumentCore.Measurement (PostMeasure Projector)
open Qatlib.Foundations.PureStateMath (ApplyGate Ket MeasureProb QState ZeroStr applyGate_mul)
open Qatlib.Foundations.PureStateMath.BornBridge (relabelGate relabelState relabelState_apply applyGate_relabelGate)
open Qatlib.Foundations.PureStateMath.Reflection (ReflectionAbout)
open Qatlib.Concepts.QRAM.SignedReadout (embeddedTreePreparation embedded_tree_preparation_unitary)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry)

/-- Relabel a word with a singleton control clock as a gate on the data space. -/
def clockWordGate {I : Type} [Fintype I] [DecidableEq I]
    (oracles : ℕ → Matrix I I ℂ) (word : Word I 1) : Matrix I I ℂ :=
  relabelGate (Equiv.prodUnique I (Fin 1)) (wordMatrix oracles word)

/-- A legal single-clock word over unitary oracles gives a unitary data gate. -/
theorem clock_word_gate_unitary {I : Type} [Fintype I] [DecidableEq I] {slots : ℕ}
    (oracles : ℕ → Matrix I I ℂ) (word : Word I 1)
    (hOracles : ∀ j < slots, oracles j ∈ Matrix.unitaryGroup I ℂ) (hWord : legal slots word) :
    clockWordGate oracles word ∈ Matrix.unitaryGroup I ℂ :=
  relabelGate_mem_unitary (wordMatrix_unitary oracles word hOracles hWord) _

/-- Applying the relabeled matrix agrees with the original word on its only clock slice. -/
theorem clock_word_gate_apply {I : Type} [Fintype I] [DecidableEq I]
    (oracles : ℕ → Matrix I I ℂ) (word : Word I 1) (ψ : QState I) :
    ApplyGate (clockWordGate oracles word) ψ = clockState oracles word ψ := by
  let e := Equiv.prodUnique I (Fin 1)
  have hSlice (i : I) : e.symm i = (i, (0 : Fin 1)) :=
    Prod.ext rfl (Subsingleton.elim _ _)
  have hInput : relabelState e (clean 1 Nat.zero_lt_one ψ) = ψ := by
    funext i
    simp [relabelState_apply, hSlice, clean]
  calc
    ApplyGate (clockWordGate oracles word) ψ =
        ApplyGate (relabelGate e (wordMatrix oracles word)) (relabelState e (clean 1 Nat.zero_lt_one ψ)) :=
      congrArg (ApplyGate (relabelGate e (wordMatrix oracles word))) hInput.symm
    _ = relabelState e (ApplyGate (wordMatrix oracles word) (clean 1 Nat.zero_lt_one ψ)) :=
      applyGate_relabelGate e _ _
    _ = _ := by
      funext i
      simp only [relabelState_apply, hSlice, clockState, run, ApplyGate]

variable {n depth rows columns : ℕ}

/-- The amplified word's seed reflection can be executed by undoing the residual loader,
reflecting about the left zero-address seed, and loading the residual again. -/
theorem stencil_residual_seed_reflection (rowScratch : Fin rows) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition : Fin n → ℝ) (precision : ℝ) (hValid : Valid residual) (hMass : 0 < mass residual) :
    let place := stencilResidualAddress (depth := depth) rowScratch columnScratch width hWidth condition precision
    let seed := place (ZeroStr depth)
    let L := embeddedTreePreparation place seed residual
    ReflectionAbout (seedProjector (stencilBinInput rowScratch columnScratch residual width hWidth condition precision)) =
      L * ReflectionAbout (seedProjector (Ket seed)) * Lᴴ := by
  intro place seed L
  have hUnitary : L ∈ Matrix.unitaryGroup _ ℂ := embedded_tree_preparation_unitary place seed residual hValid
  have hReflection := (prepared_aa_reflection_and_access L seed ∅ hUnitary).2.2.1
  change L * ReflectionAbout (seedProjector (Ket seed)) * Lᴴ =
    ReflectionAbout (seedProjector (ApplyGate L (Ket seed))) at hReflection
  have hLoaded : ApplyGate L (Ket seed) = stencilBinInput rowScratch columnScratch residual
      width hWidth condition precision := stencil_bin_input_preparation_apply rowScratch columnScratch residual
        hValid hMass width hWidth condition precision
  rw [hLoaded] at hReflection
  exact hReflection.symm

/-- Load the residual tree and execute a word of the staged stencil oracles. -/
def stencilBinWordPreparation (rowScratch : Fin rows) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition : Fin n → ℝ) (precision : ℝ) :
    let W := BinStageWorkspace width condition precision (StencilWorkspace depth rows columns)
    (ℕ → Matrix W W ℂ) → Word W 1 → Matrix W W ℂ :=
  fun V word =>
    let place := stencilResidualAddress (depth := depth) rowScratch columnScratch width hWidth condition precision
    clockWordGate V word * embeddedTreePreparation place (place (ZeroStr depth)) residual

/-- The legally amplified target circuit is unitary from the same left-frame seed. -/
theorem stencil_bin_word_preparation_unitary
    (rowScratch : Fin rows) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition : Fin n → ℝ) (precision : ℝ)
    (V : ℕ → Matrix (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns))
      (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns)) ℂ)
    (word : Word (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns)) 1)
    (hValid : Valid residual) (hOracles : ∀ j < n + 1, V j ∈ Matrix.unitaryGroup _ ℂ) (hWord : legal (n + 1) word) :
    stencilBinWordPreparation rowScratch columnScratch residual width hWidth condition precision V word ∈
      Matrix.unitaryGroup _ ℂ :=
  (Matrix.unitaryGroup (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns)) ℂ).mul_mem
    (clock_word_gate_unitary V word hOracles hWord) (embedded_tree_preparation_unitary _ _ _ hValid)

/-- The prepared word output is exactly its run on the QRAM-loaded stencil input. -/
theorem stencil_bin_word_preparation_apply (rowScratch : Fin rows) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition : Fin n → ℝ) (precision : ℝ)
    (V : ℕ → Matrix (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns))
      (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns)) ℂ)
    (word : Word (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns)) 1)
    (hValid : Valid residual) (hMass : 0 < mass residual) :
    let seed := stencilResidualAddress rowScratch columnScratch width hWidth condition precision (ZeroStr depth)
    ApplyGate (stencilBinWordPreparation rowScratch columnScratch residual width hWidth condition precision V word)
        (Ket seed) =
      clockState V word (stencilBinInput rowScratch columnScratch residual width hWidth condition precision) := by
  intro seed
  unfold stencilBinWordPreparation
  rw [applyGate_mul, stencil_bin_input_preparation_apply rowScratch columnScratch residual hValid hMass,
    clock_word_gate_apply]

/-- A positive raw success event supplies a coherent amplified gate with constant success
probability, the original conditional state, and the existing weighted slot bound. -/
theorem encoded_stencil_bin_coherent_amplification (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (hValid : Valid residual) (hMass : 0 < mass residual)
    (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ) (prices : ℕ → ℕ)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columns)
    (hn : 0 < n) (hWidth : ∀ t, 0 < width t) :
    let C := stencilWalkFrame depth rowScratch columnScratch
    let U := stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch
    let P := binClockProjection (M := StencilWorkspace depth geometry.stencilSize columns) width condition precision
    let V := binStageOracle width condition threshold precision C U
    let bad := Projector (stencilBinFailure (depth := depth) rowScratch columnScratch width condition precision)
    let E := extendClock n P
    let initial := stencilBinInput rowScratch columnScratch residual width hWidth condition precision
    let a := plainAmplitude E bad V initial n
    let S := stencilBinSuccess (depth := depth) rowScratch columnScratch width condition precision
    let raw := stencilBinOutput geometry coefficients entryScale rowScratch columnScratch residual width hWidth
      condition threshold precision
    let seed := stencilResidualAddress rowScratch columnScratch width hWidth condition precision (ZeroStr depth)
    0 < MeasureProb raw S → ∃ K : ℝ, 0 < K ∧ ∃ rounds : ℕ → ℕ,
      let word := nestedWord E bad initial rounds n
      let A := stencilBinWordPreparation rowScratch columnScratch residual width hWidth condition precision V word
      let amplified := ApplyGate A (Ket seed)
      A ∈ Matrix.unitaryGroup _ ℂ ∧ 1 / 100 ≤ MeasureProb amplified S ∧
        PostMeasure amplified S = PostMeasure raw S ∧
        (weightedCost prices word : ℝ) ≤ K / a *
          (((prices 0 + prices 1 : ℕ) : ℝ) + quasinorm23 (fun j : Fin (n - 1) =>
            plainAmplitude E bad V initial (j.val + 1) * prices (j.val + 2))) := by
  intro C U P V bad E initial a S raw seed hRaw
  obtain ⟨K, hK, _, rounds, _, _, _, hLegal, _, hSuccess, hCost, hState⟩ :=
    encoded_stencil_bin_amplification geometry coefficients entryScale rowScratch columnScratch residual
      hValid hMass width condition threshold precision prices hScale hEntry hColumns hn hWidth hRaw
  let word := nestedWord E bad initial rounds n
  have hOutput := stencil_bin_word_preparation_apply rowScratch columnScratch residual width hWidth condition
    precision V word hValid hMass
  obtain ⟨hC, hU, hSq, _⟩ :=
    stencil_walk_encoding geometry coefficients entryScale rowScratch columnScratch hScale hEntry hColumns
  have hStage := (bin_stage_legal width condition threshold precision C U hC hU hSq hWidth).1
  have hOracles : ∀ j < n + 1, V j ∈ Matrix.unitaryGroup _ ℂ := fun j hj => hStage ⟨j, hj⟩
  refine ⟨K, hK, rounds, ?_, ?_, ?_, hCost⟩
  · exact stencil_bin_word_preparation_unitary rowScratch columnScratch residual width hWidth condition
      precision V word hValid hOracles hLegal
  · rw [hOutput]
    exact hSuccess
  · rw [hOutput]
    exact hState

end Qatlib.Papers.QFVMChen22.TimeStep
