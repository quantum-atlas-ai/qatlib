/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVariableTimeKernel
import Qatlib.Concepts.QlsReadoutSpec.ProgramModel.PaidWordSemanticsLows
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel

open Qatlib.Concepts.QsvtCore.QsVtMain

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.QlsReadoutSpec.ProgramModel
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open scoped Classical BigOperators
set_option warningAsError false
set_option linter.unusedSectionVars false

variable {H : Type} [Fintype H] [DecidableEq H]

theorem source_controlled_zero_relabel (U : Matrix H H ℂ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled U ({0} : Finset (Fin 2)) =
      relabelGate (paidFlagEquiv (H := H)) (flagFalseControl U) := by
  ext ⟨h,k⟩ ⟨h',l⟩
  fin_cases k <;> fin_cases l <;>
    simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled, paidFlagEquiv, relabelGate, Matrix.reindex_apply,
      flagFalseControl, Qatlib.Concepts.BlockEncoding.LCU.select, boolEquivFin2, Matrix.one_apply]

theorem flagFalseControl_mul (U V : Matrix H H ℂ) :
    flagFalseControl U * flagFalseControl V = flagFalseControl (U * V) := by
  ext ⟨b,h⟩ ⟨c,i⟩
  cases b <;> cases c <;>
    simp [flagFalseControl, Qatlib.Concepts.BlockEncoding.LCU.select, Matrix.mul_apply,
      Fintype.sum_prod_type, Matrix.one_apply]

theorem source_controlled_zero_mul (U V : Matrix H H ℂ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled U ({0} : Finset (Fin 2)) * Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled V {0} =
      Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled (U * V) {0} := by
  simp only [source_controlled_zero_relabel]
  rw [← Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul,
      flagFalseControl_mul]

theorem cleanFlag_relabel (ψ : QState H) :
    relabelState (paidFlagEquiv (H := H)) (cleanFlag ψ) = Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide) ψ := by
  funext ⟨h,k⟩
  fin_cases k <;>
    simp [paidFlagEquiv, relabelState, cleanFlag, Qatlib.Concepts.QlsReadoutSpec.Amplification.clean,
        boolEquivFin2]

def paidStageWord (P target : Matrix H H ℂ) (slot : ℕ) : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H 2 :=
  [Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.known (relabelGate (paidFlagEquiv (H := H)) (cppNot P)),
    Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.known (Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled (ReflectionAbout target) {0}),
    Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.call slot {0} false,
    Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.known (Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled (ReflectionAbout target) {0}),
    Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.known (relabelGate (paidFlagEquiv (H := H)) (cppNot P))]

theorem paidStage_matrix (oracles : ℕ → Matrix H H ℂ) (P target : Matrix H H ℂ) (slot : ℕ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix oracles (paidStageWord P target slot) =
      relabelGate (paidFlagEquiv (H := H))
        (cppNot P * flagFalseControl (ReflectionAbout target * oracles slot * ReflectionAbout target) *
          cppNot P) := by
  let N := relabelGate (paidFlagEquiv (H := H)) (cppNot P)
  let R := ReflectionAbout target
  calc
    _ = N * (Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled R ({0} : Finset (Fin 2)) *
        Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled (oracles slot) {0} * Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled R {0}) * N := by
      simp [paidStageWord, Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix, N, R,
          Matrix.mul_assoc]
    _ = N * Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled (R * oracles slot * R) {0} * N := by
      rw [source_controlled_zero_mul, source_controlled_zero_mul]
    _ = _ := by
      rw [source_controlled_zero_relabel]
      simp only [N, R, ← Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul]

theorem paidStage_clean (oracles : ℕ → Matrix H H ℂ) (P target : Matrix H H ℂ)
    (slot : ℕ) (hP : IsOrthogonalProjector P) (_hT : IsOrthogonalProjector target)
    (hcomm : (ReflectionAbout target * oracles slot * ReflectionAbout target) * P =
      P * (ReflectionAbout target * oracles slot * ReflectionAbout target)) (ψ : QState H) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix oracles (paidStageWord P target slot) *ᵥ Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide) ψ =
      Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide)
        (coherentStage P (ReflectionAbout target * oracles slot * ReflectionAbout target) *ᵥ ψ) := by
  change ApplyGate (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix oracles (paidStageWord P target slot))
    (Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide) ψ) = _
  rw [paidStage_matrix, ← cleanFlag_relabel, applyGate_relabelGate]
  rw [applyGate_mul, applyGate_mul, paid_stage_clean_state _ _ hP hcomm]
  exact cleanFlag_relabel _

theorem paidStage_calls (P target : Matrix H H ℂ) (slot : ℕ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (paidStageWord P target slot) slot = 1 ∧
      Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (paidStageWord P target slot) = 4 := by
  simp [paidStageWord, Qatlib.Concepts.QlsReadoutSpec.Amplification.calls,
      Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount]

theorem paidStage_other_calls (P target : Matrix H H ℂ) (slot k : ℕ) (hk : k ≠ slot) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (paidStageWord P target slot) k = 0 := by
  simp [paidStageWord, Qatlib.Concepts.QlsReadoutSpec.Amplification.calls, Ne.symm hk]

theorem paidStage_legal (P target : Matrix H H ℂ) (slot slots : ℕ)
    (hP : IsOrthogonalProjector P) (hT : IsOrthogonalProjector target) (hslot : slot < slots) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.legal slots (paidStageWord P target slot) := by
  have hN := source_cppNot_unitary P hP
  have hR := controlled_unitary (reflectionAbout_unitary hT) ({0} : Finset (Fin 2))
  intro s hs
  simp only [paidStageWord, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact hN
  · exact hR
  · exact hslot
  · exact hR
  · exact hN

theorem paidStage_adjoint_syntax (P target : Matrix H H ℂ) (slot : ℕ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint (paidStageWord P target slot) =
      [Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.known ((relabelGate (paidFlagEquiv (H := H)) (cppNot P))ᴴ),
        Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.known ((Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled (ReflectionAbout target) ({0} : Finset (Fin 2)))ᴴ),
        Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.call slot {0} true,
        Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.known ((Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled (ReflectionAbout target) ({0} : Finset (Fin 2)))ᴴ),
        Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.known ((relabelGate (paidFlagEquiv (H := H)) (cppNot P))ᴴ)] := by
  rfl

theorem paidStage_adjoint_inverse_calls (P target : Matrix H H ℂ) (slot : ℕ) :
    (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint (paidStageWord P target slot)).countP
      (fun s => match s with | .call _ _ adj => adj | .known _ => false) = 1 ∧
    Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint (paidStageWord P target slot)) slot = 1 := by
  constructor
  · rw [paidStage_adjoint_syntax]
    rfl
  · rw [calls_wordAdjoint]
    exact (paidStage_calls P target slot).1

theorem paidStage_wordAdjoint_matrix (oracles : ℕ → Matrix H H ℂ)
    (P target : Matrix H H ℂ) (slot : ℕ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix oracles (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint (paidStageWord P target slot)) =
      (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix oracles (paidStageWord P target slot))ᴴ :=
  wordMatrix_wordAdjoint oracles _

theorem paidStage_adjoint_undo (oracles : ℕ → Matrix H H ℂ)
    (P target : Matrix H H ℂ) (slot slots : ℕ)
    (hOracle : ∀ k < slots, oracles k ∈ unitaryGroup H ℂ)
    (hlegal : Qatlib.Concepts.QlsReadoutSpec.Amplification.legal slots (paidStageWord P target slot))
    (Φ : QState (Qatlib.Concepts.QlsReadoutSpec.Amplification.Space H 2)) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix oracles (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint (paidStageWord P target slot)) *ᵥ
      (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix oracles (paidStageWord P target slot) *ᵥ Φ) = Φ := by
  have hU := wordMatrix_unitary oracles (paidStageWord P target slot) hOracle hlegal
  have hu : (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix oracles (paidStageWord P target slot))ᴴ *
      Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix oracles (paidStageWord P target slot) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hU
  rw [wordMatrix_wordAdjoint, Matrix.mulVec_mulVec,
    hu, Matrix.one_mulVec]

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
