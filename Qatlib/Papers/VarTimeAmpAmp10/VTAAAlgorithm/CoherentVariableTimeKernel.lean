/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVariableTimeDefs
import Qatlib.Concepts.QsvtCore.QsVtMain.CPPPhaseCompiler
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel

/-!
# A clean flag implementation of coherent stages

This module implements `coherentStage` using a Boolean flag, projector-controlled flag flips,
and `flagFalseControl`. The clean-state identities connect the matrix construction with the
variable-time stage semantics used for [Ambainis2012], while the unitarity results apply to the
full flag workspace.

## Main statements

* `paid_stage_clean_state`: execution with a clean flag realizes the coherent stage.
* `paid_stage_full_unitary`: unitarity of the full flag circuit.
* `paidFlagEquiv`: conversion to the two-label workspace convention.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QsvtCore.QsVtMain

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
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
open scoped Classical BigOperators
set_option warningAsError false
set_option linter.unusedSectionVars false

variable {H : Type} [Fintype H] [DecidableEq H]

/-- The block column with `B` in the false-flag block and `C` in the true-flag block. -/
def flagColumns (B C : Matrix H H ℂ) : Matrix (Bool × H) H ℂ :=
  fun i j => if i.1 then C i.2 j else B i.2 j

/-- A projector-controlled flag flip transforms block columns by the stated
complementary-projector combinations. -/
theorem cppNot_flagColumns (P B C : Matrix H H ℂ) :
    cppNot P * flagColumns B C =
      flagColumns ((1 - P) * B + P * C) (P * B + (1 - P) * C) := by
  ext ⟨b,h⟩ i
  cases b <;> simp [cppNot, flagColumns, Matrix.mul_apply, Fintype.sum_prod_type, _root_.add_comm]

/-- The controlled matrix applying `W` on the false-flag block and the identity on the true-flag
block. -/
def flagFalseControl (W : Matrix H H ℂ) : Matrix (Bool × H) (Bool × H) ℂ :=
  Qatlib.Concepts.BlockEncoding.LCU.select (fun b : Bool => if b then 1 else W)

/-- False-flag control preserves unitarity. -/
theorem flagFalseControl_unitary (W : Matrix H H ℂ) (hW : W ∈ unitaryGroup H ℂ) :
    flagFalseControl W ∈ unitaryGroup (Bool × H) ℂ := by
  apply Qatlib.Concepts.BlockEncoding.LCU.select_unitary
  intro b
  cases b
  · exact hW
  · exact Submonoid.one_mem _

/-- False-flag control multiplies the false block by `W` and leaves the true block unchanged. -/
theorem flagFalseControl_columns (W B C : Matrix H H ℂ) :
    flagFalseControl W * flagColumns B C = flagColumns (W * B) C := by
  ext ⟨b,h⟩ i
  cases b <;>
    simp [flagFalseControl, Qatlib.Concepts.BlockEncoding.LCU.select, flagColumns, Matrix.mul_apply,
      Fintype.sum_prod_type, Matrix.one_apply]

/-- Multiplying the clean-frame embedding by `V` gives the block column with entries `V` and
zero. -/
theorem cppCleanFrame_mul (V : Matrix H H ℂ) :
    cppCleanFrame (1 : Matrix H H ℂ) * V = flagColumns V 0 := by
  ext ⟨b,h⟩ i
  cases b <;> simp [cppCleanFrame, flagColumns, Matrix.mul_apply, Matrix.one_apply]

/-- For an orthogonal projector `P` commuting with `W`, the flag-flip, controlled-`W`, flag-flip
circuit implements `coherentStage P W` on the clean-frame embedding. -/
theorem paid_stage_clean_matrix (P W : Matrix H H ℂ) (hP : IsOrthogonalProjector P)
    (hcomm : W * P = P * W) :
    cppNot P * flagFalseControl W * cppNot P * cppCleanFrame (1 : Matrix H H ℂ) =
      cppCleanFrame (1 : Matrix H H ℂ) * coherentStage P W := by
  have hPP : P * P = P := hP.1
  have hPC : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  have hCP : (1 - P) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
  have hPWC : P * W * (1 - P) = 0 := by
    rw [← hcomm, Matrix.mul_assoc, hPC, Matrix.mul_zero]
  have hCWP : (1 - P) * W * P = 0 := by
    rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hCP, Matrix.zero_mul]
  have htop : (1 - P) * (W * (1 - P)) + P * P = coherentStage P W := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hCWP, sub_zero, hPP]
    exact _root_.add_comm _ _
  have hbottom : P * (W * (1 - P)) + (1 - P) * P = 0 := by
    rw [← Matrix.mul_assoc, hPWC, hCP, _root_.add_zero]
  have hfirst : cppNot P * cppCleanFrame (1 : Matrix H H ℂ) = flagColumns (1 - P) P := by
    change cppNot P * flagColumns 1 0 = _
    rw [cppNot_flagColumns]
    simp only [Matrix.mul_one, Matrix.mul_zero, _root_.add_zero]
  calc
    _ = cppNot P * (flagFalseControl W * (cppNot P * cppCleanFrame (1 : Matrix H H ℂ))) := by
      simp only [Matrix.mul_assoc]
    _ = cppNot P * (flagFalseControl W * flagColumns (1 - P) P) := by rw [hfirst]
    _ = cppNot P * flagColumns (W * (1 - P)) P := by rw [flagFalseControl_columns]
    _ = flagColumns ((1 - P) * (W * (1 - P)) + P * P)
        (P * (W * (1 - P)) + (1 - P) * P) := cppNot_flagColumns _ _ _
    _ = flagColumns (coherentStage P W) 0 := by rw [htop, hbottom]
    _ = _ := (cppCleanFrame_mul _).symm

/-- The state with payload `ψ` in the false-flag block and zero in the true-flag block. -/
def cleanFlag (ψ : QState H) : QState (Bool × H) := fun q => if q.1 then 0 else ψ q.2

/-- The clean-frame matrix maps `ψ` to its clean Boolean-flag embedding. -/
theorem cppCleanFrame_apply (ψ : QState H) :
    cppCleanFrame (1 : Matrix H H ℂ) *ᵥ ψ = cleanFlag ψ := by
  funext ⟨b,h⟩
  cases b <;> simp [cppCleanFrame, cleanFlag, Matrix.mulVec, dotProduct, Matrix.one_apply]

/-- For an orthogonal projector `P` commuting with `W`, the three-step flag circuit returns a
clean flag and applies `coherentStage P W` to the payload. -/
theorem paid_stage_clean_state (P W : Matrix H H ℂ) (hP : IsOrthogonalProjector P)
    (hcomm : W * P = P * W) (ψ : QState H) :
    ApplyGate (cppNot P) (ApplyGate (flagFalseControl W) (ApplyGate (cppNot P) (cleanFlag ψ))) =
      cleanFlag (ApplyGate (coherentStage P W) ψ) := by
  have h := congrArg (fun A : Matrix (Bool × H) H ℂ => A *ᵥ ψ)
    (paid_stage_clean_matrix P W hP hcomm)
  simpa only [← Matrix.mulVec_mulVec, cppCleanFrame_apply, ApplyGate] using! h

/-- The full three-step flag circuit is unitary whenever `P` is an orthogonal projector and `W`
is unitary. -/
theorem paid_stage_full_unitary (P W : Matrix H H ℂ) (hP : IsOrthogonalProjector P)
    (hW : W ∈ unitaryGroup H ℂ) :
    cppNot P * flagFalseControl W * cppNot P ∈ unitaryGroup (Bool × H) ℂ :=
  Submonoid.mul_mem _
    (Submonoid.mul_mem _ (cppNot_unitary hP) (flagFalseControl_unitary W hW))
    (cppNot_unitary hP)

/-- The equivalence converting `Bool × H` into `H × Fin 2` by swapping factors and identifying
the Boolean flag with `Fin 2`. -/
def paidFlagEquiv : (Bool × H) ≃ (H × Fin 2) :=
  (Equiv.prodComm Bool H).trans (Equiv.prodCongr (Equiv.refl H) boolEquivFin2)

/-- Relabeling the projector-controlled flag flip into `H × Fin 2` preserves its unitarity. -/
theorem source_cppNot_unitary (P : Matrix H H ℂ) (hP : IsOrthogonalProjector P) :
    relabelGate (paidFlagEquiv (H := H)) (cppNot P) ∈ unitaryGroup (H × Fin 2) ℂ :=
  (relabelGate_mem_unitaryGroup _ _).mpr (cppNot_unitary hP)

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
