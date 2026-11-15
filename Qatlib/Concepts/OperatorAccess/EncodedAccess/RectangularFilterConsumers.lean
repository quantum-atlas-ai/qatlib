/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.MatrixAccess.CircuitPipeline.RectangularFilteredComposition
public import Qatlib.Concepts.BlockEncoding.Postselection

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.BlockEncoding

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.MatrixAccess.CircuitPipeline

namespace Qatlib.Concepts.OperatorAccess.EncodedAccess

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator ComplexOrder Classical

set_option autoImplicit false
set_option linter.unusedSectionVars false

abbrev RectConsumerData := RectangularData (Fin 1) (Fin 2) (Fin 3)

noncomputable def rectPositiveDataOracle : Matrix RectConsumerData RectConsumerData ℂ :=
  permMatrix (Equiv.swap (Sum.inl (0 : Fin 1)) (Sum.inr (Sum.inl (0 : Fin 2))))

noncomputable def rectPositiveBGate : Matrix (Fin 1 × RectConsumerData) (Fin 1 × RectConsumerData) ℂ :=
  TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ)
    (permMatrix (Equiv.swap (Sum.inr (Sum.inl (0 : Fin 2))) (Sum.inr (Sum.inr (0 : Fin 3)))))

def rectPositiveA : Matrix (Fin 2) (Fin 1) ℂ := Matrix.of fun m _ => if m = 0 then (1 : ℂ) else 0

def rectPositiveB : Matrix (Fin 3) (Fin 2) ℂ :=
  Matrix.of fun o m => if o = 0 ∧ m = 0 then (1 : ℂ) else 0

noncomputable def rectLeakDataOracle : Matrix RectConsumerData RectConsumerData ℂ :=
  permMatrix (Equiv.swap (Sum.inl (0 : Fin 1)) (Sum.inr (Sum.inr (0 : Fin 3))))

noncomputable def rectLeakBGate : Matrix (Fin 1 × RectConsumerData) (Fin 1 × RectConsumerData) ℂ :=
  TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ)
    (permMatrix (Equiv.swap (Sum.inr (Sum.inr (0 : Fin 3))) (Sum.inr (Sum.inr (1 : Fin 3)))))

/-- The positive oracle swap sends the input tag to the first middle tag. -/
private theorem posOracle_inl (i : Fin 1) :
    ((Equiv.swap (Sum.inl (0 : Fin 1)) (Sum.inr (Sum.inl (0 : Fin 2))) : RectConsumerData → RectConsumerData) (Sum.inl i)) = Sum.inr (Sum.inl 0) := by
  rw [show i = 0 from Subsingleton.elim i 0]
  simp [Equiv.swap_apply_left]

/-- On middle tags, the positive oracle swap sends the first tag to the input and fixes the
other tags. -/
private theorem posOracle_inr_inl (m : Fin 2) :
    ((Equiv.swap (Sum.inl (0 : Fin 1)) (Sum.inr (Sum.inl (0 : Fin 2))) : RectConsumerData → RectConsumerData) (Sum.inr (Sum.inl m)))
      = if m = 0 then Sum.inl (0 : Fin 1) else Sum.inr (Sum.inl m) := by
  fin_cases m
  · simp [Equiv.swap_apply_right]
  · simp [Equiv.swap_apply_of_ne_of_ne]

/-- The positive oracle swap fixes every output tag. -/
private theorem posOracle_inr_inr (o : Fin 3) :
    ((Equiv.swap (Sum.inl (0 : Fin 1)) (Sum.inr (Sum.inl (0 : Fin 2))) : RectConsumerData → RectConsumerData) (Sum.inr (Sum.inr o))) = Sum.inr (Sum.inr o) := by
  simp [Equiv.swap_apply_of_ne_of_ne]

/-- The positive B-gate swap sends the first middle tag to the first output tag and fixes the
others. -/
private theorem posBGate_inr_inl (m : Fin 2) :
    ((Equiv.swap (Sum.inr (Sum.inl (0 : Fin 2))) (Sum.inr (Sum.inr (0 : Fin 3))) : RectConsumerData → RectConsumerData) (Sum.inr (Sum.inl m)))
      = if m = 0 then Sum.inr (Sum.inr (0 : Fin 3)) else Sum.inr (Sum.inl m) := by
  fin_cases m
  · simp [Equiv.swap_apply_left]
  · simp [Equiv.swap_apply_of_ne_of_ne]

/-- The positive B-gate swap sends the first output tag to the first middle tag and fixes the
others. -/
private theorem posBGate_inr_inr (o : Fin 3) :
    ((Equiv.swap (Sum.inr (Sum.inl (0 : Fin 2))) (Sum.inr (Sum.inr (0 : Fin 3))) : RectConsumerData → RectConsumerData) (Sum.inr (Sum.inr o)))
      = if o = 0 then Sum.inr (Sum.inl (0 : Fin 2)) else Sum.inr (Sum.inr o) := by
  fin_cases o <;> simp [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]

/-- The leakage oracle swap sends the input tag to the first output tag. -/
private theorem leakOracle_inl (i : Fin 1) :
    ((Equiv.swap (Sum.inl (0 : Fin 1)) (Sum.inr (Sum.inr (0 : Fin 3))) : RectConsumerData → RectConsumerData) (Sum.inl i)) = Sum.inr (Sum.inr 0) := by
  rw [show i = 0 from Subsingleton.elim i 0]
  simp [Equiv.swap_apply_left]

/-- The leakage oracle swap fixes every middle tag. -/
private theorem leakOracle_inr_inl (m : Fin 2) :
    ((Equiv.swap (Sum.inl (0 : Fin 1)) (Sum.inr (Sum.inr (0 : Fin 3))) : RectConsumerData → RectConsumerData) (Sum.inr (Sum.inl m))) = Sum.inr (Sum.inl m) := by
  simp [Equiv.swap_apply_of_ne_of_ne]

/-- The leakage oracle swap sends the first output tag to the input tag and fixes the other
output tags. -/
private theorem leakOracle_inr_inr (o : Fin 3) :
    ((Equiv.swap (Sum.inl (0 : Fin 1)) (Sum.inr (Sum.inr (0 : Fin 3))) : RectConsumerData → RectConsumerData) (Sum.inr (Sum.inr o)))
      = if o = 0 then Sum.inl (0 : Fin 1) else Sum.inr (Sum.inr o) := by
  fin_cases o <;> simp [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne, Fin.isValue]

/-- The leakage B-gate swap fixes every middle tag. -/
private theorem leakBGate_inr_inl (m : Fin 2) :
    ((Equiv.swap (Sum.inr (Sum.inr (0 : Fin 3))) (Sum.inr (Sum.inr (1 : Fin 3))) : RectConsumerData → RectConsumerData) (Sum.inr (Sum.inl m)))
      = Sum.inr (Sum.inl m) := by
  simp [Equiv.swap_apply_of_ne_of_ne]

/-- The leakage B-gate swap exchanges the first two output tags and fixes the remaining tag. -/
private theorem leakBGate_inr_inr (o : Fin 3) :
    ((Equiv.swap (Sum.inr (Sum.inr (0 : Fin 3))) (Sum.inr (Sum.inr (1 : Fin 3))) : RectConsumerData → RectConsumerData) (Sum.inr (Sum.inr o)))
      = if o = 0 then Sum.inr (Sum.inr (1 : Fin 3)) else if o = 1 then Sum.inr (Sum.inr (0 : Fin 3))
        else Sum.inr (Sum.inr o) := by
  fin_cases o <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne]

/-- The positive oracle input-to-middle entry is one precisely at the first middle tag. -/
private theorem posOracle_corner (m : Fin 2) (i : Fin 1) :
    rectPositiveDataOracle (Sum.inr (Sum.inl m)) (Sum.inl i)
      = if m = 0 then (1 : ℂ) else 0 := by
  simp only [rectPositiveDataOracle, permMatrix, Matrix.of_apply, posOracle_inl]
  by_cases hm : m = 0 <;> simp [hm]

/-- The positive B-gate middle-to-output entry is one precisely when both tags are first. -/
private theorem posBGate_corner (o : Fin 3) (m : Fin 2) :
    rectPositiveBGate (0, Sum.inr (Sum.inr o)) (0, Sum.inr (Sum.inl m))
      = if o = 0 ∧ m = 0 then (1 : ℂ) else 0 := by
  simp only [rectPositiveBGate, TensorGate, Matrix.kronecker_apply, Matrix.one_apply,
    permMatrix, Matrix.of_apply, posBGate_inr_inl, Fin.isValue]
  by_cases hm : m = 0 <;> by_cases ho : o = 0 <;> simp [hm, ho]

/-- Every input-to-middle entry of the leakage oracle is zero. -/
private theorem leakOracle_middle (m : Fin 2) (i : Fin 1) :
    rectLeakDataOracle (Sum.inr (Sum.inl m)) (Sum.inl i) = 0 := by
  simp [rectLeakDataOracle, permMatrix, Matrix.of_apply, leakOracle_inl]

/-- Every middle-to-output entry of the leakage B-gate is zero. -/
private theorem leakBGate_corner (o : Fin 3) (m : Fin 2) :
    rectLeakBGate (0, Sum.inr (Sum.inr o)) (0, Sum.inr (Sum.inl m)) = 0 := by
  simp only [rectLeakBGate, TensorGate, Matrix.kronecker_apply, Matrix.one_apply,
    permMatrix, Matrix.of_apply, leakBGate_inr_inl]
  have hne : ¬((Sum.inr (Sum.inr o) : RectConsumerData) = Sum.inr (Sum.inl m)) := by
    intro h
    have h1 := Sum.inr_injective h
    exact absurd h1 (by simp)
  simp only [ite_eq_right hne]
  norm_num

set_option maxHeartbeats 1000000 in

/-- The concrete rectangular filtered circuit exactly encodes the positive product, succeeds
with probability one, and uses one query and two gates. -/
theorem rectangularFiltered_positive_one_two_three_consumer :
    let C_A : List (AdjointStep (Fin 1 × RectConsumerData)) := [.forward]
    let C_B : List (AdjointStep (Fin 1 × RectConsumerData)) := [.gate rectPositiveBGate]
    let W := evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
      (TensorGate (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) rectPositiveDataOracle))
      (rectProductCircuit C_A C_B)
    let R := rectInputFrame (I := Fin 1) (M := Fin 2) (O := Fin 3) (0 : Fin 1) (0 : Fin 1)
    let L := rectOutputFrame (I := Fin 1) (M := Fin 2) (O := Fin 3) (0 : Fin 1) (0 : Fin 1)
    rectPositiveDataOracle ∈ Matrix.unitaryGroup RectConsumerData ℂ ∧
    WellFormedAdjointCircuit C_A ∧ WellFormedAdjointCircuit C_B ∧
    Qatlib.Concepts.BlockEncoding.BlockEncoding rectPositiveA (evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ)
        rectPositiveDataOracle) C_A)
      (encodingFiber (0 : Fin 1) * rectMiddleTagFrame) (encodingFiber (0 : Fin 1)
        * rectInputTagFrame) 1 0 ∧
    Qatlib.Concepts.BlockEncoding.BlockEncoding rectPositiveB (evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ)
        rectPositiveDataOracle) C_B)
      (encodingFiber (0 : Fin 1) * rectOutputTagFrame) (encodingFiber (0 : Fin 1)
        * rectMiddleTagFrame) 1 0 ∧
    Qatlib.Concepts.Execution.WorkspaceCP.compress L W R = rectPositiveB * rectPositiveA ∧
    Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionProbability W L R (Ket (0 : Fin 1)) = 1 ∧
    Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionOutput W L R (Ket (0 : Fin 1)) = some (Ket (0 : Fin 3)) ∧
    adjointQueryCount (rectProductCircuit C_A C_B) = 1 ∧
    adjointGateCount (rectProductCircuit C_A C_B) = 2 := by
  intro C_A C_B W R L
  have hswap1 : Function.Involutive
      (Equiv.swap (Sum.inl (0 : Fin 1)) (Sum.inr (Sum.inl (0 : Fin 2))) : RectConsumerData → RectConsumerData) :=
    fun x => Equiv.swap_apply_self _ _ x
  have hswap2 : Function.Involutive
      (Equiv.swap (Sum.inr (Sum.inl (0 : Fin 2))) (Sum.inr (Sum.inr (0 : Fin 3))) : RectConsumerData → RectConsumerData) :=
    fun x => Equiv.swap_apply_self _ _ x
  have hG1 := rectangularTagFilter_frames_and_projector (I := Fin 1) (M := Fin 2) (O := Fin 3)
    (0 : Fin 1) (0 : Fin 1)
  have hmid := hG1.2.1
  have hin := hG1.1
  have hout := hG1.2.2.1
  have hRiso := hG1.2.2.2.1
  have hLiso := hG1.2.2.2.2.1
  have hU : rectPositiveDataOracle ∈ Matrix.unitaryGroup RectConsumerData ℂ :=
    permMatrix_unitary hswap1
  have hBG : rectPositiveBGate ∈ Matrix.unitaryGroup (Fin 1 × RectConsumerData) ℂ :=
    tensorGate_unitary (Matrix.unitaryGroup (Fin 1) ℂ).one_mem (permMatrix_unitary hswap2)
  have hWfA : WellFormedAdjointCircuit C_A := by
    show WellFormedAdjointCircuit [.forward]
    simp
  have hWfB : WellFormedAdjointCircuit C_B := by
    show WellFormedAdjointCircuit [.gate rectPositiveBGate]
    simp only [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    exact hBG
  have hAexpr : (evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectPositiveDataOracle) C_A)
      = TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectPositiveDataOracle := by
    show instructionMatrix _ AdjointStep.forward *
        (1 : Matrix (Fin 1 × RectConsumerData) (Fin 1 × RectConsumerData) ℂ) = _
    rw [Matrix.mul_one]
    rfl
  have hBexpr : (evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectPositiveDataOracle) C_B)
      = rectPositiveBGate := by
    show instructionMatrix _ (AdjointStep.gate rectPositiveBGate) *
        (1 : Matrix (Fin 1 × RectConsumerData) (Fin 1 × RectConsumerData) ℂ) = _
    rw [Matrix.mul_one]
    rfl
  have hcA : Qatlib.Concepts.Execution.WorkspaceCP.compress (encodingFiber (0 : Fin 1) * rectMiddleTagFrame)
      (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectPositiveDataOracle)
      (encodingFiber (0 : Fin 1) * rectInputTagFrame) = rectPositiveA := by
    ext m i
    rw [rectLeftCorner_entry (I := Fin 1) (M := Fin 2) (O := Fin 3) (0 : Fin 1)
      (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectPositiveDataOracle) m i]
    simp only [TensorGate, Matrix.kronecker_apply, Matrix.one_apply, posOracle_corner,
      rectPositiveA, Matrix.of_apply]
    simp
  have hcB : Qatlib.Concepts.Execution.WorkspaceCP.compress (encodingFiber (0 : Fin 1) * rectOutputTagFrame)
      rectPositiveBGate (encodingFiber (0 : Fin 1) * rectMiddleTagFrame) = rectPositiveB := by
    ext o m
    rw [rectRightCorner_entry (I := Fin 1) (M := Fin 2) (O := Fin 3) (0 : Fin 1) rectPositiveBGate
      o m, posBGate_corner]
    rfl
  have hBEA : Qatlib.Concepts.BlockEncoding.BlockEncoding rectPositiveA
      (evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectPositiveDataOracle) C_A)
      (encodingFiber (0 : Fin 1) * rectMiddleTagFrame)
      (encodingFiber (0 : Fin 1) * rectInputTagFrame) 1 0 := by
    rw [hAexpr]
    refine ⟨tensorGate_unitary (Matrix.unitaryGroup (Fin 1) ℂ).one_mem hU,
      IsIsometry.mul (encodingFiber_isIsometry (I := RectConsumerData) (0 : Fin 1)) hmid,
      IsIsometry.mul (encodingFiber_isIsometry (I := RectConsumerData) (0 : Fin 1)) hin,
      by norm_num, by norm_num, by rw [hcA, one_smul ℝ, sub_self, norm_zero]⟩
  have hBEB : Qatlib.Concepts.BlockEncoding.BlockEncoding rectPositiveB
      (evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectPositiveDataOracle) C_B)
      (encodingFiber (0 : Fin 1) * rectOutputTagFrame)
      (encodingFiber (0 : Fin 1) * rectMiddleTagFrame) 1 0 := by
    rw [hBexpr]
    refine ⟨hBG,
      IsIsometry.mul (encodingFiber_isIsometry (I := RectConsumerData) (0 : Fin 1)) hout,
      IsIsometry.mul (encodingFiber_isIsometry (I := RectConsumerData) (0 : Fin 1)) hmid,
      by norm_num, by norm_num, by rw [hcB, one_smul ℝ, sub_self, norm_zero]⟩
  have hprogram := rectangularFilteredCircuit_same_oracle_semantics_and_cost
    rectPositiveDataOracle C_A C_B
  have hproduct := rectangularTagFilter_approximate_block_product
    (0 : Fin 1) (0 : Fin 1) rectPositiveA rectPositiveB _ _ 1 1 0 0 hBEA hBEB
  have hWBE : Qatlib.Concepts.BlockEncoding.BlockEncoding (rectPositiveB * rectPositiveA) W L R 1 0 := by
    simpa only [← hprogram.2.1, one_mul, mul_zero, add_zero] using! hproduct
  have hcomp : Qatlib.Concepts.Execution.WorkspaceCP.compress L W R = rectPositiveB * rectPositiveA := by
    have he := hWBE.error_le
    rw [one_smul] at he
    exact (sub_eq_zero.mp (norm_le_zero_iff.mp he)).symm
  have htarget : (rectPositiveB * rectPositiveA) *ᵥ Ket (0 : Fin 1) = Ket (0 : Fin 3) := by
    funext o
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, rectPositiveB,
      rectPositiveA, Ket, Matrix.of_apply, Fin.sum_univ_two, Fin.sum_univ_one]
    fin_cases o <;> simp
  have hbranch : Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionVector W L R (Ket (0 : Fin 1)) = Ket (0 : Fin 3) := by
    have he := (rectangularFilteredCircuit_actual_branch_and_born
      (0 : Fin 1) (0 : Fin 1) rectPositiveDataOracle C_A C_B (Ket (0 : Fin 1))).2.1
    rw [hAexpr, hBexpr, hcB, hcA, htarget] at he
    exact he
  have htargetBranch :
      Qatlib.Concepts.Execution.WorkspaceCP.compress L W R *ᵥ Ket (0 : Fin 1) = Ket
      (0 : Fin 3) := hbranch
  have hr : ‖Qatlib.Concepts.BlockEncoding.Postselection.stateVector ((rectPositiveB * rectPositiveA) *ᵥ
      Ket (0 : Fin 1))‖ = 1 := by
    rw [← hcomp, htargetBranch]
    exact (Qatlib.Concepts.BlockEncoding.Postselection.normalized_iff_stateVector_norm _).mp
        (normalized_ket _)
  have hprob : Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionProbability W L R (Ket (0 : Fin 1)) = 1 := by
    have he := (rectangularFilteredCircuit_probability_error_and_lower
      (0 : Fin 1) (0 : Fin 1) rectPositiveDataOracle C_A C_B
      rectPositiveA rectPositiveB 1 1 0 0 (Ket (0 : Fin 1)) hBEA hBEB (normalized_ket _)).1
    have hb : |Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionProbability W L R (Ket (0 : Fin 1)) - 1| ≤ 0 := by
      simpa only [hr, one_mul, one_pow, mul_zero, zero_mul, add_zero, zero_add] using! he
    have hz := abs_nonpos_iff.mp hb
    linarith
  have hout : Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionOutput W L R (Ket (0 : Fin 1)) = some (Ket (0 : Fin 3)) := by
    have hgap : (1 : ℝ) * 0 + 1 * 0 + 0 * 0 <
        ‖Qatlib.Concepts.BlockEncoding.Postselection.stateVector ((rectPositiveB * rectPositiveA) *ᵥ Ket (0 : Fin 1))‖ := by
      rw [hr]
      norm_num
    obtain ⟨_, φ, hφ, hnorm, _⟩ := rectangularFilteredCircuit_gap_actual_normalized_output
      (0 : Fin 1) (0 : Fin 1) rectPositiveDataOracle C_A C_B
      rectPositiveA rectPositiveB 1 1 0 0 (Ket (0 : Fin 1)) hBEA hBEB (normalized_ket _) hgap
    have hnormalize : NormedSpace.normalize (Qatlib.Concepts.BlockEncoding.Postselection.stateVector (Ket (0 : Fin 3))) =
        Qatlib.Concepts.BlockEncoding.Postselection.stateVector (Ket (0 : Fin 3)) :=
      NormedSpace.normalize_eq_self_of_norm_eq_one
        ((Qatlib.Concepts.BlockEncoding.Postselection.normalized_iff_stateVector_norm _).mp (normalized_ket _))
    have hd : ‖Qatlib.Concepts.BlockEncoding.Postselection.stateVector φ - Qatlib.Concepts.BlockEncoding.Postselection.stateVector (Ket (0 : Fin 3))‖ ≤ 0 := by
      simpa only [htarget, hnormalize, mul_zero, zero_mul, add_zero, zero_add, zero_div]
        using! hnorm.2.2
    have he := sub_eq_zero.mp (norm_le_zero_iff.mp hd)
    have hφket : φ = Ket (0 : Fin 3) := by
      funext o
      exact congrArg (fun v : EuclideanSpace ℂ (Fin 3) => v o) he
    exact hφ.trans (congrArg some hφket)
  refine ⟨hU, hWfA, hWfB, hBEA, hBEB, hcomp, hprob, hout, ?_, ?_⟩
  · show adjointQueryCount (rectProductCircuit C_A C_B) = 1
    have := (rectangularFilteredCircuit_same_oracle_semantics_and_cost
      rectPositiveDataOracle C_A C_B).2.2.1
    simpa [C_A, C_B, rectProductCircuit, rectLiftLeftCircuit, rectLiftRightCircuit,
      rectLiftStepLeft, rectLiftStepRight] using! this
  · have := (rectangularFilteredCircuit_same_oracle_semantics_and_cost
      rectPositiveDataOracle C_A C_B).2.2.2.1
    show adjointGateCount (rectProductCircuit C_A C_B) = 2
    simpa [C_A, C_B, rectProductCircuit, rectLiftLeftCircuit, rectLiftRightCircuit,
      rectLiftStepLeft, rectLiftStepRight] using! this

set_option maxHeartbeats 1000000 in

/-- The leakage example has a nonzero unfiltered corner but zero filtered compression and
success probability, with one query and two gates. -/
theorem rectangularFiltered_leakage_counterexample_consumer :
    let C_A : List (AdjointStep (Fin 1 × RectConsumerData)) := [.forward]
    let C_B : List (AdjointStep (Fin 1 × RectConsumerData)) := [.gate rectLeakBGate]
    let U := evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectLeakDataOracle) C_A
    let V := evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectLeakDataOracle) C_B
    let W := rectFilteredProduct U V
    let R := rectInputFrame (I := Fin 1) (M := Fin 2) (O := Fin 3) (0 : Fin 1) (0 : Fin 1)
    let L := rectOutputFrame (I := Fin 1) (M := Fin 2) (O := Fin 3) (0 : Fin 1) (0 : Fin 1)
    rectLeakDataOracle ∈ Matrix.unitaryGroup RectConsumerData ℂ ∧
    WellFormedAdjointCircuit C_A ∧ WellFormedAdjointCircuit C_B ∧
    Qatlib.Concepts.Execution.WorkspaceCP.compress (encodingFiber (0 : Fin 1) * rectMiddleTagFrame) U
        (encodingFiber (0 : Fin 1) * rectInputTagFrame) = 0 ∧
    Qatlib.Concepts.Execution.WorkspaceCP.compress L
        (TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftRight V * independentLiftLeft U)) R =
      (fun o (_ : Fin 1) => if o = (1 : Fin 3) then (1 : ℂ) else 0) ∧
    Qatlib.Concepts.Execution.WorkspaceCP.compress L W R = 0 ∧
    Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionProbability W L R (Ket (0 : Fin 1)) = 0 ∧
    Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionOutput W L R (Ket (0 : Fin 1)) = none ∧
    adjointQueryCount (rectProductCircuit C_A C_B) = 1 ∧
    adjointGateCount (rectProductCircuit C_A C_B) = 2 := by
  intro C_A C_B U V W R L
  have hswapL : Function.Involutive
      (Equiv.swap (Sum.inl (0 : Fin 1)) (Sum.inr (Sum.inr (0 : Fin 3))) : RectConsumerData → RectConsumerData) :=
    fun x => Equiv.swap_apply_self _ _ x
  have hswapO : Function.Involutive
      (Equiv.swap (Sum.inr (Sum.inr (0 : Fin 3))) (Sum.inr (Sum.inr (1 : Fin 3))) : RectConsumerData → RectConsumerData) :=
    fun x => Equiv.swap_apply_self _ _ x
  have hG1 := rectangularTagFilter_frames_and_projector (I := Fin 1) (M := Fin 2) (O := Fin 3)
    (0 : Fin 1) (0 : Fin 1)
  have hLiso := hG1.2.2.2.2.1
  have hU : rectLeakDataOracle ∈ Matrix.unitaryGroup RectConsumerData ℂ :=
    permMatrix_unitary hswapL
  have hBG : rectLeakBGate ∈ Matrix.unitaryGroup (Fin 1 × RectConsumerData) ℂ :=
    tensorGate_unitary (Matrix.unitaryGroup (Fin 1) ℂ).one_mem (permMatrix_unitary hswapO)
  have hWfA : WellFormedAdjointCircuit C_A := by
    show WellFormedAdjointCircuit [.forward]
    simp
  have hWfB : WellFormedAdjointCircuit C_B := by
    show WellFormedAdjointCircuit [.gate rectLeakBGate]
    simp only [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    exact hBG
  have hUexpr : (evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectLeakDataOracle) C_A)
      = TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectLeakDataOracle := by
    show instructionMatrix _ AdjointStep.forward *
        (1 : Matrix (Fin 1 × RectConsumerData) (Fin 1 × RectConsumerData) ℂ) = _
    rw [Matrix.mul_one]
    rfl
  have hVexpr : (evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectLeakDataOracle) C_B)
      = rectLeakBGate := by
    show instructionMatrix _ (AdjointStep.gate rectLeakBGate) *
        (1 : Matrix (Fin 1 × RectConsumerData) (Fin 1 × RectConsumerData) ℂ) = _
    rw [Matrix.mul_one]
    rfl
  have hmid0 : Qatlib.Concepts.Execution.WorkspaceCP.compress (encodingFiber (0 : Fin 1) * rectMiddleTagFrame)
      (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectLeakDataOracle)
      (encodingFiber (0 : Fin 1) * rectInputTagFrame) = 0 := by
    ext m i
    rw [rectLeftCorner_entry (I := Fin 1) (M := Fin 2) (O := Fin 3) (0 : Fin 1)
      (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectLeakDataOracle) m i]
    simp only [TensorGate, Matrix.kronecker_apply, Matrix.one_apply, leakOracle_middle]
    rw [show ((0 : Matrix (Fin 2) (Fin 1) ℂ) m i) = (0 : ℂ) from rfl, mul_zero]
  have hBc0 : Qatlib.Concepts.Execution.WorkspaceCP.compress (encodingFiber (0 : Fin 1) * rectOutputTagFrame)
      rectLeakBGate (encodingFiber (0 : Fin 1) * rectMiddleTagFrame) = 0 := by
    ext o m
    rw [rectRightCorner_entry (I := Fin 1) (M := Fin 2) (O := Fin 3) (0 : Fin 1) rectLeakBGate
      o m, leakBGate_corner]
    simp
  have hcomp0 : Qatlib.Concepts.Execution.WorkspaceCP.compress L W R = 0 := by
    show Qatlib.Concepts.Execution.WorkspaceCP.compress L
      (rectFilteredProduct (evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ)
        rectLeakDataOracle) C_A) (evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ)
        rectLeakDataOracle) C_B)) R = 0
    rw [hUexpr, hVexpr,
      (rectangularTagFilter_exact_compressed_product (I := Fin 1) (M := Fin 2) (O := Fin 3)
        (0 : Fin 1) (0 : Fin 1)
        (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectLeakDataOracle) rectLeakBGate).1,
      hBc0, Matrix.zero_mul]
  have hbranch : Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionVector W L R (Ket (0 : Fin 1)) = 0 := by
    have hprogram := rectangularFilteredCircuit_same_oracle_semantics_and_cost
      rectLeakDataOracle C_A C_B
    have he := (rectangularFilteredCircuit_actual_branch_and_born
      (0 : Fin 1) (0 : Fin 1) rectLeakDataOracle C_A C_B (Ket (0 : Fin 1))).2.1
    rw [hprogram.2.1] at he
    change Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionVector W L R
        (Ket (0 : Fin 1)) = _ at he
    rw [hVexpr, hBc0, Matrix.zero_mul, Matrix.zero_mulVec] at he
    exact he
  refine ⟨hU, hWfA, hWfB, ?_, ?_, hcomp0, ?_, ?_, ?_, ?_⟩
  · show Qatlib.Concepts.Execution.WorkspaceCP.compress (encodingFiber (0 : Fin 1) * rectMiddleTagFrame)
      (evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectLeakDataOracle) C_A)
      (encodingFiber (0 : Fin 1) * rectInputTagFrame) = 0
    rw [hUexpr]
    exact hmid0
  · ext o i
    have hcorner := rectangularTagFilter_unfiltered_corner (I := Fin 1) (M := Fin 2)
      (O := Fin 3) (0 : Fin 1) (0 : Fin 1)
      (evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectLeakDataOracle) C_A)
      (evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectLeakDataOracle) C_B) o i
    show (Qatlib.Concepts.Execution.WorkspaceCP.compress L
        (TensorGate (1 : Matrix Bool Bool ℂ)
          (independentLiftRight (evaluate (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ)
            rectLeakDataOracle) C_B) * independentLiftLeft (evaluate
              (TensorGate (1 : Matrix (Fin 1) (Fin 1) ℂ) rectLeakDataOracle) C_A))) R) o i
      = if o = (1 : Fin 3) then (1 : ℂ) else 0
    rw [hcorner, hUexpr, hVexpr]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [rectLeakBGate, TensorGate, Matrix.kronecker_apply, Matrix.one_apply,
      rectLeakDataOracle, permMatrix, Matrix.of_apply, leakOracle_inl,
      leakBGate_inr_inr]
    fin_cases o <;> simp
  · show Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionProbability W L R (Ket (0 : Fin 1)) = 0
    rw [Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionProbability_eq_norm_sq hLiso, hbranch]
    simp [Qatlib.Concepts.BlockEncoding.Postselection.stateVector]
  · show Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionOutput W L R (Ket (0 : Fin 1)) = none
    rw [Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionOutput, hbranch]
    exact conditionalState_zero
  · show adjointQueryCount (rectProductCircuit C_A C_B) = 1
    have := (rectangularFilteredCircuit_same_oracle_semantics_and_cost
      rectLeakDataOracle C_A C_B).2.2.1
    simpa [C_A, C_B, rectProductCircuit, rectLiftLeftCircuit, rectLiftRightCircuit,
      rectLiftStepLeft, rectLiftStepRight] using! this
  · have := (rectangularFilteredCircuit_same_oracle_semantics_and_cost
      rectLeakDataOracle C_A C_B).2.2.2.1
    show adjointGateCount (rectProductCircuit C_A C_B) = 2
    simpa [C_A, C_B, rectProductCircuit, rectLiftLeftCircuit, rectLiftRightCircuit,
      rectLiftStepLeft, rectLiftStepRight] using! this

end Qatlib.Concepts.OperatorAccess.EncodedAccess
