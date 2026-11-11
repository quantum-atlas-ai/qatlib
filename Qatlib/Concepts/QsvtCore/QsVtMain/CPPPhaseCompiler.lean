/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT
import Qatlib.Concepts.MatrixAccess.FrameFilterProd

/-!
# Compilation of controlled projector phases

This module defines `CPPStep`, its matrix interpretation, and `cppCompile` for indexed families
of real phases. A Boolean ancilla implements each projector phase through a flip–phase–flip
gadget, following the alternating-phase framework of [GilyenSuLowWiebe2019].

The clean embedding is preserved by compilation, and `cppCounts` records oracle calls, the two
projector flips, and phase gates separately.

## Main statements

* `cpp_not_clean_phase_gadget`: Implement a projector phase on a clean Boolean ancilla.
* `cppCompile_clean`: Identify the clean action of a compiled phase family.
* `cpp_family_actual_compilation_and_counts`: Combine unitarity, clean action, and exact
  instruction counts.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix Polynomial
open scoped Classical BigOperators Kronecker

/-- The matrix that flips a Boolean ancilla on the `P` component and acts identically on its
complement. -/
noncomputable def cppNot {H : Type} [DecidableEq H] (P : Matrix H H ℂ) :
    Matrix (Bool×H) (Bool×H) ℂ := fun i j => if i.1=j.1 then (1-P) i.2 j.2 else P i.2 j.2

/-- The frame obtained by adjoining a Boolean ancilla in the `false` state. -/
noncomputable def cppCleanFrame {H I : Type} (F : Matrix H I ℂ) :
    Matrix (Bool×H) I ℂ := fun i j => if i.1 then 0 else F i.2 j

/-- The diagonal Boolean phase gate with conjugate phases on `false` and `true`, tensored with
the data identity. -/
noncomputable def cppBitPhase {H : Type} [DecidableEq H] (φ : ℝ) :
    Matrix (Bool×H) (Bool×H) ℂ :=
  (Matrix.diagonal (fun b : Bool => if b then anglePhase φ else star (anglePhase φ))) ⊗ₖ
    (1 : Matrix H H ℂ)

/-- Instructions for two projector-controlled flips, forward and adjoint oracle calls, and
indexed real phases. -/
inductive CPPStep (J : Type) where
  | projectorP | projectorQ | forward | backward
  | phase : (J→ℝ) → CPPStep J

/-- Exchange the two projector instructions and exchange forward with backward oracle calls. -/
def cppSwap {J : Type} : CPPStep J→CPPStep J
  | .projectorP => .projectorQ | .projectorQ => .projectorP
  | .forward => .backward | .backward => .forward | .phase f => .phase f

/-- Exchange forward and backward oracle calls while preserving projector and phase
instructions. -/
def cppSwapData {J : Type} : CPPStep J→CPPStep J
  | .forward => .backward | .backward => .forward | s => s

/-- Compile an indexed phase list into alternating projector-controlled phase gadgets and oracle
calls. -/
def cppCompile {J : Type} : List (J→ℝ) → List (CPPStep J)
  | [] => []
  | f::fs => [.projectorQ,.phase f,.projectorQ,.forward]++(cppCompile fs).map cppSwap

/-- Count oracle calls, `P` flips, `Q` flips, and phase instructions, in that order. -/
def cppCounts {J : Type} : List (CPPStep J)→ℕ×ℕ×ℕ×ℕ
  | [] => (0,0,0,0)
  | s::ss => let c:=cppCounts ss; match s with
    | .forward | .backward => (c.1+1,c.2.1,c.2.2.1,c.2.2.2)
    | .projectorP => (c.1,c.2.1+1,c.2.2.1,c.2.2.2)
    | .projectorQ => (c.1,c.2.1,c.2.2.1+1,c.2.2.2)
    | .phase _ => (c.1,c.2.1,c.2.2.1,c.2.2.2+1)

/-- Interpret a compiler instruction as a matrix selected by the family index. -/
noncomputable def cppInstruction {J H : Type} [DecidableEq J] [DecidableEq H]
    (U P Q : Matrix H H ℂ) : CPPStep J→Matrix (J×(Bool×H)) (J×(Bool×H)) ℂ
  | .projectorP => select (fun _=>cppNot P)
  | .projectorQ => select (fun _=>cppNot Q)
  | .forward => select (fun _=>(1:Matrix Bool Bool ℂ)⊗ₖU)
  | .backward => select (fun _=>(1:Matrix Bool Bool ℂ)⊗ₖUᴴ)
  | .phase f => select (fun j=>cppBitPhase (H:=H) (f j))

/-- Evaluate an instruction list as the ordered product of its instruction matrices. -/
noncomputable def cppEvaluate {J H : Type} [Fintype J] [DecidableEq J]
    [Fintype H] [DecidableEq H] (U P Q : Matrix H H ℂ) :
    List (CPPStep J)→Matrix (J×(Bool×H)) (J×(Bool×H)) ℂ
  | [] => 1
  | s::ss => cppInstruction U P Q s*cppEvaluate U P Q ss

/-- The clean Boolean-ancilla embedding for an indexed family of data spaces. -/
noncomputable def cppFamilyClean {J H : Type} [DecidableEq J] [DecidableEq H] :
    Matrix (J×(Bool×H)) (J×H) ℂ :=
  fun i j => if i.1=j.1 then if i.2.1 then 0 else (1:Matrix H H ℂ) i.2.2 j.2 else 0

/-- Stack `B` and `C` in the `false` and `true` Boolean blocks of a rectangular matrix. -/
private def cppColumns {H I : Type} (B C : Matrix H I ℂ) : Matrix (Bool×H) I ℂ :=
  fun i j => if i.1 then C i.2 j else B i.2 j

/-- Multiplication by `cppNot P` mixes the two column blocks using `P` and `1 - P`. -/
private theorem cppNot_mul_columns {H I : Type} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) (B C : Matrix H I ℂ) :
    cppNot P * cppColumns B C =
      cppColumns ((1-P)*B+P*C) (P*B+(1-P)*C) := by
  ext ⟨b,h⟩ i
  cases b <;>
    simp [cppNot, cppColumns, Matrix.mul_apply, Fintype.sum_prod_type,
      add_comm]

/-- Multiplication by `cppBitPhase` scales the two column blocks by the conjugate and direct
phases. -/
private theorem cppBitPhase_mul_columns {H I : Type} [Fintype H] [DecidableEq H]
    (φ : ℝ) (B C : Matrix H I ℂ) :
    cppBitPhase (H:=H) φ * cppColumns B C =
      cppColumns (star (anglePhase φ) • B) (anglePhase φ • C) := by
  ext ⟨b,h⟩ i
  cases b <;>
    simp [cppBitPhase, cppColumns, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.diagonal_apply, Matrix.one_apply,
      ite_mul, mul_ite]

/-- Express `cppNot P` as the sum of identity and Pauli-X tensor terms on complementary data
components. -/
private theorem cppNot_tensor {H : Type} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) :
    cppNot P = TensorGate (1 : Matrix Bool Bool ℂ) (1-P) + TensorGate PauliX P := by
  ext ⟨b,h⟩ ⟨c,i⟩
  cases b <;> cases c <;> simp [cppNot, TensorGate, Matrix.one_apply, PauliX, permMatrix]

/-- For an orthogonal projector `P`, the projector-controlled Boolean flip is unitary. -/
theorem cppNot_unitary {H : Type} [Fintype H] [DecidableEq H]
    {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P) :
    cppNot P ∈ unitaryGroup (Bool×H) ℂ := by
  have hid : P*P=P := hP.1
  have hstar : Pᴴ=P := hP.2
  have hX2 : PauliX*PauliX=1 := permMatrix_mul_self Bool.not_not
  have hXH : PauliXᴴ=PauliX := permMatrix_conjTranspose Bool.not_not
  have h01 : P*(1-P)=0 := by rw [Matrix.mul_sub, Matrix.mul_one, hid, sub_self]
  have h10 : (1-P)*P=0 := by rw [Matrix.sub_mul, Matrix.one_mul, hid, sub_self]
  have h00 : (1-P)*(1-P)=1-P := by rw [Matrix.sub_mul, Matrix.one_mul, h01, sub_zero]
  have hself : (cppNot P)ᴴ = cppNot P := by
    rw [cppNot_tensor, Matrix.conjTranspose_add, tensorGate_conjTranspose,
      tensorGate_conjTranspose, Matrix.conjTranspose_one, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hstar, hXH]
  have hsq : cppNot P * cppNot P = 1 := by
    rw [cppNot_tensor]
    simp only [Matrix.add_mul, Matrix.mul_add, tensorGate_mul]
    rw [Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hX2,
      h00, h01, h10, hid]
    simp only [TensorGate, Matrix.kronecker_zero, add_zero, zero_add]
    rw [← Matrix.kronecker_add, sub_add_cancel, Matrix.one_kronecker_one]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hself, hsq]

/-- The flip–phase–flip gadget implements `phaseRotation` on the clean ancilla, and its
projector-controlled flip is unitary [GilyenSuLowWiebe2019]. -/
theorem cpp_not_clean_phase_gadget : ∀ (H : Type) [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) (φ : ℝ), IsOrthogonalProjector P →
  cppNot P ∈ unitaryGroup (Bool×H) ℂ ∧
  cppNot P * cppBitPhase (H:=H) φ * cppNot P * cppCleanFrame (1 : Matrix H H ℂ) =
    cppCleanFrame (1 : Matrix H H ℂ) * phaseRotation P (anglePhase φ) := by
  intro H _ _ P φ hP
  refine ⟨cppNot_unitary hP, ?_⟩
  have hid : P*P=P := hP.1
  have hstar : Pᴴ=P := hP.2
  have hX2 : PauliX*PauliX=1 := permMatrix_mul_self Bool.not_not
  have hXH : PauliXᴴ=PauliX := permMatrix_conjTranspose Bool.not_not
  have h01 : P*(1-P)=0 := by rw [Matrix.mul_sub, Matrix.mul_one, hid, sub_self]
  have h10 : (1-P)*P=0 := by rw [Matrix.sub_mul, Matrix.one_mul, hid, sub_self]
  have h00 : (1-P)*(1-P)=1-P := by rw [Matrix.sub_mul, Matrix.one_mul, h01, sub_zero]
  have hclean : cppCleanFrame (1 : Matrix H H ℂ) = cppColumns 1 0 := rfl
  rw [hclean, Matrix.mul_assoc, Matrix.mul_assoc, cppNot_mul_columns,
    Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.mul_one, Matrix.mul_zero, add_zero,
    cppBitPhase_mul_columns, cppNot_mul_columns]
  simp only [Matrix.mul_smul, h00, hid, h01, h10, smul_zero, add_zero]
  ext ⟨b,h⟩ i
  cases b <;> simp [cppColumns, Matrix.mul_apply,
    Matrix.one_apply, phaseRotation, add_comm, ite_mul]

/-- The Boolean phase gate is unitary for every real angle. -/
private theorem cppBitPhase_unitary {H : Type} [Fintype H] [DecidableEq H] (φ : ℝ) :
    cppBitPhase (H:=H) φ ∈ unitaryGroup (Bool×H) ℂ := by
  rw [cppBitPhase]
  apply tensorGate_unitary
  · have hz : anglePhase φ * star (anglePhase φ) = 1 := by
      simpa only [IsPhase, mul_comm] using anglePhase_isPhase φ
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext b c
    cases b <;> cases c <;>
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
        Fintype.sum_bool, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
        star_zero, star_star, zero_mul, mul_zero, zero_add, add_zero,
        Matrix.one_apply]
    all_goals simpa only [starRingEnd_apply, mul_comm] using hz
  · exact (unitaryGroup H ℂ).one_mem

/-- Every interpreted instruction is unitary when the oracle is unitary and both projectors are
orthogonal. -/
private theorem cppInstruction_unitary {J H : Type} [Fintype J] [DecidableEq J]
    [Fintype H] [DecidableEq H] {U P Q : Matrix H H ℂ}
    (hU : U ∈ unitaryGroup H ℂ) (hP : IsOrthogonalProjector P)
    (hQ : IsOrthogonalProjector Q) (s : CPPStep J) :
    cppInstruction U P Q s ∈ unitaryGroup (J×(Bool×H)) ℂ := by
  cases s with
  | projectorP => exact select_unitary _ (fun _ => cppNot_unitary hP)
  | projectorQ => exact select_unitary _ (fun _ => cppNot_unitary hQ)
  | forward => exact select_unitary _ (fun _ => tensorGate_unitary (unitaryGroup Bool ℂ).one_mem hU)
  | backward => exact select_unitary _ (fun _ => tensorGate_unitary (unitaryGroup Bool ℂ).one_mem (adjoint_unitary hU))
  | phase f => exact select_unitary _ (fun j => cppBitPhase_unitary (f j))

/-- Evaluation of any instruction list is unitary for a unitary oracle and orthogonal
projectors. -/
theorem cppEvaluate_unitary {J H : Type} [Fintype J] [DecidableEq J]
    [Fintype H] [DecidableEq H] {U P Q : Matrix H H ℂ}
    (hU : U ∈ unitaryGroup H ℂ) (hP : IsOrthogonalProjector P)
    (hQ : IsOrthogonalProjector Q) (ss : List (CPPStep J)) :
    cppEvaluate U P Q ss ∈ unitaryGroup (J×(Bool×H)) ℂ := by
  induction ss with
  | nil => exact (unitaryGroup _ ℂ).one_mem
  | cons s ss ih => exact (unitaryGroup _ ℂ).mul_mem (cppInstruction_unitary hU hP hQ s) ih

/-- Evaluation of a concatenated instruction list is the product of the two evaluations. -/
private theorem cppEvaluate_append {J H : Type} [Fintype J] [DecidableEq J]
    [Fintype H] [DecidableEq H] (U P Q : Matrix H H ℂ) (ss ts : List (CPPStep J)) :
    cppEvaluate U P Q (ss++ts) = cppEvaluate U P Q ss * cppEvaluate U P Q ts := by
  induction ss with
  | nil => simp [cppEvaluate]
  | cons s ss ih => simp [cppEvaluate, ih, Matrix.mul_assoc]

/-- Swapping projector and oracle directions in every instruction evaluates as adjointing the
oracle and exchanging the projectors. -/
private theorem cppEvaluate_swap {J H : Type} [Fintype J] [DecidableEq J]
    [Fintype H] [DecidableEq H] (U P Q : Matrix H H ℂ) (ss : List (CPPStep J)) :
    cppEvaluate U P Q (ss.map cppSwap) = cppEvaluate Uᴴ Q P ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => cases s <;> simp [cppEvaluate, cppInstruction, cppSwap, ih]

/-- Rectangular matrix multiplication with an explicit finite intermediate index. -/
private noncomputable abbrev cppMul {M N K : Type} [Fintype N]
    (A : Matrix M N ℂ) (B : Matrix N K ℂ) : Matrix M K ℂ :=
  @HMul.hMul (Matrix M N ℂ) (Matrix N K ℂ) (Matrix M K ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

/-- Associativity of the explicitly instantiated rectangular matrix product. -/
private theorem cppMul_assoc {M N K L : Type} [Fintype N] [Fintype K]
    (A : Matrix M N ℂ) (B : Matrix N K ℂ) (C : Matrix K L ℂ) :
    cppMul (cppMul A B) C = cppMul A (cppMul B C) := Matrix.mul_assoc A B C

/-- The product of two selected matrix families is the selected family of their products. -/
private theorem cppMul_select {J H : Type} [Fintype J] [DecidableEq J]
    [Fintype H] [DecidableEq H] (U V : J → Matrix H H ℂ) :
    cppMul (select U) (select V) = select (fun j => U j * V j) := parallel_select_mul U V

/-- The block diagonal rectangular matrix selected from an indexed family of rectangular
matrices. -/
private noncomputable def cppSelectRect {J H I : Type} [DecidableEq J]
    (F : J → Matrix H I ℂ) : Matrix (J×H) (J×I) ℂ :=
  fun i j => if i.1=j.1 then F i.1 i.2 j.2 else 0

/-- Left multiplication by a selected square family acts independently on each rectangular
block. -/
private theorem cpp_select_rect_mul {J H I : Type} [Fintype J] [DecidableEq J]
    [Fintype H] (U : J → Matrix H H ℂ) (F : J → Matrix H I ℂ) :
    cppMul (select U) (cppSelectRect F) = cppSelectRect (fun j => cppMul (U j) (F j)) := by
  ext ⟨j,h⟩ ⟨k,i⟩
  by_cases hj : j=k
  · subst k; simp [select,cppSelectRect,Matrix.mul_apply,Fintype.sum_prod_type,mul_ite,ite_mul]
  · simp [select,cppSelectRect,Matrix.mul_apply,Fintype.sum_prod_type,mul_ite,ite_mul,hj]

/-- Right multiplication by a selected square family acts independently on each rectangular
block. -/
private theorem cpp_rect_select_mul {J H I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] (F : J → Matrix H I ℂ) (U : J → Matrix I I ℂ) :
    cppMul (cppSelectRect F) (select U) = cppSelectRect (fun j => cppMul (F j) (U j)) := by
  ext ⟨j,h⟩ ⟨k,i⟩
  by_cases hj : j=k
  · subst k; simp [select,cppSelectRect,Matrix.mul_apply,Fintype.sum_prod_type,mul_ite,ite_mul]
  · simp [select,cppSelectRect,Matrix.mul_apply,Fintype.sum_prod_type,mul_ite,ite_mul,hj]

/-- A data gate tensored with the Boolean identity intertwines the clean embedding with the
original data gate. -/
private theorem cpp_data_clean {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) :
    ((1 : Matrix Bool Bool ℂ) ⊗ₖ U) * cppCleanFrame (1 : Matrix H H ℂ) =
      cppCleanFrame (1 : Matrix H H ℂ) * U := by
  ext ⟨b,h⟩ i
  cases b <;> simp [cppCleanFrame, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, ite_mul, mul_ite]

/-- The selected flip–phase–flip gadget implements the family of projector phase rotations on
the clean embedding. -/
private theorem cpp_family_gadget {J H : Type} [Fintype J] [DecidableEq J]
    [Fintype H] [DecidableEq H] {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    (f : J → ℝ) :
    cppMul (select (fun _ : J => cppNot P) * select (fun j => cppBitPhase (H:=H) (f j)) *
      select (fun _ : J => cppNot P)) cppFamilyClean =
      cppMul cppFamilyClean (select (fun j => phaseRotation P (anglePhase (f j)))) := by
  change cppMul _ (cppSelectRect (fun _ : J => cppCleanFrame (1 : Matrix H H ℂ))) =
    cppMul (cppSelectRect (fun _ : J => cppCleanFrame (1 : Matrix H H ℂ))) _
  rw [parallel_select_mul, parallel_select_mul, cpp_select_rect_mul, cpp_rect_select_mul]
  congr 1
  funext j
  exact (cpp_not_clean_phase_gadget H P (f j) hP).2

/-- Selected data gates intertwine the family clean embedding with the corresponding selected
data operators. -/
private theorem cpp_family_data {J H : Type} [Fintype J] [DecidableEq J]
    [Fintype H] [DecidableEq H] (U : Matrix H H ℂ) :
    cppMul (select (fun _ : J => (1 : Matrix Bool Bool ℂ) ⊗ₖ U)) cppFamilyClean =
      cppMul cppFamilyClean (select (fun _ : J => U)) := by
  change cppMul _ (cppSelectRect (fun _ : J => cppCleanFrame (1 : Matrix H H ℂ))) =
    cppMul (cppSelectRect (fun _ : J => cppCleanFrame (1 : Matrix H H ℂ))) _
  rw [cpp_select_rect_mul, cpp_rect_select_mul]
  congr 1; funext j; exact cpp_data_clean U

/-- The compiled phase family acts on the clean embedding as the selected family of alternating
phase words. -/
theorem cppCompile_clean {J H : Type} [Fintype J] [DecidableEq J]
    [Fintype H] [DecidableEq H] (U P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q) (fs : List (J→ℝ)) :
    (cppEvaluate U P Q (cppCompile fs) * cppFamilyClean : Matrix (J×(Bool×H)) (J×H) ℂ) =
      cppFamilyClean * select (fun j => phasedAlternating U P Q 1
        (fs.map (fun f => anglePhase (f j)))) := by
  change cppMul (cppEvaluate U P Q (cppCompile fs)) (cppFamilyClean (J:=J) (H:=H)) =
    cppMul (cppFamilyClean (J:=J) (H:=H)) (select (fun j => phasedAlternating U P Q 1 (fs.map (fun f => anglePhase (f j)))))
  induction fs generalizing U P Q with
  | nil => simp [cppCompile,cppEvaluate,phasedAlternating,parallel_select_one]
  | cons f fs ih =>
    rw [cppCompile,cppEvaluate_append,cppEvaluate_swap,cppMul_assoc,
      ih Uᴴ Q P hQ hP]
    simp only [cppEvaluate,cppInstruction,Matrix.mul_one]
    have hh : cppMul ((select (fun _ : J => cppNot Q)) *
        ((select (fun j => cppBitPhase (H:=H) (f j))) *
          ((select (fun _ : J => cppNot Q)) * (select (fun _ : J => (1 : Matrix Bool Bool ℂ) ⊗ₖ U)))))
        cppFamilyClean = cppMul cppFamilyClean
          (select (fun j => phaseRotation Q (anglePhase (f j)) * U)) := by
      calc
        _ = cppMul (select (fun _ : J => cppNot Q) * select (fun j => cppBitPhase (H:=H) (f j)) *
              select (fun _ : J => cppNot Q))
              (cppMul (select (fun _ : J => (1 : Matrix Bool Bool ℂ) ⊗ₖ U)) cppFamilyClean) := by
          simp only [cppMul,Matrix.mul_assoc]
        _ = _ := by
          rw [cpp_family_data, ← cppMul_assoc, cpp_family_gadget hQ, cppMul_assoc,cppMul_select]
    rw [← cppMul_assoc, hh, cppMul_assoc,cppMul_select]
    rfl

/-- Instruction counts add componentwise under list concatenation. -/
private theorem cppCounts_append {J : Type} (ss ts : List (CPPStep J)) :
    cppCounts (ss++ts) =
    ((cppCounts ss).1+(cppCounts ts).1,
      (cppCounts ss).2.1+(cppCounts ts).2.1,
      (cppCounts ss).2.2.1+(cppCounts ts).2.2.1,
      (cppCounts ss).2.2.2+(cppCounts ts).2.2.2) := by
  induction ss with
  | nil => simp [cppCounts]
  | cons s ss ih => cases s <;> simp [cppCounts,ih,Nat.add_comm,Nat.add_left_comm]

/-- Swapping projector and oracle directions exchanges the two projector counts and preserves
oracle and phase counts. -/
private theorem cppCounts_swap {J : Type} (ss : List (CPPStep J)) :
    cppCounts (ss.map cppSwap) =
      ((cppCounts ss).1,(cppCounts ss).2.2.1,(cppCounts ss).2.1,(cppCounts ss).2.2.2) := by
  induction ss with
  | nil => rfl
  | cons s ss ih => cases s <;> simp [cppCounts,cppSwap,ih]

/-- A compiled phase list of length `d` has counts `(d, 2 * (d / 2), 2 * ((d + 1) / 2), d)`. -/
theorem cppCompile_counts {J : Type} (fs : List (J→ℝ)) :
    cppCounts (cppCompile fs) =
      (fs.length,2*(fs.length/2),2*((fs.length+1)/2),fs.length) := by
  induction fs with
  | nil => simp [cppCompile,cppCounts]
  | cons f fs ih =>
    simp only [cppCompile,cppCounts_append,cppCounts_swap,ih,cppCounts,List.length_cons]
    apply Prod.ext
    · dsimp; omega
    · apply Prod.ext
      · dsimp; omega
      · apply Prod.ext <;> dsimp <;> omega

/-- Reversing only oracle directions in every instruction is equivalent to evaluating with the
adjoint oracle. -/
theorem cppEvaluate_swapData {J H : Type} [Fintype J] [DecidableEq J]
    [Fintype H] [DecidableEq H] (U P Q : Matrix H H ℂ) (ss : List (CPPStep J)) :
    cppEvaluate U P Q (ss.map cppSwapData) = cppEvaluate Uᴴ P Q ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => cases s <;> simp [cppEvaluate,cppInstruction,cppSwapData,ih]

/-- Compilation yields a unitary whose clean action is the indexed alternating phase word, with
exact oracle, projector, and phase counts [GilyenSuLowWiebe2019]. -/
theorem cpp_family_actual_compilation_and_counts : ∀ (J H : Type)
    [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
    (U P Q : Matrix H H ℂ) (fs : List (J→ℝ)),
  U ∈ unitaryGroup H ℂ → IsOrthogonalProjector P → IsOrthogonalProjector Q →
  cppEvaluate U P Q (cppCompile fs) ∈ unitaryGroup (J×(Bool×H)) ℂ ∧
  (cppEvaluate U P Q (cppCompile fs) * cppFamilyClean : Matrix (J×(Bool×H)) (J×H) ℂ) =
    cppFamilyClean * select (fun j => phasedAlternating U P Q 1
      (fs.map (fun f => anglePhase (f j)))) ∧
  cppCounts (cppCompile fs) = (fs.length,2*(fs.length/2),2*((fs.length+1)/2),fs.length) := by
  intro J H _ _ _ _ U P Q fs hU hP hQ
  exact ⟨cppEvaluate_unitary hU hP hQ _,cppCompile_clean U P Q hP hQ fs,cppCompile_counts fs⟩

end Qatlib.Concepts.QsvtCore.QsVtMain
