/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentLoopBudget
import Qatlib.Concepts.PauliClifford.ExactRank.MeasuredPauliShadows
import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.MixedInstrument.ClockBridge
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped ComplexOrder ENNReal

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

noncomputable def fairFlagZero : Operator 2 := !![1, 0; 0, 0]

noncomputable def fairFlagOne : Operator 2 := !![0, 0; 0, 1]

noncomputable def fairH : Operator 2 := pauliBasisMatrix 0

private theorem fairFlagZero_mul_self : fairFlagZero * fairFlagZero = fairFlagZero := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [fairFlagZero, Matrix.mul_apply, Fin.sum_univ_two]

private theorem fairFlagOne_mul_self : fairFlagOne * fairFlagOne = fairFlagOne := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [fairFlagOne, Matrix.mul_apply, Fin.sum_univ_two]

private theorem fairFlagZero_star : fairFlagZeroᴴ = fairFlagZero := by
  ext a b <;> fin_cases a <;> fin_cases b <;> simp [fairFlagZero, Matrix.conjTranspose_apply]

private theorem fairFlagOne_star : fairFlagOneᴴ = fairFlagOne := by
  ext a b <;> fin_cases a <;> fin_cases b <;> simp [fairFlagOne, Matrix.conjTranspose_apply]

private theorem trace_fairFlagZero : Matrix.trace fairFlagZero = 1 := by
  simp [Matrix.trace, fairFlagZero, Fin.sum_univ_two]

private theorem trace_fairFlagOne : Matrix.trace fairFlagOne = 1 := by
  simp [Matrix.trace, fairFlagOne, Fin.sum_univ_two]

private theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

private theorem pauliX_star : pauliXᴴ = pauliX := by
  ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauliX, Matrix.conjTranspose_apply]

private theorem fairPauliX_unitary : pauliX ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, pauliX_star, pauliX_mul_self]

private theorem pauliX_double_conj (Y : Operator 2) :
    pauliX * (pauliX * Y * pauliX) * pauliX = Y := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] <;>
    norm_num

private theorem trace_pauliX_conj (M : Operator 2) :
    Matrix.trace (pauliX * M * pauliX) = Matrix.trace M := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, pauliX_mul_self, Matrix.one_mul]

private theorem fairH_star : fairHᴴ = fairH := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [fairH, pauliBasisMatrix_zero, Matrix.conjTranspose_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] <;>
    norm_num

private theorem fZ_mul_H : fairFlagZero * fairH = ((Real.sqrt 2 : ℂ)⁻¹) • !![1, 1; 0, 0] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [fairFlagZero, fairH, pauliBasisMatrix_zero, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.mulVec, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.smul_apply, smul_eq_mul] <;>
    norm_num

private theorem hH_fZ : fairH * fairFlagZero = ((Real.sqrt 2 : ℂ)⁻¹) • !![1, 0; 1, 0] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [fairFlagZero, fairH, pauliBasisMatrix_zero, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.mulVec, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.smul_apply, smul_eq_mul] <;>
    norm_num

private theorem hAZ : (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * fairFlagZero
    * !![1, 0; 1, 0] = fairFlagZero := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [fairFlagZero, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    norm_num

private theorem fairFlagZero_sandwich :
    (fairFlagZero * fairH * fairFlagZero) * (fairH * fairFlagZero)
      = (1/2:ℂ) • fairFlagZero := by
  rw [fZ_mul_H, hH_fZ, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    sqrt2_inv_sq, hAZ]

private theorem fOne_mul_H : fairFlagOne * fairH = ((Real.sqrt 2 : ℂ)⁻¹) • !![0, 0; 1, -1] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [fairFlagOne, fairH, pauliBasisMatrix_zero, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.mulVec, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.smul_apply, smul_eq_mul] <;>
    norm_num

private theorem hH_fOne : fairH * fairFlagOne = ((Real.sqrt 2 : ℂ)⁻¹) • !![0, 1; 0, -1] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [fairFlagOne, fairH, pauliBasisMatrix_zero, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.mulVec, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.smul_apply, smul_eq_mul] <;>
    norm_num

private theorem hBZ : (!![0, 0; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) * fairFlagZero
    * !![0, 1; 0, -1] = fairFlagOne := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [fairFlagOne, fairFlagZero, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec,
      dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    norm_num

private theorem fairFlagOne_sandwich :
    (fairFlagOne * fairH * fairFlagZero) * (fairH * fairFlagOne)
      = (1/2:ℂ) • fairFlagOne := by
  rw [fOne_mul_H, hH_fOne, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    sqrt2_inv_sq, hBZ]

private theorem star_sqrt2_inv : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
  rw [← starRingEnd_apply, Complex.conj_inv, Complex.conj_ofReal]

private theorem half_ofReal : ((1/2:ℝ):ℂ) = (1/2:ℂ) := by norm_num

private theorem half_pow_real (k : ℕ) : ((1/2:ℂ)^k) = (((1/2:ℝ)^k : ℝ) : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ, ih, ← half_ofReal, ← Complex.ofReal_mul]

private theorem half_mul_re (z : ℂ) : (((1/2:ℝ):ℂ) * z).re = (1/2:ℝ) * z.re := by
  rw [Complex.mul_re]
  norm_num

private theorem tensorGate_add_left (A B : Operator 2) (V : Operator 2) :
    TensorGate (A + B) V = TensorGate A V + TensorGate B V := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [tensorGate_apply, Matrix.add_apply]
  ring

private theorem tensorGate_add_right (U A B : Operator 2) :
    TensorGate U (A + B) = TensorGate U A + TensorGate U B := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [tensorGate_apply, Matrix.add_apply]
  ring

private theorem tensorGate_smul_right (c : ℂ) (U V : Operator 2) :
    TensorGate U (c • V) = c • TensorGate U V := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [tensorGate_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem tensorGate_smul_left (c : ℂ) (U V : Operator 2) :
    TensorGate (c • U) V = c • TensorGate U V := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [tensorGate_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem tensorGate_sub_left (A B V : Operator 2) :
    TensorGate (A - B) V = TensorGate A V - TensorGate B V := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [tensorGate_apply, Matrix.sub_apply]
  ring

private theorem one_sub_fairFlagZero : (1 : Operator 2) - fairFlagZero = fairFlagOne := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [fairFlagOne, fairFlagZero, Matrix.one_apply]

private theorem one_sub_tensorGate (U : Operator 2) :
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - TensorGate U 1
      = TensorGate (1 - U) 1 := by
  rw [← tensorGate_one, ← tensorGate_sub_left]

private theorem traceLeft_tensorGate (A Y : Operator 2) :
    Matrix.traceLeft (TensorGate A Y) = (Matrix.trace A) • Y := by
  ext b b'
  show ∑ a : Fin 2, A a a * Y b b' = (Matrix.trace A) * Y b b'
  simp only [Matrix.trace, Matrix.diag_apply, Finset.sum_mul]

private theorem traceLeft_add_general {d : ℕ} [Fintype (Fin d)]
    (A B : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) :
    Matrix.traceLeft (A + B) = Matrix.traceLeft A + Matrix.traceLeft B := by
  ext c c'
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.add_apply, Finset.sum_add_distrib]

private theorem traceLeft_smul_general {d : ℕ} [Fintype (Fin d)] (c : ℂ)
    (A : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) :
    Matrix.traceLeft (c • A) = c • Matrix.traceLeft A := by
  ext c' c''
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.smul_apply, Finset.mul_sum, smul_eq_mul]

private theorem relabelGate_sub_general {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A B : Matrix I I ℂ) :
    relabelGate e (A - B) = relabelGate e A - relabelGate e B := by
  ext x y <;> simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply]

private theorem isOrthogonalProjector_relabelGate {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) {P : Matrix I I ℂ} (hP : IsOrthogonalProjector P) :
    IsOrthogonalProjector (relabelGate e P) := by
  refine ⟨?_, ?_⟩
  · show relabelGate e P * relabelGate e P = relabelGate e P
    rw [← teleportRelabelGate_mul, hP.1]
  · show (relabelGate e P)ᴴ = relabelGate e P
    have h2 : Pᴴ = P := hP.2
    rw [teleportRelabelGate_conjTranspose, h2]

noncomputable def fairFlipTrueMap : Operator 2 →ₗ[ℂ] Operator 2 :=
  conjBranch ((Real.sqrt 2 : ℂ)⁻¹ • (1 : Operator 2))

noncomputable def fairFlipFalseMap : Operator 2 →ₗ[ℂ] Operator 2 :=
  conjBranch ((Real.sqrt 2 : ℂ)⁻¹ • pauliX)

theorem fairFlipTrueMap_apply (X : Operator 2) :
    fairFlipTrueMap X = (1/2:ℂ) • X := by
  rw [fairFlipTrueMap, conjBranch_apply, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    star_sqrt2_inv]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, smul_smul,
    sqrt2_inv_sq]

theorem fairFlipFalseMap_apply (X : Operator 2) :
    fairFlipFalseMap X = (1/2:ℂ) • (pauliX * X * pauliX) := by
  rw [fairFlipFalseMap, conjBranch_apply, Matrix.conjTranspose_smul, pauliX_star,
    star_sqrt2_inv]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sqrt2_inv_sq]

noncomputable def fairFlipLoopInstrument : Instrument Bool 2 2 :=
  Instrument.ofBranches (fun b => if b then fairFlipTrueMap else fairFlipFalseMap)
    (fun b => by cases b <;> exact completelyPositive_conjBranch _)
    (fun A => by
      have hsum : ∑ o : Bool,
          (if o then fairFlipTrueMap else fairFlipFalseMap) A
          = fairFlipFalseMap A + fairFlipTrueMap A := by
        simp [add_comm]
      rw [hsum, fairFlipTrueMap_apply, fairFlipFalseMap_apply, Matrix.trace_add,
        Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, trace_pauliX_conj,
        ← two_mul, ← mul_assoc]
      norm_num)

theorem fairFlip_branch_true (X : Operator 2) :
    fairFlipLoopInstrument.branch true X = (1/2:ℂ) • X :=
  fairFlipTrueMap_apply X

theorem fairFlip_branch_false (X : Operator 2) :
    fairFlipLoopInstrument.branch false X = (1/2:ℂ) • (pauliX * X * pauliX) :=
  fairFlipFalseMap_apply X

def fairRegEquiv : (Fin 2 × Fin 2) ≃ Fin 4 := finProdFinEquiv

noncomputable def fairFlipHGate : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  TensorGate fairH (1 : Operator 2)

noncomputable def fairFlipProj : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  TensorGate fairFlagZero (1 : Operator 2)

noncomputable def fairFlipXGate : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  TensorGate (1 : Operator 2) pauliX

noncomputable def fairFlipK : Bool → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
  | true => fairFlipProj * fairFlipHGate
  | false => fairFlipXGate * (1 - fairFlipProj) * fairFlipHGate

private theorem fairFlipHGate_unitary :
    relabelGate fairRegEquiv fairFlipHGate ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary (pauliBasisMatrix_unitary 0) (Submonoid.one_mem _)) _

private theorem fairFlipXGate_unitary :
    relabelGate fairRegEquiv fairFlipXGate ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary (Submonoid.one_mem _) fairPauliX_unitary) _

private theorem fairFlipProj_projector : IsOrthogonalProjector fairFlipProj := by
  refine ⟨?_, ?_⟩
  · show fairFlipProj * fairFlipProj = fairFlipProj
    rw [fairFlipProj, tensorGate_mul, fairFlagZero_mul_self, Matrix.mul_one]
  · show fairFlipProjᴴ = fairFlipProj
    rw [fairFlipProj, tensorGate_conjTranspose, fairFlagZero_star, Matrix.conjTranspose_one]

noncomputable def fairFlipProgram : ObservedCircuit (Fin 4) :=
  .step (.gate (relabelGate fairRegEquiv fairFlipHGate))
    (.project (relabelGate fairRegEquiv fairFlipProj)
      (.step (.gate (relabelGate fairRegEquiv fairFlipXGate)) (.halt false))
      (.step (.gate (1 : Operator 4)) (.halt true)))

theorem fairFlip_wf : observedWellFormed fairFlipProgram := by
  simp only [fairFlipProgram, observedWellFormed]
  exact ⟨fairFlipHGate_unitary,
    ⟨isOrthogonalProjector_relabelGate _ fairFlipProj_projector,
      ⟨⟨fairFlipXGate_unitary, trivial⟩, ⟨Submonoid.one_mem _, trivial⟩⟩⟩⟩

theorem fairFlip_leaf_count : observedLeafCount fairFlipProgram = 2 := rfl

noncomputable def fairFlipLeaf (b : Bool) : Fin (observedLeafCount fairFlipProgram) :=
  Fin.cast (rfl) (if b then (1 : Fin 2) else (0 : Fin 2))

theorem fairFlip_leaf_data (b : Bool) :
    (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).accepted = b ∧
    (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).queries = 0 ∧
    (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).gates = 2 ∧
    (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).measurements = 1 := by
  cases b <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem fairFlipLeafOperator_raw_false :
    (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf false)).operator
      = (((1 : Operator 4) * relabelGate fairRegEquiv fairFlipXGate)
        * (1 - relabelGate fairRegEquiv fairFlipProj))
        * relabelGate fairRegEquiv fairFlipHGate := rfl

theorem fairFlipLeafOperator_raw_true :
    (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf true)).operator
      = (((1 : Operator 4) * 1) * relabelGate fairRegEquiv fairFlipProj)
        * relabelGate fairRegEquiv fairFlipHGate := rfl

theorem fairFlipLeafOperator_eq (b : Bool) :
    (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).operator
      = relabelGate fairRegEquiv (fairFlipK b) := by
  cases b
  · rw [fairFlipLeafOperator_raw_false, Matrix.one_mul]
    have h1 : (1 : Operator 4) - relabelGate fairRegEquiv fairFlipProj
        = relabelGate fairRegEquiv (1 - fairFlipProj) := by
      rw [← teleportRelabelGate_one fairRegEquiv, ← relabelGate_sub_general]
    rw [h1, ← teleportRelabelGate_mul, ← teleportRelabelGate_mul, fairFlipK]
  · rw [fairFlipLeafOperator_raw_true, Matrix.one_mul, Matrix.one_mul,
      ← teleportRelabelGate_mul, fairFlipK]

noncomputable def fairFlipFrame (X : Operator 2) : Operator 4 :=
  relabelGate fairRegEquiv (TensorGate fairFlagZero X)

noncomputable def fairFlipActualBranchCore (b : Bool) (X : Operator 2) : Operator 2 :=
  Matrix.traceLeft (fairFlipK b * TensorGate fairFlagZero X * (fairFlipK b).conjTranspose)

noncomputable def fairFlipActualBranchMap (b : Bool) : Operator 2 →ₗ[ℂ] Operator 2 where
  toFun := fairFlipActualBranchCore b
  map_add' := by
    intro ρ σ
    unfold fairFlipActualBranchCore
    simp only [Matrix.mul_add, Matrix.add_mul, tensorGate_add_right, traceLeft_add_general]
  map_smul' := by
    intro r ρ
    unfold fairFlipActualBranchCore
    simp only [Matrix.mul_smul, Matrix.smul_mul, tensorGate_smul_right,
      traceLeft_smul_general, RingHom.id_apply]

private theorem fairFlipK_true : fairFlipK true = TensorGate (fairFlagZero * fairH) 1 := by
  rw [fairFlipK, fairFlipProj, fairFlipHGate, tensorGate_mul, Matrix.one_mul]

private theorem fairFlipK_false :
    fairFlipK false = TensorGate (fairFlagOne * fairH) pauliX := by
  rw [fairFlipK, fairFlipXGate, fairFlipProj, one_sub_tensorGate, one_sub_fairFlagZero,
    fairFlipHGate, tensorGate_mul, Matrix.one_mul, tensorGate_mul, Matrix.mul_one,
    Matrix.mul_one]

theorem fairFlipActualBranchCore_true (X : Operator 2) :
    fairFlipActualBranchCore true X = (1/2:ℂ) • X := by
  rw [fairFlipActualBranchCore, fairFlipK_true]
  have h1 : TensorGate (fairFlagZero * fairH) 1 * TensorGate fairFlagZero X
        * (TensorGate (fairFlagZero * fairH) 1).conjTranspose
      = (1/2:ℂ) • TensorGate fairFlagZero X := by
    rw [tensorGate_conjTranspose, Matrix.conjTranspose_mul, fairFlagZero_star, fairH_star,
      Matrix.conjTranspose_one, tensorGate_mul, tensorGate_mul, Matrix.one_mul,
      Matrix.mul_one, fairFlagZero_sandwich, tensorGate_smul_left]
  rw [h1, traceLeft_smul_general, traceLeft_tensorGate, smul_smul, trace_fairFlagZero,
    mul_one]

theorem fairFlipActualBranchCore_false (X : Operator 2) :
    fairFlipActualBranchCore false X = (1/2:ℂ) • (pauliX * X * pauliX) := by
  rw [fairFlipActualBranchCore, fairFlipK_false]
  have h1 : TensorGate (fairFlagOne * fairH) pauliX * TensorGate fairFlagZero X
        * (TensorGate (fairFlagOne * fairH) pauliX).conjTranspose
      = (1/2:ℂ) • TensorGate fairFlagOne (pauliX * X * pauliX) := by
    rw [tensorGate_conjTranspose, Matrix.conjTranspose_mul, fairFlagOne_star, fairH_star,
      pauliX_star, tensorGate_mul, tensorGate_mul, fairFlagOne_sandwich,
      tensorGate_smul_left]
  rw [h1, traceLeft_smul_general, traceLeft_tensorGate, smul_smul, trace_fairFlagOne,
    mul_one]

theorem fairFlip_observed_branch_marginal (b : Bool) (X : Operator 2) :
    Matrix.traceLeft (relabelGate fairRegEquiv.symm
        (((observedInstrument (1 : Operator 4) (Submonoid.one_mem _) fairFlipProgram
          fairFlip_wf).coarsen
          (fun i => (observedLeaf (1 : Operator 4) fairFlipProgram i).accepted)).branch b
          (fairFlipFrame X)))
      = fairFlipActualBranchCore b X := by
  have hparts : ∀ i : Fin (observedLeafCount fairFlipProgram),
      i = fairFlipLeaf true ∨ i = fairFlipLeaf false := by
    intro i
    fin_cases i
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hsum : (∑ i ∈ Finset.univ.filter
        (fun i => (observedLeaf (1 : Operator 4) fairFlipProgram i).accepted = b),
        (observedInstrument (1 : Operator 4) (Submonoid.one_mem _) fairFlipProgram
          fairFlip_wf).branch i (fairFlipFrame X))
      = (observedInstrument (1 : Operator 4) (Submonoid.one_mem _) fairFlipProgram
          fairFlip_wf).branch (fairFlipLeaf b) (fairFlipFrame X) := by
    refine Finset.sum_eq_single (fairFlipLeaf b) ?_ ?_
    · intro i hmem hni
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      rcases hparts i with h | h
      · cases b
        · exact absurd hmem (by rw [h, (fairFlip_leaf_data true).1]; simp)
        · exact (hni h).elim
      · cases b
        · exact (hni h).elim
        · exact absurd hmem (by rw [h, (fairFlip_leaf_data false).1]; simp)
    · intro hout
      exact absurd (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (fairFlip_leaf_data b).1) hout
  have hcoe : (((observedInstrument (1 : Operator 4) (Submonoid.one_mem _) fairFlipProgram
        fairFlip_wf).coarsen
        (fun i => (observedLeaf (1 : Operator 4) fairFlipProgram i).accepted)).branch b
        (fairFlipFrame X))
      = ∑ i ∈ Finset.univ.filter
          (fun i => (observedLeaf (1 : Operator 4) fairFlipProgram i).accepted = b),
          (observedInstrument (1 : Operator 4) (Submonoid.one_mem _) fairFlipProgram
            fairFlip_wf).branch i (fairFlipFrame X) := by
    simp only [Instrument.coarsen, LinearMap.sum_apply]
  rw [hcoe, hsum]
  show Matrix.traceLeft (relabelGate fairRegEquiv.symm
      (conjBranch ((observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).operator)
        (fairFlipFrame X))) = _
  rw [conjBranch_apply, fairFlipLeafOperator_eq b, fairFlipFrame, ← teleportRelabelGate_mul,
    teleportRelabelGate_conjTranspose, ← teleportRelabelGate_mul, relabelGate_relabelGate]
  rfl

theorem fairFlip_actual_branch_bridge :
    ∀ b : Bool, fairFlipActualBranchMap b = fairFlipLoopInstrument.branch b := by
  intro b
  apply LinearMap.ext
  intro X
  cases b
  · show fairFlipActualBranchCore false X = fairFlipLoopInstrument.branch false X
    rw [fairFlipActualBranchCore_false, fairFlip_branch_false]
  · show fairFlipActualBranchCore true X = fairFlipLoopInstrument.branch true X
    rw [fairFlipActualBranchCore_true, fairFlip_branch_true]

noncomputable def fairTerminalCandidate (X : Operator 2) : Operator 2 :=
  (2/3:ℂ) • X + (1/3:ℂ) • (pauliX * X * pauliX)

private noncomputable def fairFlipConjPow (n : ℕ) (Y : Operator 2) : Operator 2 :=
  if n % 2 = 0 then Y else pauliX * Y * pauliX

theorem fairContinue_eq (n : ℕ) (Y : Operator 2) :
    loopContinueMap fairFlipLoopInstrument n Y
      = (((1/2:ℝ)^n : ℝ) : ℂ) • fairFlipConjPow n Y := by
  induction n generalizing Y with
  | zero => simp [fairFlipConjPow]
  | succ n ih =>
      have hc : (((1/2:ℝ)^(n+1) : ℝ) : ℂ)
          = (((1/2:ℝ)^n : ℝ) : ℂ) * (1/2:ℂ) := by
        rw [pow_succ, Complex.ofReal_mul, half_ofReal]
      rw [loopContinueMap_succ_apply, ih, map_smul, fairFlip_branch_false, smul_smul, ← hc]
      by_cases hpar : n % 2 = 0
      · have h1 : ¬ (n + 1) % 2 = 0 := by omega
        simp only [fairFlipConjPow, if_pos hpar, if_neg h1]
      · have h1 : (n + 1) % 2 = 0 := by omega
        simp only [fairFlipConjPow, if_neg hpar, if_pos h1, pauliX_double_conj]

theorem fairHaltAt_eq (n : ℕ) (Y : Operator 2) :
    loopHaltAt fairFlipLoopInstrument n Y
      = (1/2:ℂ) • loopContinueMap fairFlipLoopInstrument n Y :=
  fairFlip_branch_true _

private theorem loopContinueMap_comp_branch_false {D : ℕ} (I : Instrument Bool D D) (n : ℕ)
    (Y : Operator D) :
    loopContinueMap I n (I.branch false Y) = loopContinueMap I (n + 1) Y := by
  induction n generalizing Y with
  | zero => rfl
  | succ n ih => rw [loopContinueMap_succ_apply, loopContinueMap_succ_apply, ih]

private theorem fairFixed (X : Operator 2) :
    fairTerminalCandidate X = fairFlipLoopInstrument.branch true X
      + fairFlipLoopInstrument.branch false (fairTerminalCandidate X) := by
  have hconj : pauliX * fairTerminalCandidate X * pauliX
      = (2/3:ℂ) • (pauliX * X * pauliX) + (1/3:ℂ) • X := by
    rw [fairTerminalCandidate, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, pauliX_double_conj]
  rw [fairFlip_branch_true, fairFlip_branch_false, hconj, fairTerminalCandidate]
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, pauliX, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    ring

private theorem fair_candidate_partial (X : Operator 2) (n : ℕ) :
    fairTerminalCandidate X = loopPartialMap fairFlipLoopInstrument n X
      + loopContinueMap fairFlipLoopInstrument n (fairTerminalCandidate X) := by
  induction n with
  | zero => simp [loopPartialMap_apply]
  | succ n ih =>
      have hps : loopPartialMap fairFlipLoopInstrument (n + 1) X
          = loopPartialMap fairFlipLoopInstrument n X
            + loopHaltAt fairFlipLoopInstrument n X := by
        rw [loopPartialMap_apply, loopPartialMap_apply, Finset.sum_range_succ]
      have hcomm : loopContinueMap fairFlipLoopInstrument n
            (fairFlipLoopInstrument.branch true X)
          = fairFlipLoopInstrument.branch true (loopContinueMap fairFlipLoopInstrument n X) := by
        rw [fairFlip_branch_true, fairFlip_branch_true, map_smul]
      have hkey : loopContinueMap fairFlipLoopInstrument n (fairTerminalCandidate X)
          = loopHaltAt fairFlipLoopInstrument n X
            + loopContinueMap fairFlipLoopInstrument (n + 1) (fairTerminalCandidate X) := by
        rw [loopHaltAt_apply]
        conv_lhs => rw [fairFixed X]
        rw [map_add, hcomm, loopContinueMap_comp_branch_false]
      rw [hps]
      calc fairTerminalCandidate X
          = loopPartialMap fairFlipLoopInstrument n X
            + loopContinueMap fairFlipLoopInstrument n (fairTerminalCandidate X) := ih
        _ = loopPartialMap fairFlipLoopInstrument n X
            + (loopHaltAt fairFlipLoopInstrument n X
              + loopContinueMap fairFlipLoopInstrument (n + 1)
                  (fairTerminalCandidate X)) := by rw [hkey]
        _ = (loopPartialMap fairFlipLoopInstrument n X + loopHaltAt fairFlipLoopInstrument n X)
            + loopContinueMap fairFlipLoopInstrument (n + 1)
                (fairTerminalCandidate X) := (add_assoc _ _ _).symm

private def fairFlipIdx (a : Fin 2) : Fin 2 := if a = 0 then 1 else 0

private theorem pauliX_conj_entry (M : Operator 2) (a b : Fin 2) :
    (pauliX * M * pauliX) a b = M (fairFlipIdx a) (fairFlipIdx b) := by
  fin_cases a <;> fin_cases b <;>
    simp only [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, fairFlipIdx, reduceIte] <;>
    norm_num

set_option maxHeartbeats 400000 in

theorem fairTerminal_eq (X : Operator 2) :
    loopTerminalMap fairFlipLoopInstrument X
      = (2/3:ℂ) • X + (1/3:ℂ) • (pauliX * X * pauliX) := by
  refine tendsto_nhds_unique (loopTerminalMap_tendsto fairFlipLoopInstrument X) ?_
  rw [tendsto_matrix_iff_entrywise]
  intro i j
  have hsplit : (fun n => (loopPartialMap fairFlipLoopInstrument n X) i j)
      = fun n => (fairTerminalCandidate X) i j
          - (loopContinueMap fairFlipLoopInstrument n (fairTerminalCandidate X)) i j := by
    funext n
    have h := fair_candidate_partial X n
    have hentry : (fairTerminalCandidate X) i j
        = ((loopPartialMap fairFlipLoopInstrument n) X) i j
          + ((loopContinueMap fairFlipLoopInstrument n) (fairTerminalCandidate X)) i j := by
      conv_lhs => rw [h]
      rw [Matrix.add_apply]
    rw [hentry]
    abel
  rw [hsplit]
  show Filter.Tendsto (fun n => (fairTerminalCandidate X) i j
      - (loopContinueMap fairFlipLoopInstrument n (fairTerminalCandidate X)) i j)
      Filter.atTop (nhds ((fairTerminalCandidate X) i j))
  set D := fairTerminalCandidate X with hD
  have hC : ∀ a b : Fin 2, ‖D a b‖
      ≤ ‖D 0 0‖ + ‖D 0 1‖ + ‖D 1 0‖ + ‖D 1 1‖ := by
    intro a b
    fin_cases a <;> fin_cases b
    · show ‖D 0 0‖ ≤ ‖D 0 0‖ + ‖D 0 1‖ + ‖D 1 0‖ + ‖D 1 1‖
      nlinarith [norm_nonneg (D 0 1), norm_nonneg (D 1 0), norm_nonneg (D 1 1)]
    · show ‖D 0 1‖ ≤ ‖D 0 0‖ + ‖D 0 1‖ + ‖D 1 0‖ + ‖D 1 1‖
      nlinarith [norm_nonneg (D 0 0), norm_nonneg (D 1 0), norm_nonneg (D 1 1)]
    · show ‖D 1 0‖ ≤ ‖D 0 0‖ + ‖D 0 1‖ + ‖D 1 0‖ + ‖D 1 1‖
      nlinarith [norm_nonneg (D 0 0), norm_nonneg (D 0 1), norm_nonneg (D 1 1)]
    · show ‖D 1 1‖ ≤ ‖D 0 0‖ + ‖D 0 1‖ + ‖D 1 0‖ + ‖D 1 1‖
      nlinarith [norm_nonneg (D 0 0), norm_nonneg (D 0 1), norm_nonneg (D 1 0)]
  have hbound : ∀ n : ℕ, ‖(loopContinueMap fairFlipLoopInstrument n D) i j‖
      ≤ ((1/2:ℝ)^n) * (‖D 0 0‖ + ‖D 0 1‖ + ‖D 1 0‖ + ‖D 1 1‖) := by
    intro n
    have hnn : (0:ℝ) ≤ (1/2:ℝ)^n := pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n
    have hn : ‖(((1/2:ℝ)^n : ℝ) : ℂ)‖ = (1/2:ℝ)^n := by
      simp [abs_of_nonneg hnn]
    rw [fairContinue_eq n D, Matrix.smul_apply, smul_eq_mul, Complex.norm_mul, hn]
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hp : n % 2 = 0 := by omega
      simpa only [fairFlipConjPow, if_pos hp] using
        mul_le_mul_of_nonneg_left (hC i j) hnn
    · have hp : ¬ n % 2 = 0 := by omega
      simp only [fairFlipConjPow, if_neg hp, pauliX_conj_entry]
      exact mul_le_mul_of_nonneg_left (hC (fairFlipIdx i) (fairFlipIdx j)) hnn
  have hlim0 : Filter.Tendsto
      (fun n => ((1/2:ℝ)^n) * (‖D 0 0‖ + ‖D 0 1‖ + ‖D 1 0‖ + ‖D 1 1‖))
      Filter.atTop (nhds 0) := by
    simpa using Filter.Tendsto.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1))
      (tendsto_const_nhds
        (x := ‖D 0 0‖ + ‖D 0 1‖ + ‖D 1 0‖ + ‖D 1 1‖))
  have hClim : Filter.Tendsto
      (fun n => (loopContinueMap fairFlipLoopInstrument n D) i j) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hbound hlim0
  have hsub := (tendsto_const_nhds (x := D i j)).sub hClim
  simpa using hsub

private theorem fairTraceContinue (ρ : Operator 2) (hρ : IsDensityOperator ρ) (k : ℕ) :
    (Matrix.trace (loopContinueMap fairFlipLoopInstrument k ρ)).re = (1/2:ℝ)^k := by
  rw [fairContinue_eq k ρ, Matrix.trace_smul, smul_eq_mul]
  have htr : Matrix.trace (fairFlipConjPow k ρ) = 1 := by
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hp : k % 2 = 0 := by omega
      simpa only [fairFlipConjPow, if_pos hp] using hρ.2
    · have hp : ¬ k % 2 = 0 := by omega
      rw [fairFlipConjPow, if_neg hp, trace_pauliX_conj]
      exact hρ.2
  rw [htr, mul_one, Complex.ofReal_re]

private theorem fairPending (ρ : Operator 2) (hρ : IsDensityOperator ρ) (k : ℕ) :
    loopPending fairFlipLoopInstrument ρ k = ENNReal.ofReal ((1/2:ℝ)^k) := by
  rw [loopPending, fairTraceContinue ρ hρ k]

private theorem fairExpectedTime (ρ : Operator 2) (hρ : IsDensityOperator ρ) :
    loopExpectedTime fairFlipLoopInstrument ρ = 2 := by
  have hfun : loopPending fairFlipLoopInstrument ρ
      = fun k => ENNReal.ofReal ((1/2:ℝ)^k) :=
    funext fun k => fairPending ρ hρ k
  rw [loopExpectedTime, hfun]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k : ℕ => pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) k)
    summable_geometric_two, tsum_geometric_two]
  simp

theorem fairFlip_branch_false_contraction (X : Operator 2) (_hX : X.PosSemidef) :
    (Matrix.trace (fairFlipLoopInstrument.branch false X)).re
      ≤ (1/2:ℝ) * (Matrix.trace X).re := by
  rw [fairFlip_branch_false, Matrix.trace_smul, smul_eq_mul, trace_pauliX_conj,
    ← half_ofReal, half_mul_re]

private theorem fairNeverMass (ρ : Operator 2) (hρ : IsDensityOperator ρ) :
    loopNeverMass fairFlipLoopInstrument ρ = 0 :=
  (instrument_loop_geometric_actual_trace_cutoff 2 fairFlipLoopInstrument (1/2:ℝ) ρ
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1) hρ
    fairFlip_branch_false_contraction).2.1

theorem instrument_loop_fair_flip_actual_channel_consumer :
    (∀ X : Operator 2,
      fairFlipLoopInstrument.branch true X = (1/2:ℂ) • X ∧
      fairFlipLoopInstrument.branch false X = (1/2:ℂ) • (pauliX*X*pauliX)) ∧
    (∀ X : Operator 2, loopTerminalMap fairFlipLoopInstrument X = (2/3:ℂ) • X + (1/3:ℂ) • (pauliX*X*pauliX)) ∧
    (∀ (ρ : Operator 2), IsDensityOperator ρ → loopExpectedTime fairFlipLoopInstrument ρ = 2 ∧
        loopNeverMass fairFlipLoopInstrument ρ = 0) :=
  ⟨fun X => ⟨fairFlip_branch_true X, fairFlip_branch_false X⟩,
    fun X => fairTerminal_eq X,
    fun ρ hρ => ⟨fairExpectedTime ρ hρ, fairNeverMass ρ hρ⟩⟩

theorem fair_flip_program_legality_and_counts :
    observedWellFormed fairFlipProgram ∧ observedLeafCount fairFlipProgram = 2 ∧
    (∀ b : Bool, (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).accepted = b ∧
      (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).queries = 0 ∧
      (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).gates = 2 ∧
      (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).measurements = 1) :=
  ⟨fairFlip_wf, rfl, fun b => fairFlip_leaf_data b⟩

theorem fair_flip_expected_resources (ρ : Operator 2) (hρ : IsDensityOperator ρ) :
    loopExpectedTime fairFlipLoopInstrument ρ = 2 ∧
    (loopExpectedTime fairFlipLoopInstrument ρ).toReal * 2 = 4 ∧
    (loopExpectedTime fairFlipLoopInstrument ρ).toReal * 1 = 2 := by
  refine ⟨fairExpectedTime ρ hρ, ?_, ?_⟩ <;>
    rw [fairExpectedTime ρ hρ] <;> simp <;> norm_num

end Qatlib.Concepts.AdversaryBounds.AdvDuality
