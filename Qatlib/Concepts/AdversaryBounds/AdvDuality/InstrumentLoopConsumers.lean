/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentLoopBudget
import Qatlib.Concepts.PauliClifford.ExactRank.MeasuredPauliShadows
import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol

/-!
# A Fair Flip Instrument Loop

This module constructs `fairFlipLoopInstrument`, whose halting branch scales the input by one
half and whose continuing branch scales Pauli-X conjugation by one half. The observed
implementation `fairFlipProgram` acts on a flag initialized by `fairFlipFrame`, measures it
after a Hadamard gate, and conditionally flips the data qubit; its elementary gates and
projective measurements use the standard quantum circuit formalism of [NielsenChuang2010].

The branch marginal calculation connects the observed circuit to the instrument. Summing the
unbounded loop gives `fairTerminal_eq`, with weights two thirds for the input and one third for
its Pauli-X conjugate, while normalized inputs have expected time two and zero nontermination
mass.

## Main statements

* `fairFlip_observed_branch_marginal` and `fairFlip_actual_branch_bridge` identify the
  implemented branch maps.
* `instrument_loop_fair_flip_actual_channel_consumer` collects the branch formulas, terminal
  channel, expected time, and nontermination mass.
* `fair_flip_program_legality_and_counts` records two leaves, each with zero queries, two gates,
  and one measurement.
* `fair_flip_expected_resources` evaluates the expected-time products for gates and measurements
  as four and two.

## References

- [Nielsen and Chuang, 2010][NielsenChuang2010], *Quantum Computation and Quantum Information*.
-/

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

/-- The computational-basis projector onto the zero state of the flag qubit. -/
noncomputable def fairFlagZero : Operator 2 := !![1, 0; 0, 0]

/-- The computational-basis projector onto the one state of the flag qubit. -/
noncomputable def fairFlagOne : Operator 2 := !![0, 0; 0, 1]

/-- The Hadamard operator used to prepare the fair flag measurement. -/
noncomputable def fairH : Operator 2 := pauliBasisMatrix 0

/-- The zero flag projector is idempotent. -/
private theorem fairFlagZero_mul_self : fairFlagZero * fairFlagZero = fairFlagZero := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [fairFlagZero, Matrix.mul_apply, Fin.sum_univ_two]

/-- The one flag projector is idempotent. -/
private theorem fairFlagOne_mul_self : fairFlagOne * fairFlagOne = fairFlagOne := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [fairFlagOne, Matrix.mul_apply, Fin.sum_univ_two]

/-- The zero flag projector is self-adjoint. -/
private theorem fairFlagZero_star : fairFlagZeroᴴ = fairFlagZero := by
  ext a b <;> fin_cases a <;> fin_cases b <;> simp [fairFlagZero, Matrix.conjTranspose_apply]

/-- The one flag projector is self-adjoint. -/
private theorem fairFlagOne_star : fairFlagOneᴴ = fairFlagOne := by
  ext a b <;> fin_cases a <;> fin_cases b <;> simp [fairFlagOne, Matrix.conjTranspose_apply]

/-- The zero flag projector has trace one. -/
private theorem trace_fairFlagZero : Matrix.trace fairFlagZero = 1 := by
  simp [Matrix.trace, fairFlagZero, Fin.sum_univ_two]

/-- The one flag projector has trace one. -/
private theorem trace_fairFlagOne : Matrix.trace fairFlagOne = 1 := by
  simp [Matrix.trace, fairFlagOne, Fin.sum_univ_two]

/-- The square of the Pauli-X operator is the identity. -/
private theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- The Pauli-X operator is self-adjoint. -/
private theorem pauliX_star : pauliXᴴ = pauliX := by
  ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauliX, Matrix.conjTranspose_apply]

/-- The Pauli-X operator belongs to the unitary group on a qubit. -/
private theorem fairPauliX_unitary : pauliX ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, pauliX_star, pauliX_mul_self]

/-- Conjugating a qubit operator twice by Pauli X returns the original operator. -/
private theorem pauliX_double_conj (Y : Operator 2) :
    pauliX * (pauliX * Y * pauliX) * pauliX = Y := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] <;>
    norm_num

/-- Conjugation by Pauli X preserves the trace of every qubit operator. -/
private theorem trace_pauliX_conj (M : Operator 2) :
    Matrix.trace (pauliX * M * pauliX) = Matrix.trace M := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, pauliX_mul_self, Matrix.one_mul]

/-- The flag Hadamard operator is self-adjoint. -/
private theorem fairH_star : fairHᴴ = fairH := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [fairH, pauliBasisMatrix_zero, Matrix.conjTranspose_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] <;>
    norm_num

/-- Compute the zero flag projector multiplied on the right by the flag Hadamard operator. -/
private theorem fZ_mul_H : fairFlagZero * fairH = ((Real.sqrt 2 : ℂ)⁻¹) • !![1, 1; 0, 0] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [fairFlagZero, fairH, pauliBasisMatrix_zero, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.mulVec, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.smul_apply, smul_eq_mul] <;>
    norm_num

/-- Compute the flag Hadamard operator multiplied on the right by the zero flag projector. -/
private theorem hH_fZ : fairH * fairFlagZero = ((Real.sqrt 2 : ℂ)⁻¹) • !![1, 0; 1, 0] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [fairFlagZero, fairH, pauliBasisMatrix_zero, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.mulVec, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.smul_apply, smul_eq_mul] <;>
    norm_num

/-- The unnormalized zero-outcome flag matrix sandwiches the zero flag projector to itself. -/
private theorem hAZ : (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * fairFlagZero
    * !![1, 0; 1, 0] = fairFlagZero := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [fairFlagZero, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    norm_num

/-- The zero-outcome Hadamard branch sends the zero flag projector to one half of that
projector. -/
private theorem fairFlagZero_sandwich :
    (fairFlagZero * fairH * fairFlagZero) * (fairH * fairFlagZero)
      = (1/2:ℂ) • fairFlagZero := by
  rw [fZ_mul_H, hH_fZ, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    sqrt2_inv_sq, hAZ]

/-- Compute the one flag projector multiplied on the right by the flag Hadamard operator. -/
private theorem fOne_mul_H : fairFlagOne * fairH = ((Real.sqrt 2 : ℂ)⁻¹) • !![0, 0; 1, -1] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [fairFlagOne, fairH, pauliBasisMatrix_zero, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.mulVec, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.smul_apply, smul_eq_mul] <;>
    norm_num

/-- Compute the flag Hadamard operator multiplied on the right by the one flag projector. -/
private theorem hH_fOne : fairH * fairFlagOne = ((Real.sqrt 2 : ℂ)⁻¹) • !![0, 1; 0, -1] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [fairFlagOne, fairH, pauliBasisMatrix_zero, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.mulVec, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.smul_apply, smul_eq_mul] <;>
    norm_num

/-- The unnormalized one-outcome flag matrix sandwiches the zero flag projector to the one flag
projector. -/
private theorem hBZ : (!![0, 0; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) * fairFlagZero
    * !![0, 1; 0, -1] = fairFlagOne := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [fairFlagOne, fairFlagZero, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec,
      dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    norm_num

/-- The one-outcome Hadamard branch sends the zero flag projector to one half of the one flag
projector. -/
private theorem fairFlagOne_sandwich :
    (fairFlagOne * fairH * fairFlagZero) * (fairH * fairFlagOne)
      = (1/2:ℂ) • fairFlagOne := by
  rw [fOne_mul_H, hH_fOne, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    sqrt2_inv_sq, hBZ]

/-- The complex inverse square root of two is fixed by conjugation. -/
private theorem star_sqrt2_inv : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
  rw [← starRingEnd_apply, Complex.conj_inv, Complex.conj_ofReal]

/-- Embedding the real scalar one half into the complex numbers gives the complex scalar one
half. -/
private theorem half_ofReal : ((1/2:ℝ):ℂ) = (1/2:ℂ) := by norm_num

/-- Powers of complex one half equal the complex embeddings of the corresponding real powers. -/
private theorem half_pow_real (k : ℕ) : ((1/2:ℂ)^k) = (((1/2:ℝ)^k : ℝ) : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ, ih, ← half_ofReal, ← Complex.ofReal_mul]

/-- Multiplication by the real scalar one half multiplies the real part of a complex number by
one half. -/
private theorem half_mul_re (z : ℂ) : (((1/2:ℝ):ℂ) * z).re = (1/2:ℝ) * z.re := by
  rw [Complex.mul_re]
  norm_num

/-- The tensor product of qubit operators distributes over addition in its first factor. -/
private theorem tensorGate_add_left (A B : Operator 2) (V : Operator 2) :
    TensorGate (A + B) V = TensorGate A V + TensorGate B V := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [tensorGate_apply, Matrix.add_apply]
  ring

/-- The tensor product of qubit operators distributes over addition in its second factor. -/
private theorem tensorGate_add_right (U A B : Operator 2) :
    TensorGate U (A + B) = TensorGate U A + TensorGate U B := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [tensorGate_apply, Matrix.add_apply]
  ring

/-- A complex scalar in the second tensor factor can be pulled out of `TensorGate`. -/
private theorem tensorGate_smul_right (c : ℂ) (U V : Operator 2) :
    TensorGate U (c • V) = c • TensorGate U V := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [tensorGate_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- A complex scalar in the first tensor factor can be pulled out of `TensorGate`. -/
private theorem tensorGate_smul_left (c : ℂ) (U V : Operator 2) :
    TensorGate (c • U) V = c • TensorGate U V := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [tensorGate_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The tensor product of qubit operators distributes over subtraction in its first factor. -/
private theorem tensorGate_sub_left (A B V : Operator 2) :
    TensorGate (A - B) V = TensorGate A V - TensorGate B V := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [tensorGate_apply, Matrix.sub_apply]
  ring

/-- The complement of the zero flag projector is the one flag projector. -/
private theorem one_sub_fairFlagZero : (1 : Operator 2) - fairFlagZero = fairFlagOne := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [fairFlagOne, fairFlagZero, Matrix.one_apply]

/-- The complement of `TensorGate U 1` is the tensor product of `1 - U` with the identity. -/
private theorem one_sub_tensorGate (U : Operator 2) :
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - TensorGate U 1
      = TensorGate (1 - U) 1 := by
  rw [← tensorGate_one, ← tensorGate_sub_left]

/-- Tracing out the first factor of a qubit tensor product multiplies the second factor by the
trace of the first. -/
private theorem traceLeft_tensorGate (A Y : Operator 2) :
    Matrix.traceLeft (TensorGate A Y) = (Matrix.trace A) • Y := by
  ext b b'
  show ∑ a : Fin 2, A a a * Y b b' = (Matrix.trace A) * Y b b'
  simp only [Matrix.trace, Matrix.diag_apply, Finset.sum_mul]

/-- Partial trace over the first subsystem preserves addition for matrices with a qubit second
subsystem. -/
private theorem traceLeft_add_general {d : ℕ} [Fintype (Fin d)]
    (A B : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) :
    Matrix.traceLeft (A + B) = Matrix.traceLeft A + Matrix.traceLeft B := by
  ext c c'
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.add_apply, Finset.sum_add_distrib]

/-- Partial trace over the first subsystem preserves complex scalar multiplication for matrices
with a qubit second subsystem. -/
private theorem traceLeft_smul_general {d : ℕ} [Fintype (Fin d)] (c : ℂ)
    (A : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) :
    Matrix.traceLeft (c • A) = c • Matrix.traceLeft A := by
  ext c' c''
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.smul_apply, Finset.mul_sum, smul_eq_mul]

/-- Relabeling matrix indices by an equivalence preserves subtraction. -/
private theorem relabelGate_sub_general {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A B : Matrix I I ℂ) :
    relabelGate e (A - B) = relabelGate e A - relabelGate e B := by
  ext x y <;> simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply]

/-- Relabeling matrix indices by an equivalence preserves the orthogonal projector property. -/
private theorem isOrthogonalProjector_relabelGate {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) {P : Matrix I I ℂ} (hP : IsOrthogonalProjector P) :
    IsOrthogonalProjector (relabelGate e P) := by
  refine ⟨?_, ?_⟩
  · show relabelGate e P * relabelGate e P = relabelGate e P
    rw [← teleportRelabelGate_mul, hP.1]
  · show (relabelGate e P)ᴴ = relabelGate e P
    have h2 : Pᴴ = P := hP.2
    rw [teleportRelabelGate_conjTranspose, h2]

/-- The halting branch map defined by the Kraus operator equal to the identity divided by the
square root of two. -/
noncomputable def fairFlipTrueMap : Operator 2 →ₗ[ℂ] Operator 2 :=
  conjBranch ((Real.sqrt 2 : ℂ)⁻¹ • (1 : Operator 2))

/-- The continuing branch map defined by the Kraus operator equal to Pauli X divided by the
square root of two. -/
noncomputable def fairFlipFalseMap : Operator 2 →ₗ[ℂ] Operator 2 :=
  conjBranch ((Real.sqrt 2 : ℂ)⁻¹ • pauliX)

/-- The fair halting map scales each input operator by one half. -/
theorem fairFlipTrueMap_apply (X : Operator 2) :
    fairFlipTrueMap X = (1/2:ℂ) • X := by
  rw [fairFlipTrueMap, conjBranch_apply, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    star_sqrt2_inv]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, smul_smul,
    sqrt2_inv_sq]

/-- The fair continuing map is one half of conjugation by Pauli X. -/
theorem fairFlipFalseMap_apply (X : Operator 2) :
    fairFlipFalseMap X = (1/2:ℂ) • (pauliX * X * pauliX) := by
  rw [fairFlipFalseMap, conjBranch_apply, Matrix.conjTranspose_smul, pauliX_star,
    star_sqrt2_inv]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sqrt2_inv_sq]

/-- The Boolean qubit instrument that halts with one-half-scaled identity output and continues
with one-half-scaled Pauli-X conjugation. -/
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

/-- The true branch of the fair flip instrument scales the input operator by one half. -/
theorem fairFlip_branch_true (X : Operator 2) :
    fairFlipLoopInstrument.branch true X = (1/2:ℂ) • X :=
  fairFlipTrueMap_apply X

/-- The false branch of the fair flip instrument is one half of Pauli-X conjugation of the
input. -/
theorem fairFlip_branch_false (X : Operator 2) :
    fairFlipLoopInstrument.branch false X = (1/2:ℂ) • (pauliX * X * pauliX) :=
  fairFlipFalseMap_apply X

/-- The standard equivalence flattening a flag qubit and a data qubit into a four-dimensional
register. -/
def fairRegEquiv : (Fin 2 × Fin 2) ≃ Fin 4 := finProdFinEquiv

/-- The two-qubit gate applying the flag Hadamard operator and the identity on the data qubit. -/
noncomputable def fairFlipHGate : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  TensorGate fairH (1 : Operator 2)

/-- The projector onto a zero flag, tensored with the identity on the data qubit. -/
noncomputable def fairFlipProj : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  TensorGate fairFlagZero (1 : Operator 2)

/-- The two-qubit gate applying the identity on the flag and Pauli X on the data qubit. -/
noncomputable def fairFlipXGate : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  TensorGate (1 : Operator 2) pauliX

/-- The joint branch operator for the fair flip implementation: a Hadamard followed by flag
projection, with a data flip on the false branch. -/
noncomputable def fairFlipK : Bool → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
  | true => fairFlipProj * fairFlipHGate
  | false => fairFlipXGate * (1 - fairFlipProj) * fairFlipHGate

/-- The flag Hadamard gate is unitary after flattening the two-qubit register. -/
private theorem fairFlipHGate_unitary :
    relabelGate fairRegEquiv fairFlipHGate ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary (pauliBasisMatrix_unitary 0) (Submonoid.one_mem _)) _

/-- The data Pauli-X gate is unitary after flattening the two-qubit register. -/
private theorem fairFlipXGate_unitary :
    relabelGate fairRegEquiv fairFlipXGate ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary (Submonoid.one_mem _) fairPauliX_unitary) _

/-- The zero-flag measurement operator is an orthogonal projector on the joint register. -/
private theorem fairFlipProj_projector : IsOrthogonalProjector fairFlipProj := by
  refine ⟨?_, ?_⟩
  · show fairFlipProj * fairFlipProj = fairFlipProj
    rw [fairFlipProj, tensorGate_mul, fairFlagZero_mul_self, Matrix.mul_one]
  · show fairFlipProjᴴ = fairFlipProj
    rw [fairFlipProj, tensorGate_conjTranspose, fairFlagZero_star, Matrix.conjTranspose_one]

/-- An observed circuit that applies a flag Hadamard, measures the zero-flag projector, and
applies a data flip on the false branch or an identity gate on the true branch. -/
noncomputable def fairFlipProgram : ObservedCircuit (Fin 4) :=
  .step (.gate (relabelGate fairRegEquiv fairFlipHGate))
    (.project (relabelGate fairRegEquiv fairFlipProj)
      (.step (.gate (relabelGate fairRegEquiv fairFlipXGate)) (.halt false))
      (.step (.gate (1 : Operator 4)) (.halt true)))

/-- The fair flip observed circuit is well formed. -/
theorem fairFlip_wf : observedWellFormed fairFlipProgram := by
  simp only [fairFlipProgram, observedWellFormed]
  exact ⟨fairFlipHGate_unitary,
    ⟨isOrthogonalProjector_relabelGate _ fairFlipProj_projector,
      ⟨⟨fairFlipXGate_unitary, trivial⟩, ⟨Submonoid.one_mem _, trivial⟩⟩⟩⟩

/-- The fair flip observed circuit has exactly two leaves. -/
theorem fairFlip_leaf_count : observedLeafCount fairFlipProgram = 2 := rfl

/-- Select the fair flip circuit leaf with the given Boolean acceptance value. -/
noncomputable def fairFlipLeaf (b : Bool) : Fin (observedLeafCount fairFlipProgram) :=
  Fin.cast (rfl) (if b then (1 : Fin 2) else (0 : Fin 2))

/-- The leaf selected by `b` has acceptance value `b`, zero queries, two gates, and one
measurement. -/
theorem fairFlip_leaf_data (b : Bool) :
    (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).accepted = b ∧
    (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).queries = 0 ∧
    (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).gates = 2 ∧
    (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).measurements = 1 := by
  cases b <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Expand the false leaf operator as the ordered product of the data flip, the complement of
the flag projector, and the flag Hadamard, including the initial identity factor. -/
theorem fairFlipLeafOperator_raw_false :
    (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf false)).operator
      = (((1 : Operator 4) * relabelGate fairRegEquiv fairFlipXGate)
        * (1 - relabelGate fairRegEquiv fairFlipProj))
        * relabelGate fairRegEquiv fairFlipHGate := rfl

/-- Expand the true leaf operator as the ordered product of the identity gate, the flag
projector, and the flag Hadamard, including the initial identity factor. -/
theorem fairFlipLeafOperator_raw_true :
    (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf true)).operator
      = (((1 : Operator 4) * 1) * relabelGate fairRegEquiv fairFlipProj)
        * relabelGate fairRegEquiv fairFlipHGate := rfl

/-- The operator of the leaf selected by `b` is the relabeled joint branch operator `fairFlipK
b`. -/
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

/-- Embed a data-qubit operator into the four-dimensional register with the flag fixed in its
zero state. -/
noncomputable def fairFlipFrame (X : Operator 2) : Operator 4 :=
  relabelGate fairRegEquiv (TensorGate fairFlagZero X)

/-- Apply the joint branch operator to a zero-flag input and trace out the flag to obtain the
data-qubit branch output. -/
noncomputable def fairFlipActualBranchCore (b : Bool) (X : Operator 2) : Operator 2 :=
  Matrix.traceLeft (fairFlipK b * TensorGate fairFlagZero X * (fairFlipK b).conjTranspose)

/-- The complex-linear map packaging the flag-initialized, flag-traced branch operation
`fairFlipActualBranchCore`. -/
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

/-- The true joint branch operator is the tensor product of the zero-flag Hadamard branch with
the data identity. -/
private theorem fairFlipK_true : fairFlipK true = TensorGate (fairFlagZero * fairH) 1 := by
  rw [fairFlipK, fairFlipProj, fairFlipHGate, tensorGate_mul, Matrix.one_mul]

/-- The false joint branch operator is the tensor product of the one-flag Hadamard branch with
data Pauli X. -/
private theorem fairFlipK_false :
    fairFlipK false = TensorGate (fairFlagOne * fairH) pauliX := by
  rw [fairFlipK, fairFlipXGate, fairFlipProj, one_sub_tensorGate, one_sub_fairFlagZero,
    fairFlipHGate, tensorGate_mul, Matrix.one_mul, tensorGate_mul, Matrix.mul_one,
    Matrix.mul_one]

/-- After initialization and tracing out the flag, the true joint branch scales the data
operator by one half. -/
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

/-- After initialization and tracing out the flag, the false joint branch gives one half of
Pauli-X conjugation of the data operator. -/
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

/-- Coarsen the observed fair flip instrument by acceptance, apply it to a zero-flag input, undo
the register relabeling, and trace out the flag. The resulting branch output is
`fairFlipActualBranchCore b X`. -/
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

/-- Each implemented data-qubit branch map equals the corresponding branch of
`fairFlipLoopInstrument`. -/
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

/-- The candidate terminal output mixing the input with weight two thirds and its Pauli-X
conjugate with weight one third. -/
noncomputable def fairTerminalCandidate (X : Operator 2) : Operator 2 :=
  (2/3:ℂ) • X + (1/3:ℂ) • (pauliX * X * pauliX)

/-- Return the input for even `n` and its Pauli-X conjugate for odd `n`. -/
private noncomputable def fairFlipConjPow (n : ℕ) (Y : Operator 2) : Operator 2 :=
  if n % 2 = 0 then Y else pauliX * Y * pauliX

/-- After `n` continuing branches, the fair flip loop output is scaled by `(1/2) ^ n` and
conjugated by Pauli X exactly when `n` is odd. -/
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

/-- The fair flip output that halts after `n` continuations is one half of the output surviving
those continuations. -/
theorem fairHaltAt_eq (n : ℕ) (Y : Operator 2) :
    loopHaltAt fairFlipLoopInstrument n Y
      = (1/2:ℂ) • loopContinueMap fairFlipLoopInstrument n Y :=
  fairFlip_branch_true _

/-- Applying one continuing branch before `n` further continuations equals applying `n + 1`
continuations. -/
private theorem loopContinueMap_comp_branch_false {D : ℕ} (I : Instrument Bool D D) (n : ℕ)
    (Y : Operator D) :
    loopContinueMap I n (I.branch false Y) = loopContinueMap I (n + 1) Y := by
  induction n generalizing Y with
  | zero => rfl
  | succ n ih => rw [loopContinueMap_succ_apply, loopContinueMap_succ_apply, ih]

/-- The candidate terminal output equals the immediate true-branch output plus the false branch
applied to that candidate output. -/
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

/-- The candidate terminal output decomposes into the first `n` halting outputs plus `n`
continuing branches applied to the candidate output. -/
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

/-- Exchange the two computational-basis indices of a qubit. -/
private def fairFlipIdx (a : Fin 2) : Fin 2 := if a = 0 then 1 else 0

/-- Conjugation by Pauli X exchanges both matrix indices according to `fairFlipIdx`. -/
private theorem pauliX_conj_entry (M : Operator 2) (a b : Fin 2) :
    (pauliX * M * pauliX) a b = M (fairFlipIdx a) (fairFlipIdx b) := by
  fin_cases a <;> fin_cases b <;>
    simp only [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, fairFlipIdx, reduceIte] <;>
    norm_num

set_option maxHeartbeats 400000 in

/-- The terminal fair flip loop map is the mixture of the identity map with weight two thirds
and Pauli-X conjugation with weight one third. -/
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

/-- For a density input, the real trace surviving `k` fair flip continuations is exactly `(1/2)
^ k`. -/
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

/-- For a density input, the fair flip pending mass at step `k` is `ENNReal.ofReal ((1/2) ^ k)`. -/
private theorem fairPending (ρ : Operator 2) (hρ : IsDensityOperator ρ) (k : ℕ) :
    loopPending fairFlipLoopInstrument ρ k = ENNReal.ofReal ((1/2:ℝ)^k) := by
  rw [loopPending, fairTraceContinue ρ hρ k]

/-- The expected number of fair flip loop rounds is exactly two for every density input. -/
private theorem fairExpectedTime (ρ : Operator 2) (hρ : IsDensityOperator ρ) :
    loopExpectedTime fairFlipLoopInstrument ρ = 2 := by
  have hfun : loopPending fairFlipLoopInstrument ρ
      = fun k => ENNReal.ofReal ((1/2:ℝ)^k) :=
    funext fun k => fairPending ρ hρ k
  rw [loopExpectedTime, hfun]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k : ℕ => pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) k)
    summable_geometric_two, tsum_geometric_two]
  simp

/-- The real trace of the fair flip continuing branch is at most one half of the input real
trace for every positive semidefinite input. -/
theorem fairFlip_branch_false_contraction (X : Operator 2) (_hX : X.PosSemidef) :
    (Matrix.trace (fairFlipLoopInstrument.branch false X)).re
      ≤ (1/2:ℝ) * (Matrix.trace X).re := by
  rw [fairFlip_branch_false, Matrix.trace_smul, smul_eq_mul, trace_pauliX_conj,
    ← half_ofReal, half_mul_re]

/-- The fair flip loop has zero nontermination mass for every density input. -/
private theorem fairNeverMass (ρ : Operator 2) (hρ : IsDensityOperator ρ) :
    loopNeverMass fairFlipLoopInstrument ρ = 0 :=
  (instrument_loop_geometric_actual_trace_cutoff 2 fairFlipLoopInstrument (1/2:ℝ) ρ
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1) hρ
    fairFlip_branch_false_contraction).2.1

/-- Collect the fair flip branch formulas and terminal mixture, together with expected time two
and zero nontermination mass for every density input. -/
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

/-- The fair flip circuit is well formed and has two leaves, each carrying its designated
acceptance bit, zero queries, two gates, and one measurement. -/
theorem fair_flip_program_legality_and_counts :
    observedWellFormed fairFlipProgram ∧ observedLeafCount fairFlipProgram = 2 ∧
    (∀ b : Bool, (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).accepted = b ∧
      (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).queries = 0 ∧
      (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).gates = 2 ∧
      (observedLeaf (1 : Operator 4) fairFlipProgram (fairFlipLeaf b)).measurements = 1) :=
  ⟨fairFlip_wf, rfl, fun b => fairFlip_leaf_data b⟩

/-- For a density input, fair flip expected time is two; multiplying its real value by two gates
or one measurement per round gives four gates or two measurements, respectively. -/
theorem fair_flip_expected_resources (ρ : Operator 2) (hρ : IsDensityOperator ρ) :
    loopExpectedTime fairFlipLoopInstrument ρ = 2 ∧
    (loopExpectedTime fairFlipLoopInstrument ρ).toReal * 2 = 4 ∧
    (loopExpectedTime fairFlipLoopInstrument ρ).toReal * 1 = 2 := by
  refine ⟨fairExpectedTime ρ hρ, ?_, ?_⟩ <;>
    rw [fairExpectedTime ρ hρ] <;> simp <;> norm_num

end Qatlib.Concepts.AdversaryBounds.AdvDuality
