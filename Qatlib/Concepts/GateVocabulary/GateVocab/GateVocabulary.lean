/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabularyDefs
import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.PauliClifford.ExactRank

set_option autoImplicit false
universe u v w x

macro "gate_matrix" : tactic => `(tactic| (ext row col <;>
    (first
      | (guard_hyp row : Fin 0; fin_cases row)
      | (guard_hyp row : Fin 1; fin_cases row)
      | (guard_hyp row : Fin 2; fin_cases row)
      | (guard_hyp row : Bool; fin_cases row)) <;>
    (first
      | (guard_hyp col : Fin 0; fin_cases col)
      | (guard_hyp col : Fin 1; fin_cases col)
      | (guard_hyp col : Fin 2; fin_cases col)
      | (guard_hyp col : Bool; fin_cases col))))

namespace Qatlib.Concepts.GateVocabulary.GateVocab

open Matrix

theorem pauli_multiplication (a b : Fin 4) :
    pauliBool a * pauliBool b =
      pauliProductPhase a b • pauliBool (pauliProductIndex a b) := by
  fin_cases a <;> fin_cases b <;> ext i j <;> cases i <;> cases j <;>
    norm_num [pauliBool, pauliProductPhase, pauliProductIndex, pauliYBool,
      PauliX, PauliZ, permMatrix, Matrix.mul_apply, Fintype.sum_bool,
      Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]

theorem pauli_adjoint (a : Fin 4) : (pauliBool a)ᴴ = pauliBool a := by
  fin_cases a <;> ext i j <;> cases i <;> cases j <;>
    simp [pauliBool, pauliYBool, PauliX, PauliZ, permMatrix,
      Matrix.conjTranspose_apply]

theorem pauli_involution (a : Fin 4) : pauliBool a * pauliBool a = 1 := by
  rw [pauli_multiplication]
  fin_cases a <;> norm_num [pauliProductPhase, pauliProductIndex, pauliBool]

theorem pauli_unitary (a : Fin 4) : pauliBool a ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, pauli_adjoint]
  exact pauli_involution a

theorem phaseS_square : phaseS * phaseS = PauliZ := by
  ext i j
  cases i <;> cases j <;>
    norm_num [phaseS, PauliZ, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply]

theorem phaseS_fourth : phaseS ^ 4 = 1 := by
  calc
    phaseS ^ 4 = (phaseS * phaseS) * (phaseS * phaseS) := by noncomm_ring
    _ = 1 := by rw [phaseS_square, pauliZ_mul_self]

theorem phaseS_unitary : phaseS ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  cases i <;> cases j <;>
    norm_num [phaseS, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply]

theorem phaseS_adjoint_inverse : phaseSᴴ = phaseS⁻¹ := by
  apply (Matrix.inv_eq_left_inv ?_).symm
  simpa only [Matrix.star_eq_conjTranspose] using
    Matrix.mem_unitaryGroup_iff'.mp phaseS_unitary

theorem hadamard_x_intertwines : Hadamard * PauliX = PauliZ * Hadamard := by
  ext i j
  cases i <;> cases j <;>
    simp [Hadamard, PauliX, PauliZ, permMatrix, Matrix.mul_apply,
      Matrix.diagonal_apply]

theorem hadamard_x_conjugation : Hadamard * PauliX * Hadamard = PauliZ := by
  rw [hadamard_x_intertwines, Matrix.mul_assoc, hadamard_mul_self, Matrix.mul_one]

theorem hadamard_z_conjugation : Hadamard * PauliZ * Hadamard = PauliX := by
  rw [← hadamard_x_conjugation]
  simp only [← Matrix.mul_assoc, hadamard_mul_self, Matrix.one_mul]
  rw [Matrix.mul_assoc, hadamard_mul_self, Matrix.mul_one]

theorem toFinGate_adjoint (U : Matrix Bool Bool ℂ) :
    toFinGate Uᴴ = (toFinGate U)ᴴ := rfl

theorem toFinGate_eq_relabel (U : Matrix Bool Bool ℂ) :
    toFinGate U = relabelGate boolEquivFin2 U := rfl

theorem toFinGate_unitary {U : Matrix Bool Bool ℂ} (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    toFinGate U ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    ← toFinGate_adjoint, ← map_mul]
  have h := Matrix.mem_unitaryGroup_iff'.mp hU
  simpa only [Matrix.star_eq_conjTranspose, map_one] using congrArg toFinGate h

theorem pauliFin_unitary (a : Fin 4) : pauliFin a ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  toFinGate_unitary (pauli_unitary a)

theorem hadamardFin_unitary : hadamardFin ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  toFinGate_unitary hadamard_unitary

theorem phaseSFin_unitary : phaseSFin ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  toFinGate_unitary phaseS_unitary

theorem phaseSFin_fourth : phaseSFin ^ 4 = 1 := by
  simpa only [phaseSFin, map_pow, map_one] using congrArg toFinGate phaseS_fourth

theorem pauliFin_adjoint (a : Fin 4) : (pauliFin a)ᴴ = pauliFin a := by
  rw [pauliFin, ← toFinGate_adjoint, pauli_adjoint]

theorem pauliFin_involution (a : Fin 4) : pauliFin a * pauliFin a = 1 := by
  simpa only [pauliFin, map_mul, map_one] using congrArg toFinGate (pauli_involution a)

theorem hadamardFin_adjoint : hadamardFinᴴ = hadamardFin := by
  rw [hadamardFin, ← toFinGate_adjoint, hadamard_conjTranspose]

theorem hadamardFin_involution : hadamardFin * hadamardFin = 1 := by
  simpa only [hadamardFin, map_mul, map_one] using congrArg toFinGate hadamard_mul_self

theorem pauliFin_multiplication (a b : Fin 4) :
    pauliFin a * pauliFin b = pauliProductPhase a b • pauliFin (pauliProductIndex a b) := by
  simpa only [pauliFin, map_mul, map_smul] using congrArg toFinGate (pauli_multiplication a b)

theorem pauliFin_legacy : pauliFin 1 = pauliX ∧ pauliFin 2 = pauliY ∧ pauliFin 3 = pauliZ := by
  constructor
  · gate_matrix <;>
      norm_num [pauliFin, toFinGate, pauliBool, PauliX, permMatrix, pauliX,
        Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, boolEquivFin2]
  constructor
  · gate_matrix <;>
      norm_num [pauliFin, toFinGate, pauliBool, pauliYBool, pauliY,
        Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, boolEquivFin2]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pauliFin, toFinGate, pauliBool, PauliZ, pauliZ,
        Matrix.diagonal_apply, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, boolEquivFin2]

theorem pauliAxis_legacy (a : Fin 3) : pauliAxis a = pauliMatrix a := by
  fin_cases a
  · exact pauliFin_legacy.1
  · exact pauliFin_legacy.2.1
  · exact pauliFin_legacy.2.2

theorem pauliAxis_unitary (a : Fin 3) : pauliAxis a ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  pauliFin_unitary _

theorem tensor_product_unitary (n : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ i, A i ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    tensorPauliProduct n A ∈ Matrix.unitaryGroup (Fin (2^n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    tensorPauliProduct_conjTranspose, tensorPauliProduct_mul, ← tensorPauliProduct_one n]
  congr 1
  funext i
  simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp (hA i)

theorem pauli_axis_expansion (B : Matrix (Fin 2) (Fin 2) ℂ) :
    B = (1/2 : ℂ) • (Matrix.trace B • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ∑ a : Fin 3, Matrix.trace (pauliAxis a * B) • pauliAxis a) := by
  simp only [pauliAxis_legacy]
  have htr : Matrix.trace B = B 0 0 + B 1 1 := Matrix.trace_fin_two B
  have hx := trace_pauliX_mul B
  have hy := trace_pauliY_mul B
  have hz := trace_pauliZ_mul B
  have hyI : Complex.I • pauliY = !![(0 : ℂ), 1; -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliY, Matrix.smul_apply, Complex.I_mul_I]
  have hysplit : (Complex.I * B 0 1 - Complex.I * B 1 0) • pauliY =
      (B 0 1 - B 1 0) • (!![(0 : ℂ), 1; -1, 0]) := by
    rw [show Complex.I * B 0 1 - Complex.I * B 1 0 =
        Complex.I * (B 0 1 - B 1 0) from by ring, mul_smul, smul_comm, hyI]
  rw [htr, Fin.sum_univ_three, pauliMatrix_zero, pauliMatrix_one, pauliMatrix_two,
    hx, hy, hz, hysplit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliZ] <;> ring

theorem pauli_entry_resolution (x y u v : Fin 2) :
    (1/2 : ℂ) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) y x *
        (1 : Matrix (Fin 2) (Fin 2) ℂ) u v +
      ∑ a : Fin 3, pauliAxis a y x * pauliAxis a u v) =
        (if u = x then 1 else 0) * (if v = y then 1 else 0) := by
  have h := congrFun (congrFun (pauli_axis_expansion (Matrix.single x y (1 : ℂ))) u) v
  have ht : Matrix.trace (Matrix.single x y (1 : ℂ)) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) y x := by
    by_cases hxy : x = y
    · subst y
      simp
    · rw [Matrix.trace_single_eq_of_ne x y (1 : ℂ) hxy]
      simp [Ne.symm hxy]
  have hc (a : Fin 3) : Matrix.trace (pauliAxis a * Matrix.single x y (1 : ℂ)) =
      pauliAxis a y x := by simp [Matrix.trace_mul_single]
  have he : Matrix.single x y (1 : ℂ) u v =
      (if u = x then 1 else 0) * (if v = y then 1 else 0) := by
    by_cases hu : u = x
    · subst u
      by_cases hv : v = y
      · subst v
        simp
      · simp [hv, Ne.symm hv]
    · simp [hu, Ne.symm hu]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.sum_apply, ht, hc, he] at h
  exact h.symm

theorem pauli_shadow_reconstruction_kernel (x y u v : Fin 2) :
    (∑ o : Fin 3 × Bool,
      ((1/3 : ℂ) * PauliProjector o.1 o.2 y x) * PauliShadow o.2 o.1 u v) =
        (if u = x then 1 else 0) * (if v = y then 1 else 0) := by
  have hs (a : Fin 3) :
      (∑ b : Bool, ((1/3 : ℂ) * PauliProjector a b y x) * PauliShadow b a u v) =
        (1/6 : ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ) y x *
          (1 : Matrix (Fin 2) (Fin 2) ℂ) u v +
        (1/2 : ℂ) * (pauliAxis a y x * pauliAxis a u v) := by
    rw [pauliAxis_legacy]
    simp only [Fintype.sum_bool, PauliProjector, PauliShadow, if_true,
      Bool.false_eq_true, if_false, Matrix.smul_apply, smul_eq_mul,
      Matrix.add_apply, Matrix.sub_apply, one_mul, neg_one_mul]
    ring
  rw [Fintype.sum_prod_type]
  simp_rw [hs]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  calc
    _ = (1/2 : ℂ) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) y x *
        (1 : Matrix (Fin 2) (Fin 2) ℂ) u v +
          ∑ a : Fin 3, pauliAxis a y x * pauliAxis a u v) := by ring
    _ = _ := pauli_entry_resolution x y u v

theorem relabel_one {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) :
    relabelGate e (1 : Matrix I I ℂ) = 1 := Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_one e

theorem relabel_mul {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A B : Matrix I I ℂ) :
    relabelGate e (A * B) = relabelGate e A * relabelGate e B :=
  Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul e A B

theorem relabel_adjoint {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A : Matrix I I ℂ) :
    relabelGate e Aᴴ = (relabelGate e A)ᴴ := rfl

theorem relabel_tensor {I J I' J' : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    (e : I ≃ I') (f : J ≃ J') (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    relabelGate (Equiv.prodCongr e f) (TensorGate A B) =
      TensorGate (relabelGate e A) (relabelGate f B) := relabelGate_prodCongr e f A B

theorem regOneBool_path : regOneBool.trans boolEquivFin2 = bitVecEquiv 1 := by
  ext x
  have hx : x = fun _ => x 0 := by
    funext i
    congr 1
    exact Subsingleton.elim i 0
  rw [hx]
  generalize x 0 = b
  cases b <;> rfl

theorem matrix_ext_on_kets {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A B : Matrix J I ℂ)
    (h : ∀ x, A *ᵥ Qatlib.Foundations.PureStateMath.Ket x = B *ᵥ Qatlib.Foundations.PureStateMath.Ket x) : A = B := by
  ext i j
  have he := congrFun (h j) i
  simpa [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket] using he

theorem swapGate_unitary : swapGate ∈ Matrix.unitaryGroup (Bool × Bool) ℂ :=
  permMatrix_unitary (fun _ => rfl)

theorem toffoliUpdate_involutive {n : ℕ} (a b t : Fin n) (hat : a ≠ t) (hbt : b ≠ t) :
    Function.Involutive (toffoliUpdate a b t) := by
  intro x
  funext i
  by_cases hi : i = t
  · subst i
    simp [toffoliUpdate, hat, hbt]
  · simp [toffoliUpdate, hi]

theorem toffoliGate_unitary {n : ℕ} (a b t : Fin n) (hat : a ≠ t) (hbt : b ≠ t) :
    toffoliGate a b t ∈ Matrix.unitaryGroup (Reg n) ℂ :=
  permMatrix_unitary (toffoliUpdate_involutive a b t hat hbt)

theorem toffoli_fifteen_basis {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) :
    (toffoliLocalSteps a b t).length = 15 ∧ reflectionLegal (toffoliLocalSteps a b t) ∧
      ∀ x : Reg n, Run 1 (reflectionCompile (toffoliLocalSteps a b t)) (Qatlib.Foundations.PureStateMath.Ket x) =
        ApplyGate (toffoliGate a b t) (Qatlib.Foundations.PureStateMath.Ket x) := by
  obtain ⟨hlen, hlegal, hrun⟩ := local_toffoli_fifteen_exact n a b t hab hat hbt
  refine ⟨hlen, hlegal, fun x => ?_⟩
  rw [hrun, toffoliGate, applyGate_permMatrix_ket (toffoliUpdate_involutive a b t hat hbt)]
  rfl

theorem toffoli_fifteen_matrix {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) : reflectionProgramMatrix (toffoliLocalSteps a b t) = toffoliGate a b t := by
  apply matrix_ext_on_kets
  intro x
  have h := (toffoli_fifteen_basis a b t hab hat hbt).2.2 x
  rwa [run_reflectionCompile] at h

theorem toffoli_fifteen_whole_state {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (ψ : QState (Reg n)) :
    Run 1 (reflectionCompile (toffoliLocalSteps a b t)) ψ = ApplyGate (toffoliGate a b t) ψ := by
  rw [run_reflectionCompile, toffoli_fifteen_matrix a b t hab hat hbt]

theorem phaseSFin_adjoint_inverse : phaseSFinᴴ = phaseSFin⁻¹ := by
  apply (Matrix.inv_eq_left_inv ?_).symm
  simpa only [Matrix.star_eq_conjTranspose] using
    Matrix.mem_unitaryGroup_iff'.mp phaseSFin_unitary

theorem hadamardFin_x_conjugation :
    hadamardFin * pauliFin 1 * hadamardFin = pauliFin 3 := by
  change toFinGate Hadamard * toFinGate PauliX * toFinGate Hadamard = toFinGate PauliZ
  rw [← map_mul, ← map_mul, hadamard_x_conjugation]

theorem hadamardFin_z_conjugation :
    hadamardFin * pauliFin 3 * hadamardFin = pauliFin 1 := by
  change toFinGate Hadamard * toFinGate PauliZ * toFinGate Hadamard = toFinGate PauliX
  rw [← map_mul, ← map_mul, hadamard_z_conjugation]

theorem relabel_tensor_right_unit (I : Type*) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) :
    relabelGate (Equiv.prodPUnit I) (TensorGate A (1 : Matrix PUnit.{1} PUnit.{1} ℂ)) = A := by
  ext i j
  simp [relabelGate, Matrix.reindex_apply, TensorGate]

theorem relabel_tensor_left_unit (I : Type*) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) :
    relabelGate (Equiv.punitProd I) (TensorGate (1 : Matrix PUnit.{1} PUnit.{1} ℂ) A) = A := by
  ext i j
  simp [relabelGate, Matrix.reindex_apply, TensorGate]

theorem part1_clause1 :
  (∀ a : Fin 4, pauliBool a ∈ Matrix.unitaryGroup Bool ℂ ∧
    (pauliBool a)ᴴ = pauliBool a ∧ pauliBool a * pauliBool a = 1) ∧
  (Hadamard ∈ Matrix.unitaryGroup Bool ℂ ∧ Hadamardᴴ = Hadamard ∧
    Hadamard * Hadamard = 1) ∧
  (phaseS ∈ Matrix.unitaryGroup Bool ℂ ∧ phaseSᴴ = phaseS⁻¹ ∧ phaseS ^ 4 = 1) ∧
  (∀ a b : Fin 4,
    pauliBool a * pauliBool b = pauliProductPhase a b • pauliBool (pauliProductIndex a b)) ∧
  (Hadamard * PauliX * Hadamard = PauliZ ∧ Hadamard * PauliZ * Hadamard = PauliX) ∧
  (∀ a : Fin 4, pauliFin a ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    (pauliFin a)ᴴ = pauliFin a ∧ pauliFin a * pauliFin a = 1) ∧
  (hadamardFin ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ hadamardFinᴴ = hadamardFin ∧
    hadamardFin * hadamardFin = 1) ∧
  (phaseSFin ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ phaseSFinᴴ = phaseSFin⁻¹ ∧
    phaseSFin ^ 4 = 1) ∧
  (∀ a b : Fin 4,
    pauliFin a * pauliFin b = pauliProductPhase a b • pauliFin (pauliProductIndex a b)) ∧
  (pauliFin 1 = pauliX ∧ pauliFin 2 = pauliY ∧ pauliFin 3 = pauliZ) ∧
  (hadamardFin * pauliFin 1 * hadamardFin = pauliFin 3 ∧
    hadamardFin * pauliFin 3 * hadamardFin = pauliFin 1) ∧
  (∀ U : Matrix Bool Bool ℂ, toFinGate U = relabelGate boolEquivFin2 U) ∧
  (swapGate ∈ Matrix.unitaryGroup (Bool × Bool) ℂ ∧
    ∀ ψ : QState (Bool × Bool), ∀ x : Bool × Bool,
      ApplyGate swapGate ψ x = ψ (x.2, x.1)) ∧
  (∀ (n : ℕ) (a b t : Fin n), a ≠ b → a ≠ t → b ≠ t →
    toffoliGate a b t ∈ Matrix.unitaryGroup (Reg n) ℂ ∧
    reflectionLegal (toffoliLocalSteps a b t) ∧
    QueryCount (reflectionCompile (toffoliLocalSteps a b t)) = 0 ∧
    GateCount (reflectionCompile (toffoliLocalSteps a b t)) = 15 ∧
    reflectionProgramMatrix (toffoliLocalSteps a b t) = toffoliGate a b t ∧
    ∀ ψ : QState (Reg n),
      Run 1 (reflectionCompile (toffoliLocalSteps a b t)) ψ = ApplyGate (toffoliGate a b t) ψ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact ⟨pauli_unitary a, pauli_adjoint a, pauli_involution a⟩
  · exact ⟨hadamard_unitary, hadamard_conjTranspose, hadamard_mul_self⟩
  · exact ⟨phaseS_unitary, phaseS_adjoint_inverse, phaseS_fourth⟩
  · exact pauli_multiplication
  · exact ⟨hadamard_x_conjugation, hadamard_z_conjugation⟩
  · intro a
    exact ⟨pauliFin_unitary a, pauliFin_adjoint a, pauliFin_involution a⟩
  · exact ⟨hadamardFin_unitary, hadamardFin_adjoint, hadamardFin_involution⟩
  · exact ⟨phaseSFin_unitary, phaseSFin_adjoint_inverse, phaseSFin_fourth⟩
  · exact pauliFin_multiplication
  · exact pauliFin_legacy
  · exact ⟨hadamardFin_x_conjugation, hadamardFin_z_conjugation⟩
  · exact toFinGate_eq_relabel
  · exact ⟨swapGate_unitary, fun ψ x => applyGate_permMatrix (fun _ => rfl) ψ x⟩
  · intro n a b t hab hat hbt
    refine ⟨toffoliGate_unitary a b t hat hbt, (toffoli_fifteen_basis a b t hab hat hbt).2.1,
      ?_, ?_, toffoli_fifteen_matrix a b t hab hat hbt,
      toffoli_fifteen_whole_state a b t hab hat hbt⟩
    · exact queryCount_reflectionCompile _
    · rw [gateCount_reflectionCompile, toffoliLocalSteps_length]

theorem part1_clause2 :
  (∀ (I : Type u) (J : Type v) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (A B : Matrix I I ℂ),
    relabelGate e (1 : Matrix I I ℂ) = 1 ∧
    relabelGate e (A * B) = relabelGate e A * relabelGate e B ∧
    relabelGate e Aᴴ = (relabelGate e A)ᴴ) ∧
  (regOneBool.trans boolEquivFin2 = bitVecEquiv 1) ∧
  (∀ (I : Type u) (J : Type v) (K : Type w) (L : Type x)
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (e : I ≃ K) (f : J ≃ L) (A : Matrix I I ℂ) (B : Matrix J J ℂ),
    relabelGate (Equiv.prodCongr e f) (TensorGate A B) =
      TensorGate (relabelGate e A) (relabelGate f B)) ∧
  (∀ (I : Type u) (J : Type v) (K : Type w)
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) (C : Matrix K K ℂ),
    relabelGate (Equiv.prodAssoc I J K) (TensorGate (TensorGate A B) C) =
      TensorGate A (TensorGate B C)) ∧
  (∀ (I : Type u) (J : Type v)
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℂ) (B : Matrix J J ℂ),
    relabelGate (Equiv.prodComm I J) (TensorGate A B) = TensorGate B A) ∧
  (∀ (I : Type u) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ),
    relabelGate (Equiv.prodPUnit I) (TensorGate A (1 : Matrix PUnit.{1} PUnit.{1} ℂ)) = A ∧
    relabelGate (Equiv.punitProd I) (TensorGate (1 : Matrix PUnit.{1} PUnit.{1} ℂ) A) = A) ∧
  (∀ (I : Type u) (J : Type v) (K : Type w) (L : Type x)
    (A : Matrix (((I × J) × K) × L) (((I × J) × K) × L) ℂ),
    relabelGate
      (((Equiv.prodCongr (Equiv.prodAssoc I J K) (Equiv.refl L)).trans
        (Equiv.prodAssoc I (J × K) L)).trans
        (Equiv.prodCongr (Equiv.refl I) (Equiv.prodAssoc J K L))) A =
      relabelGate ((Equiv.prodAssoc (I × J) K L).trans
        (Equiv.prodAssoc I J (K × L))) A) ∧
  (∀ (I : Type u) (J : Type v) (A : Matrix ((I × PUnit.{1}) × J) ((I × PUnit.{1}) × J) ℂ),
    relabelGate ((Equiv.prodAssoc I PUnit.{1} J).trans
      (Equiv.prodCongr (Equiv.refl I) (Equiv.punitProd J))) A =
      relabelGate (Equiv.prodCongr (Equiv.prodPUnit I) (Equiv.refl J)) A) ∧
  (∀ (I : Type u) (J : Type v) (K : Type w)
    (A : Matrix ((I × J) × K) ((I × J) × K) ℂ),
    relabelGate (((Equiv.prodAssoc I J K).trans (Equiv.prodComm I (J × K))).trans
      (Equiv.prodAssoc J K I)) A =
      relabelGate (((Equiv.prodCongr (Equiv.prodComm I J) (Equiv.refl K)).trans
        (Equiv.prodAssoc J I K)).trans
        (Equiv.prodCongr (Equiv.refl J) (Equiv.prodComm I K))) A) ∧
  (∀ (I : Type u) (J : Type v) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (W : Matrix I I ℂ) (C : Circuit I) (ψ : QState I) (S : Finset I),
    Run (relabelGate e W) (relabelCircuit e C) (relabelState e ψ) = relabelState e (Run W C ψ) ∧
    MeasureProb (Run (relabelGate e W) (relabelCircuit e C) (relabelState e ψ))
      (S.map e.toEmbedding) = MeasureProb (Run W C ψ) S ∧
    QueryCount (relabelCircuit e C) = QueryCount C ∧
    GateCount (relabelCircuit e C) = GateCount C ∧ Size (relabelCircuit e C) = Size C ∧
    (IsUnitaryCircuit (relabelCircuit e C) ↔ IsUnitaryCircuit C)) := by
  refine ⟨?_, regOneBool_path, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro I J _ _ _ _ e A B
    exact ⟨relabel_one e, relabel_mul e A B, relabel_adjoint e A⟩
  · intro I J K L _ _ _ _ _ _ _ _ e f A B
    exact relabel_tensor e f A B
  · intro I J K _ _ _ _ _ _ A B C
    exact relabelGate_prodAssoc A B C
  · intro I J _ _ _ _ A B
    exact relabelGate_prodComm A B
  · intro I _ _ A
    exact ⟨relabel_tensor_right_unit I A, relabel_tensor_left_unit I A⟩
  · intro I J K L A
    rfl
  · intro I J A
    rfl
  · intro I J K A
    rfl
  · intro I J _ _ _ _ e W C ψ S
    obtain ⟨hrun,hprob⟩ := run_relabelCircuit_readout e W C ψ S
    obtain ⟨hlegal,hquery,hgate,hsize⟩ := relabelCircuit_legality_resources e C
    exact ⟨hrun,hprob,hquery,hgate,hsize,hlegal⟩

theorem part1_clause3 :
  (∀ (n : ℕ) (A B : Fin n → Operator 2),
    tensorPauliProduct n A * tensorPauliProduct n B = tensorPauliProduct n (fun i => A i * B i) ∧
    (tensorPauliProduct n A)ᴴ = tensorPauliProduct n (fun i => (A i)ᴴ) ∧
    Matrix.trace (tensorPauliProduct n A) = ∏ i, Matrix.trace (A i)) ∧
  (∀ n : ℕ, tensorPauliProduct n (fun _ => 1) = 1) ∧
  (∀ (I : Type u) (J : Type v) [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A B : Matrix J I ℂ),
    (∀ x, A *ᵥ Qatlib.Foundations.PureStateMath.Ket x = B *ᵥ Qatlib.Foundations.PureStateMath.Ket x) → A = B) ∧
  (∀ B : Operator 2,
    B = (1/2 : ℂ) • (Matrix.trace B • (1 : Operator 2) +
      ∑ a : Fin 3, Matrix.trace (pauliAxis a * B) • pauliAxis a)) ∧
  (∀ x y u v : Fin 2,
    (1/2 : ℂ) * ((1 : Operator 2) y x * (1 : Operator 2) u v +
      ∑ a : Fin 3, pauliAxis a y x * pauliAxis a u v) =
      (if u = x then 1 else 0) * (if v = y then 1 else 0)) ∧
  (∀ x y u v : Fin 2,
    (∑ o : Fin 3 × Bool,
      ((1/3 : ℂ) * PauliProjector o.1 o.2 y x) * PauliShadow o.2 o.1 u v) =
      (if u = x then 1 else 0) * (if v = y then 1 else 0)) := by
  refine ⟨?_, tensorPauliProduct_one, ?_, pauli_axis_expansion,
    pauli_entry_resolution, pauli_shadow_reconstruction_kernel⟩
  · intro n A B
    exact ⟨tensorPauliProduct_mul n A B, tensorPauliProduct_conjTranspose n A,
      tensorPauliProduct_trace n A⟩
  · intro I J _ _ _ _ A B h
    exact matrix_ext_on_kets A B h

end Qatlib.Concepts.GateVocabulary.GateVocab
