/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorLocality
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.TensorRegisters.RegisterModel

namespace Qatlib.Papers.DecisionTrees97.MainResults.RaisingHamiltonian

def raising : Matrix Bool Bool ℂ := fun out input => if out = true ∧ input = false then 1 else 0

def number : Matrix Bool Bool ℂ := Matrix.diagonal (fun b => if b then 1 else 0)

theorem raising_zero : ApplyGate raising (Ket false) = Ket true := by
  ext b
  cases b <;> norm_num [ApplyGate, Matrix.mulVec, dotProduct, raising,
    Qatlib.Foundations.PureStateMath.Ket, Fintype.sum_bool]

theorem raising_one : ApplyGate raising (Ket true) = 0 := by
  ext b
  cases b <;> norm_num [ApplyGate, Matrix.mulVec, dotProduct, raising,
    Qatlib.Foundations.PureStateMath.Ket, Fintype.sum_bool]

theorem number_hermitian : number.IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro b
  cases b <;> norm_num

def levelWire (n : ℕ) (i : Fin (n + 1)) : Fin (2 * n + 1) := ⟨i.val, by omega⟩

def pathWire (n : ℕ) (i : Fin n) : Fin (2 * n + 1) := ⟨n + 1 + i.val, by omega⟩

def wireFactors {N : ℕ} (w : Fin N) (M : Matrix Bool Bool ℂ) :
    Fin N → Matrix Bool Bool ℂ := fun j => if j = w then M else 1

def edgeFactors (n : ℕ) (i : Fin n) (branch : Bool) : Fin (2 * n + 1) → Matrix Bool Bool ℂ :=
  fun j => (wireFactors (levelWire n i.castSucc) raising j)ᴴ *
    wireFactors (levelWire n i.succ) raising j *
    wireFactors (pathWire n i) (if branch then raising else 1 - number) j

def forwardEdge (n : ℕ) (i : Fin n) (branch : Bool) : Matrix (Reg (2 * n + 1)) (Reg (2 * n + 1)) ℂ :=
  productMatrix (edgeFactors n i branch)

theorem forwardEdge_source_product (n : ℕ) (i : Fin n) (branch : Bool) :
    forwardEdge n i branch =
      (productMatrix (wireFactors (levelWire n i.castSucc) raising))ᴴ *
      productMatrix (wireFactors (levelWire n i.succ) raising) *
      productMatrix (wireFactors (pathWire n i) (if branch then raising else 1 - number)) := by
  rw [productMatrix_adjoint, productMatrix_mul, productMatrix_mul]
  rfl

def edgeSupport (n : ℕ) (i : Fin n) : Finset (Fin (2 * n + 1)) :=
  {levelWire n i.castSucc, levelWire n i.succ, pathWire n i}

theorem forwardEdge_local (n : ℕ) (i : Fin n) (branch : Bool) :
    TensorLocalOn (edgeSupport n i) (forwardEdge n i branch) := by
  apply productMatrix_tensor_local
  intro j hj
  have h1 : j ≠ levelWire n i.castSucc := by
    intro h
    apply hj
    simp [edgeSupport, h]
  have h2 : j ≠ levelWire n i.succ := by
    intro h
    apply hj
    simp [edgeSupport, h]
  have h3 : j ≠ pathWire n i := by
    intro h
    apply hj
    simp [edgeSupport, h]
  simp [edgeFactors, wireFactors, h1, h2, h3]

def hopTerm (n : ℕ) (i : Fin n) : Matrix (Reg (2 * n + 1)) (Reg (2 * n + 1)) ℂ :=
  -(forwardEdge n i false + (forwardEdge n i false)ᴴ +
    forwardEdge n i true + (forwardEdge n i true)ᴴ)

theorem hopTerm_three_local (n : ℕ) (i : Fin n) :
    (edgeSupport n i).card ≤ 3 ∧ TensorLocalOn (edgeSupport n i) (hopTerm n i) := by
  refine ⟨Finset.card_le_three, ?_⟩
  have h0 := forwardEdge_local n i false
  have h1 := forwardEdge_local n i true
  have h := tensorLocalOn_add _
    (tensorLocalOn_add _ (tensorLocalOn_add _ h0 (tensorLocalOn_adjoint _ h0)) h1)
    (tensorLocalOn_adjoint _ h1)
  simpa only [neg_one_smul] using! tensorLocalOn_smul _ h (-1)

theorem hopTerm_hermitian (n : ℕ) (i : Fin n) : (hopTerm n i).IsHermitian := by
  change (hopTerm n i)ᴴ = hopTerm n i
  simp only [hopTerm, Matrix.conjTranspose_neg, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose]
  abel

def degreeWeight (n : ℕ) (i : Fin (n + 1)) : ℂ :=
  if i.val = 0 then 2 else if i.val = n then 1 else 3

def degreeTerm (n : ℕ) (i : Fin (n + 1)) : Matrix (Reg (2 * n + 1)) (Reg (2 * n + 1)) ℂ :=
  degreeWeight n i • productMatrix (wireFactors (levelWire n i) number)

theorem degreeTerm_local (n : ℕ) (i : Fin (n + 1)) :
    TensorLocalOn {levelWire n i} (degreeTerm n i) := by
  apply tensorLocalOn_smul
  apply productMatrix_tensor_local
  intro j hj
  simp only [Finset.mem_singleton] at hj
  simp [wireFactors, hj]

theorem degreeTerm_hermitian (n : ℕ) (i : Fin (n + 1)) : (degreeTerm n i).IsHermitian := by
  have hp : (productMatrix (wireFactors (levelWire n i) number))ᴴ =
      productMatrix (wireFactors (levelWire n i) number) := by
    rw [productMatrix_adjoint]
    congr 1
    funext j
    simp only [wireFactors]
    split_ifs <;> simp [number_hermitian.eq]
  have hc : star (degreeWeight n i) = degreeWeight n i := by
    unfold degreeWeight
    split_ifs <;> norm_num
  change (degreeTerm n i)ᴴ = _
  rw [degreeTerm, Matrix.conjTranspose_smul, hp, hc]

def fullTreeHamiltonian (n : ℕ) : Matrix (Reg (2 * n + 1)) (Reg (2 * n + 1)) ℂ :=
  (∑ i : Fin (n + 1), degreeTerm n i) + ∑ i : Fin n, hopTerm n i

abbrev TermIndex (n : ℕ) := Sum (Fin (n + 1)) (Fin n)

def term (n : ℕ) : TermIndex n → Matrix (Reg (2 * n + 1)) (Reg (2 * n + 1)) ℂ
  | .inl i => degreeTerm n i
  | .inr i => hopTerm n i

theorem term_hermitian (n : ℕ) (i : TermIndex n) : (term n i).IsHermitian := by
  cases i with
  | inl i => exact degreeTerm_hermitian n i
  | inr i => exact hopTerm_hermitian n i

theorem source_sum_three_local (n : ℕ) :
    fullTreeHamiltonian n = ∑ i : TermIndex n, term n i ∧
      ∀ i : TermIndex n, ∃ S : Finset (Fin (2 * n + 1)),
        S.card ≤ 3 ∧ TensorLocalOn S (term n i) := by
  constructor
  · simp only [fullTreeHamiltonian, Fintype.sum_sum_type, term]
  · intro i
    cases i with
    | inl i => exact ⟨{levelWire n i}, by simp, degreeTerm_local n i⟩
    | inr i => exact ⟨edgeSupport n i, (hopTerm_three_local n i).1, (hopTerm_three_local n i).2⟩

end Qatlib.Papers.DecisionTrees97.MainResults.RaisingHamiltonian
