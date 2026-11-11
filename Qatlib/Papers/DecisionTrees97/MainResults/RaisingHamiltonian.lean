/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorLocality
import Mathlib.Tactic

/-!
# Raising-operator tree Hamiltonian

This module constructs a tree Hamiltonian from single-bit raising and number operators. It
defines branch edge matrices, Hermitian hopping terms, and weighted degree terms, then proves
that the full Hamiltonian is a sum of Hermitian terms tensor-local on at most three wires.

These constructions accompany the results of [FarhiGutmann1998].

## Main statements

* `forwardEdge_source_product`: factors a forward edge into lifted single-wire operators.
* `term_hermitian`: proves Hermiticity of each indexed term.
* `source_sum_three_local`: gives the decomposition and the tensor-support bound.

## References

* [Farhi and Gutmann, 1998][FarhiGutmann1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.TensorRegisters.RegisterModel

namespace Qatlib.Papers.DecisionTrees97.MainResults.RaisingHamiltonian

/-- The single-bit matrix mapping the false basis state to the true basis state and annihilating
the true basis state. -/
def raising : Matrix Bool Bool ℂ := fun out input => if out = true ∧ input = false then 1 else 0

/-- The diagonal projector onto the true single-bit basis state. -/
def number : Matrix Bool Bool ℂ := Matrix.diagonal (fun b => if b then 1 else 0)

/-- The raising matrix maps the false basis state to the true basis state. -/
theorem raising_zero : ApplyGate raising (Ket false) = Ket true := by
  ext b
  cases b <;> norm_num [ApplyGate, Matrix.mulVec, dotProduct, raising,
    Qatlib.Foundations.PureStateMath.Ket, Fintype.sum_bool]

/-- The raising matrix annihilates the true basis state. -/
theorem raising_one : ApplyGate raising (Ket true) = 0 := by
  ext b
  cases b <;> norm_num [ApplyGate, Matrix.mulVec, dotProduct, raising,
    Qatlib.Foundations.PureStateMath.Ket, Fintype.sum_bool]

/-- The single-bit number projector is Hermitian. -/
theorem number_hermitian : number.IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro b
  cases b <;> norm_num

/-- The register wire occupied by a level bit in the first `n + 1` positions. -/
def levelWire (n : ℕ) (i : Fin (n + 1)) : Fin (2 * n + 1) := ⟨i.val, by omega⟩

/-- The register wire occupied by a path bit in the last `n` positions. -/
def pathWire (n : ℕ) (i : Fin n) : Fin (2 * n + 1) := ⟨n + 1 + i.val, by omega⟩

/-- The family containing `M` at wire `w` and the identity at every other wire. -/
def wireFactors {N : ℕ} (w : Fin N) (M : Matrix Bool Bool ℂ) :
    Fin N → Matrix Bool Bool ℂ := fun j => if j = w then M else 1

/-- The single-wire factors combining lowering at the source level, raising at the next level,
and the chosen path-bit branch operator. -/
def edgeFactors (n : ℕ) (i : Fin n) (branch : Bool) : Fin (2 * n + 1) → Matrix Bool Bool ℂ :=
  fun j => (wireFactors (levelWire n i.castSucc) raising j)ᴴ *
    wireFactors (levelWire n i.succ) raising j *
    wireFactors (pathWire n i) (if branch then raising else 1 - number) j

/-- The product matrix of the single-wire factors for a forward branch edge. -/
def forwardEdge (n : ℕ) (i : Fin n) (branch : Bool) : Matrix (Reg (2 * n + 1)) (Reg (2 * n + 1)) ℂ :=
  productMatrix (edgeFactors n i branch)

/-- A forward edge equals the product of the lifted source lowering operator, target raising
operator, and branch path-bit operator. See [FarhiGutmann1998]. -/
theorem forwardEdge_source_product (n : ℕ) (i : Fin n) (branch : Bool) :
    forwardEdge n i branch =
      (productMatrix (wireFactors (levelWire n i.castSucc) raising))ᴴ *
      productMatrix (wireFactors (levelWire n i.succ) raising) *
      productMatrix (wireFactors (pathWire n i) (if branch then raising else 1 - number)) := by
  rw [productMatrix_adjoint, productMatrix_mul, productMatrix_mul]
  rfl

/-- The set of the source level wire, target level wire, and path wire for an edge. -/
def edgeSupport (n : ℕ) (i : Fin n) : Finset (Fin (2 * n + 1)) :=
  {levelWire n i.castSucc, levelWire n i.succ, pathWire n i}

/-- A forward edge matrix is tensor-local on its three-wire edge support. -/
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

/-- The negative sum of both forward branch edge matrices and their conjugate transposes. -/
def hopTerm (n : ℕ) (i : Fin n) : Matrix (Reg (2 * n + 1)) (Reg (2 * n + 1)) ℂ :=
  -(forwardEdge n i false + (forwardEdge n i false)ᴴ +
    forwardEdge n i true + (forwardEdge n i true)ᴴ)

/-- The hopping term is tensor-local on an edge support of cardinality at most three. -/
theorem hopTerm_three_local (n : ℕ) (i : Fin n) :
    (edgeSupport n i).card ≤ 3 ∧ TensorLocalOn (edgeSupport n i) (hopTerm n i) := by
  refine ⟨Finset.card_le_three, ?_⟩
  have h0 := forwardEdge_local n i false
  have h1 := forwardEdge_local n i true
  have h := tensorLocalOn_add _
    (tensorLocalOn_add _ (tensorLocalOn_add _ h0 (tensorLocalOn_adjoint _ h0)) h1)
    (tensorLocalOn_adjoint _ h1)
  simpa only [neg_one_smul] using! tensorLocalOn_smul _ h (-1)

/-- Each hopping term is Hermitian. -/
theorem hopTerm_hermitian (n : ℕ) (i : Fin n) : (hopTerm n i).IsHermitian := by
  change (hopTerm n i)ᴴ = hopTerm n i
  simp only [hopTerm, Matrix.conjTranspose_neg, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose]
  abel

/-- The degree weight equal to two at level zero, one at the terminal level when distinct, and
three at other levels. -/
def degreeWeight (n : ℕ) (i : Fin (n + 1)) : ℂ :=
  if i.val = 0 then 2 else if i.val = n then 1 else 3

/-- The lifted level-bit number projector multiplied by its degree weight. -/
def degreeTerm (n : ℕ) (i : Fin (n + 1)) : Matrix (Reg (2 * n + 1)) (Reg (2 * n + 1)) ℂ :=
  degreeWeight n i • productMatrix (wireFactors (levelWire n i) number)

/-- Each degree term is tensor-local on its single level wire. -/
theorem degreeTerm_local (n : ℕ) (i : Fin (n + 1)) :
    TensorLocalOn {levelWire n i} (degreeTerm n i) := by
  apply tensorLocalOn_smul
  apply productMatrix_tensor_local
  intro j hj
  simp only [Finset.mem_singleton] at hj
  simp [wireFactors, hj]

/-- Each weighted degree term is Hermitian. -/
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

/-- The sum of the weighted degree terms and the Hermitian hopping terms. -/
def fullTreeHamiltonian (n : ℕ) : Matrix (Reg (2 * n + 1)) (Reg (2 * n + 1)) ℂ :=
  (∑ i : Fin (n + 1), degreeTerm n i) + ∑ i : Fin n, hopTerm n i

/-- The disjoint union of level indices for degree terms and edge indices for hopping terms. -/
abbrev TermIndex (n : ℕ) := Sum (Fin (n + 1)) (Fin n)

/-- The degree or hopping matrix selected by a Hamiltonian term index. -/
def term (n : ℕ) : TermIndex n → Matrix (Reg (2 * n + 1)) (Reg (2 * n + 1)) ℂ
  | .inl i => degreeTerm n i
  | .inr i => hopTerm n i

/-- Every indexed term in the tree Hamiltonian is Hermitian. See [FarhiGutmann1998]. -/
theorem term_hermitian (n : ℕ) (i : TermIndex n) : (term n i).IsHermitian := by
  cases i with
  | inl i => exact degreeTerm_hermitian n i
  | inr i => exact hopTerm_hermitian n i

/-- The full tree Hamiltonian is the sum of its indexed terms, each tensor-local on some support
of cardinality at most three. See [FarhiGutmann1998]. -/
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
