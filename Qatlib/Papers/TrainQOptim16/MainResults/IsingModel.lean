/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# MAX-2-SAT instances and the Ising Hamiltonian of arXiv:1605.05370v1

Source: Wecker, Hastings, Troyer, *Training A Quantum Optimizer*,
fixed arXiv:1605.05370v1. Section II "Problem definition and ansatz", printed
p. 2, Eqs. (1) and (2).

The paper encodes a MAX-2-SAT clause `x_i ∨ x_j` (with optional negations) as
the Ising term `(1 ± σᶻ_i)(1 ± σᶻ_j)/4`: it is `0` when the clause is true and
`1` when it is false. `HZ` is the sum of these terms over all clauses, so its
eigenvalue on a computational-basis state is the number of violated clauses;
`HX = Σ_i (1 - σˣ_i)/2` is the transverse field. This module formalizes those
definitions together with the elementary facts the schedule analysis needs:

* `clausePenalty_eq_spinTerm` — the Boolean violation indicator is exactly the
  printed spin term `(1 ± σᶻ_i)(1 ± σᶻ_j)/4`;
* `energy_eq_violatedClauses` — `HZ`'s eigenvalue is the violated-clause count;
* `hzMatrix_isHermitian`, `hzMatrix_mulVec_basis` — `HZ` is the diagonal
  Hamiltonian with the printed eigenvalues;
* `hxMatrix_isHermitian` — the transverse field of Eq. (2) is Hermitian.

Boundary: these are finite-instance definitions; no claim of a ground-state
algorithm or approximation ratio is made here. The paper's numerical training
results are handled in the sibling `SourceClaims` module.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TrainQOptim16.MainResults.IsingModel

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators Matrix

/-- A MAX-2-SAT clause over `n` Boolean variables `x_0, …, x_{n-1}`. The paper
allows any of the four forms `x_i ∨ x_j`, `x_i ∨ ¬x_j`, `¬x_i ∨ x_j`,
`¬x_i ∨ ¬x_j` with distinct variables `i ≠ j` (Sec. II, p. 2). -/
structure TwoClause (n : ℕ) where
  /-- Index of the first literal. -/
  left : Fin n
  /-- Index of the second literal. -/
  right : Fin n
  /-- The two variables of a clause are distinct. -/
  distinct : left ≠ right
  /-- Whether the first literal is negated. -/
  leftNegated : Bool
  /-- Whether the second literal is negated. -/
  rightNegated : Bool

/-- The literal `i` (or its negation) is false under the assignment `σ`. -/
def literalFalse {n : ℕ} (σ : Fin n → Bool) (i : Fin n) (negated : Bool) : Bool :=
  if negated then σ i else !σ i

/-- The clause is violated, as a `0/1` penalty. -/
def clausePenalty {n : ℕ} (c : TwoClause n) (σ : Fin n → Bool) : ℕ :=
  if literalFalse σ c.left c.leftNegated && literalFalse σ c.right c.rightNegated then 1 else 0

/-- `HZ` of Eq. (1): the number of violated clauses of the instance `clauses`
under the assignment `σ`. -/
def energy {n : ℕ} (clauses : Finset (TwoClause n)) (σ : Fin n → Bool) : ℕ :=
  ∑ c ∈ clauses, clausePenalty c σ

/-- The paper's spin variable `σᶻ = +1` for true and `σᶻ = -1` for false. -/
def spinOf (b : Bool) : ℤ :=
  if b then 1 else -1

/-- The factor `(1 ± σᶻ_i)/2` of Eq. (1): the minus sign is used for a positive
literal and the plus sign for a negated one. -/
def spinFactor {n : ℕ} (σ : Fin n → Bool) (i : Fin n) (negated : Bool) : ℤ :=
  if negated then (1 + spinOf (σ i)) / 2 else (1 - spinOf (σ i)) / 2

/-- The violated-clause indicator is exactly the printed term
`(1 ± σᶻ_i)(1 ± σᶻ_j)/4` of Eq. (1). -/
theorem clausePenalty_eq_spinTerm {n : ℕ} (c : TwoClause n) (σ : Fin n → Bool) :
    (clausePenalty c σ : ℤ) =
      spinFactor σ c.left c.leftNegated * spinFactor σ c.right c.rightNegated := by
  cases h₁ : σ c.left <;> cases h₂ : σ c.right <;>
    cases hl : c.leftNegated <;> cases hr : c.rightNegated <;>
    norm_num [clausePenalty, literalFalse, spinFactor, spinOf, h₁, h₂, hl, hr]

/-- The `HZ` eigenvalue is the number of violated clauses. -/
theorem energy_eq_violatedClauses {n : ℕ} (clauses : Finset (TwoClause n))
    (σ : Fin n → Bool) :
    energy clauses σ = ∑ c ∈ clauses, clausePenalty c σ := rfl

/-- A single clause contributes at most `1` to the energy. -/
theorem clausePenalty_le_one {n : ℕ} (c : TwoClause n) (σ : Fin n → Bool) :
    clausePenalty c σ ≤ 1 := by
  unfold clausePenalty
  split <;> omega

/-- The `HZ` eigenvalue is at most the number of clauses. -/
theorem energy_le_card {n : ℕ} (clauses : Finset (TwoClause n)) (σ : Fin n → Bool) :
    energy clauses σ ≤ clauses.card := by
  unfold energy
  calc
    ∑ c ∈ clauses, clausePenalty c σ ≤ ∑ _c ∈ clauses, 1 := by
      refine Finset.sum_le_sum ?_
      intro c _
      exact clausePenalty_le_one c σ
    _ = clauses.card := by simp

/-- `HZ` of Eq. (1) as a diagonal matrix in the computational basis: the
diagonal entry at a bit string is the number of violated clauses. -/
def hzMatrix {n : ℕ} (clauses : Finset (TwoClause n)) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.diagonal fun σ => (energy clauses σ : ℂ)

/-- The MAX-2-SAT energy `HZ` is Hermitian (all entries are real diagonal). -/
theorem hzMatrix_isHermitian {n : ℕ} (clauses : Finset (TwoClause n)) :
    (hzMatrix clauses).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro σ τ
  unfold hzMatrix Matrix.diagonal
  by_cases h : τ = σ
  · simp [h]
  · have h' : σ ≠ τ := fun hc => h hc.symm
    simp [h, h']

/-- `HZ` acts diagonally: on the computational basis vector of `σ` it returns
the number of violated clauses on that same vector. -/
theorem hzMatrix_mulVec_basis {n : ℕ} (clauses : Finset (TwoClause n))
    (σ : Fin n → Bool) :
    hzMatrix clauses *ᵥ (fun τ => if τ = σ then (1 : ℂ) else 0) =
      (fun τ => if τ = σ then (energy clauses σ : ℂ) else 0) := by
  unfold hzMatrix
  ext τ
  rw [Matrix.mulVec_diagonal]
  by_cases h : τ = σ <;> simp [h]

/-- A Pauli-`X` flip of bit `i`. -/
def xFlip {n : ℕ} (i : Fin n) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  fun σ τ => if τ = Function.update σ i (!σ i) then 1 else 0

/-- The left inverse of flipping bit `i` is flipping bit `i` again. -/
theorem update_flip_flip {n : ℕ} (σ : Fin n → Bool) (i : Fin n) :
    Function.update (Function.update σ i (!σ i)) i (!(Function.update σ i (!σ i)) i) = σ := by
  rw [Function.update_self]
  cases h : σ i <;> simp [h]

/-- The single-qubit flip matrix is Hermitian (it is the permutation matrix of
an involution). -/
theorem xFlip_isHermitian {n : ℕ} (i : Fin n) : (xFlip i).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro σ τ
  unfold xFlip
  by_cases h : τ = Function.update σ i (!σ i)
  · have h' : σ = Function.update τ i (!τ i) := by
      rw [h]
      exact (update_flip_flip σ i).symm
    rw [if_pos h, if_pos h']
    simp
  · have h' : σ ≠ Function.update τ i (!τ i) := by
      intro hc
      apply h
      rw [hc]
      exact (update_flip_flip τ i).symm
    rw [if_neg h, if_neg h']
    simp

/-- `HX` of Eq. (2): the transverse field `Σ_i (1 - σˣ_i)/2`. -/
def hxMatrix {n : ℕ} : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  ∑ i : Fin n, ((1 : ℂ) / 2) • (1 - xFlip i)

/-- The transverse field of Eq. (2) is Hermitian. -/
theorem hxMatrix_isHermitian {n : ℕ} :
    (hxMatrix : Matrix (Fin n → Bool) (Fin n → Bool) ℂ).IsHermitian := by
  unfold hxMatrix
  refine Finset.sum_induction
    (fun i : Fin n => ((1 : ℂ) / 2) • (1 - xFlip i))
    (fun A => Matrix.IsHermitian A) ?_ ?_ ?_
  · intro A B hA hB
    exact hA.add hB
  · exact Matrix.isHermitian_zero
  · intro i _
    exact (Matrix.isHermitian_one.sub (xFlip_isHermitian i)).smul (by
      show IsSelfAdjoint ((1 : ℂ) / 2)
      simp [IsSelfAdjoint])

end Qatlib.Papers.TrainQOptim16.MainResults.IsingModel
