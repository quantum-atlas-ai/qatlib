/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Matrix.Mul
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Papers.Instantaneous08.MainResults.ConstantAction.Bias

@[expose] public section

/-!
# CNOT conjugation of a single ancilla Z rotation

Lemmas 7 and 8 of [ShepherdBremner2009] compile an X-gate of a row `p` out of data-to-ancilla
CNOTs and one ancilla `Z` rotation. On the data register this module uses the
index set `F2Vec n × ZMod 2` with the second coordinate as the ancilla bus. The CNOT of a data
coordinate `j` is the permutation matrix `cnotInto j` sending `(x, b)` to `(x, b + x j)`, and the
ladder `ladder p` is the product of the CNOTs over the support of `p`. Conjugating the ancilla
rotation `ancillaZ θ` by the ladder gives the diagonal matrix whose entry at `(x, 0)` is the
character multiplier `zCoeff θ (dot p x = 0)` of
`Qatlib.Papers.Instantaneous08.MainResults.ConstantAction.xGate_char`. The result is the Z-basis
diagonal gate that agrees with the X-gate on characters; the Hadamard basis change that turns it
back into the X-gate operator is not formalized here. The product is a matrix
product over the ladder; the corresponding gate list and its size are in
`Qatlib.Papers.Instantaneous08.MainResults.ZNetworkDepth`.

## Main statements

* `deltaPerm_conj_diagonal`: conjugating a diagonal matrix by a self-inverse permutation matrix
  precomposes the diagonal with the permutation.
* `ladder_eq_deltaPerm`: the ladder is the permutation matrix of the translation by `dot p x`.
* `ladder_conj_ancillaZ`: the conjugated ancilla rotation is diagonal with the translated phase.
* `rowOperator_eq_diagonal`, `rowOperator_mulVec_zero`: the row operator acts on the ancilla-zero
  sector by the character multiplier `zCoeff θ (dot p x = 0)`.

## References

* [Shepherd and Bremner, 2009][ShepherdBremner2009], Lemmas 7 and 8, Section 5.1,
  [arXiv:0809.0847](https://arxiv.org/abs/0809.0847)
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

open Matrix

namespace Qatlib.Papers.Instantaneous08.MainResults

open Qatlib.Papers.Instantaneous08.MainResults.XProgram
open Qatlib.Papers.Instantaneous08.MainResults.ConstantAction

attribute [local instance] Classical.propDecidable

/-- The data register `F₂ⁿ` together with a single ancilla bus valued in `ZMod 2`. -/
abbrev DataBus (n : ℕ) := F2Vec n × ZMod 2

/-- The permutation matrix of a self-map of the index type, with a single one in each row. -/
def deltaPerm {I : Type*} (σ : I → I) : Matrix I I ℂ :=
  Matrix.of (fun a b => if b = σ a then 1 else 0)

/-- The identity map gives the identity matrix. -/
theorem deltaPerm_id {I : Type*} [DecidableEq I] : deltaPerm (id : I → I) = 1 := by
  ext a b
  simp [deltaPerm, Matrix.one_apply, eq_comm]

/-- Permutation matrices compose contravariantly: the matrix of `σ` times the matrix of `τ` is
the matrix of `τ ∘ σ`. -/
theorem deltaPerm_mul {I : Type*} [Fintype I] [DecidableEq I] (σ τ : I → I) :
    deltaPerm σ * deltaPerm τ = deltaPerm (τ ∘ σ) := by
  ext a b
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (σ a)]
  · simp [deltaPerm]
  · intro c _ hc
    simp [deltaPerm, hc]
  · intro h
    exact absurd (Finset.mem_univ (σ a)) h

/-- Conjugating a diagonal matrix by the permutation matrix of a self-inverse map precomposes the
diagonal entries with that map. -/
theorem deltaPerm_conj_diagonal {I : Type*} [Fintype I] [DecidableEq I] (σ : I → I)
    (hσ : ∀ a, σ (σ a) = a) (f : I → ℂ) :
    deltaPerm σ * Matrix.diagonal f * deltaPerm σ =
      Matrix.diagonal (fun a => f (σ a)) := by
  ext a b
  rw [Matrix.mul_apply]
  have hinner : ∀ c, (deltaPerm σ * Matrix.diagonal f) a c =
      (if c = σ a then 1 else 0) * f c := by
    intro c
    rw [Matrix.mul_diagonal]
    simp [deltaPerm]
  have hlast : ∀ c, deltaPerm σ c b = (if b = σ c then 1 else 0) := by
    intro c
    simp [deltaPerm]
  simp only [hinner, hlast]
  rw [Finset.sum_eq_single (σ a)]
  · rw [ite_eq_left rfl, one_mul, hσ a, Matrix.diagonal_apply]
    by_cases h : a = b
    · rw [ite_eq_left h, ite_eq_left h.symm, mul_one]
    · rw [ite_eq_right h, ite_eq_right (fun hb => h hb.symm), mul_zero]
  · intro c _ hc
    simp [hc]
  · intro h
    exact absurd (Finset.mem_univ (σ a)) h

/-- The data-to-ancilla CNOT of coordinate `j`, as a self-map of the data-ancilla index set. -/
def cnotFlip {n : ℕ} (j : Fin n) (a : DataBus n) : DataBus n := (a.1, a.2 + a.1 j)

/-- The data-to-ancilla CNOT of coordinate `j`. -/
def cnotInto {n : ℕ} (j : Fin n) : Matrix (DataBus n) (DataBus n) ℂ := deltaPerm (cnotFlip j)

/-- The `Z` rotation `exp (i θ Z)` on the ancilla bus, with eigenvalue `zCoeff θ true` at
ancilla value zero. -/
def ancillaZ {n : ℕ} (θ : ℝ) : Matrix (DataBus n) (DataBus n) ℂ :=
  Matrix.diagonal (fun a => zCoeff θ (decide (a.2 = 0)))

/-- The list of data coordinates in the support of a binary row. -/
def rowEdges {n : ℕ} (p : F2Vec n) : List (Fin n) :=
  (Finset.univ.filter (fun j => p j = 1)).toList

/-- The product of the CNOTs over the support of a binary row, ordered so that the first
instruction of the corresponding gate word acts last. -/
def ladder {n : ℕ} (p : F2Vec n) : Matrix (DataBus n) (DataBus n) ℂ :=
  ((rowEdges p).map cnotInto).reverse.prod

/-- The sum of the data coordinates over the support of a row is the dot product with the row. -/
theorem rowEdges_sum_eq_dot {n : ℕ} (p a : F2Vec n) :
    ((rowEdges p).map (fun j => a j)).sum = dot p a := by
  classical
  rw [rowEdges, Finset.sum_map_toList, Finset.sum_filter]
  change (∑ j : Fin n, if p j = 1 then a j else 0) = dot p a
  simp only [dot, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rcases Qatlib.Papers.Instantaneous08.MainResults.ClassicalApprox.zmod2_eq_zero_or_one
    (p j) with h0 | h1
  · rw [h0]
    simp
  · rw [h1]
    simp

/-- A data-to-ancilla CNOT is an involution. -/
theorem cnotFlip_involutive {n : ℕ} (j : Fin n) (a : DataBus n) :
    cnotFlip j (cnotFlip j a) = a := by
  refine Prod.ext rfl ?_
  show (a.2 + a.1 j) + a.1 j = a.2
  rw [add_assoc, CharTwo.add_self_eq_zero (a.1 j), add_zero]

/-- A ladder of CNOTs is the permutation matrix of the translation that adds the sum of the
selected data coordinates to the ancilla. -/
theorem ladder_list_eq_deltaPerm {n : ℕ} (l : List (Fin n)) :
    ((l.map cnotInto).reverse.prod) =
      deltaPerm (fun a : DataBus n => (a.1, a.2 + (l.map (fun j => a.1 j)).sum)) := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.reverse_nil, List.prod_nil, List.sum_nil]
      have h : (fun a : DataBus n => (a.1, a.2 + 0)) = id := by
        funext a
        simp
      rw [h, deltaPerm_id]
  | cons j l ih =>
      have hprod : (((j :: l).map cnotInto).reverse.prod) =
          ((l.map cnotInto).reverse.prod) * cnotInto j := by
        rw [List.map_cons, List.reverse_cons, List.prod_append]
        simp
      rw [hprod, ih]
      simp only [cnotInto]
      rw [deltaPerm_mul]
      congr 1
      funext a
      simp only [Function.comp_apply, cnotFlip, List.map_cons, List.sum_cons]
      refine Prod.ext rfl ?_
      show (a.2 + (l.map (fun j => a.1 j)).sum) + a.1 j =
        a.2 + (a.1 j + (l.map (fun j => a.1 j)).sum)
      abel

/-- The ladder over the support of `p` is the permutation matrix of the translation by
`dot p x`. -/
theorem ladder_eq_deltaPerm {n : ℕ} (p : F2Vec n) :
    ladder p = deltaPerm (fun a : DataBus n => (a.1, a.2 + dot p a.1)) := by
  rw [ladder, ladder_list_eq_deltaPerm]
  congr 1
  funext a
  rw [rowEdges_sum_eq_dot]

/-- Conjugating the ancilla rotation by the ladder gives the diagonal rotation whose eigenvalue
at `(x, b)` is `zCoeff θ (b + dot p x = 0)`. -/
theorem ladder_conj_ancillaZ {n : ℕ} (p : F2Vec n) (θ : ℝ) :
    ladder p * ancillaZ θ * ladder p =
      Matrix.diagonal (fun a : DataBus n =>
        zCoeff θ (decide (a.2 + ((rowEdges p).map (fun j => a.1 j)).sum = 0))) := by
  have hτ : ∀ a : DataBus n,
      (fun b : DataBus n => (b.1, b.2 + dot p b.1))
        ((fun b : DataBus n => (b.1, b.2 + dot p b.1)) a) = a := by
    intro a
    refine Prod.ext rfl ?_
    show (a.2 + dot p a.1) + dot p a.1 = a.2
    rw [add_assoc, CharTwo.add_self_eq_zero (dot p a.1), add_zero]
  have h := deltaPerm_conj_diagonal (σ := fun b : DataBus n => (b.1, b.2 + dot p b.1)) hτ
    (fun b : DataBus n => zCoeff θ (decide (b.2 = 0)))
  rw [ladder_eq_deltaPerm, ancillaZ, h]
  congr 1
  funext a
  rw [rowEdges_sum_eq_dot]

/-- The row operator: propagate the support of `p` to the ancilla, rotate the ancilla, and
propagate back. -/
def rowOperator {n : ℕ} (p : F2Vec n) (θ : ℝ) : Matrix (DataBus n) (DataBus n) ℂ :=
  ladder p * ancillaZ θ * ladder p

/-- The row operator is diagonal in the data-ancilla basis. -/
theorem rowOperator_eq_diagonal {n : ℕ} (p : F2Vec n) (θ : ℝ) :
    rowOperator p θ =
      Matrix.diagonal (fun a : DataBus n => zCoeff θ (decide (a.2 + dot p a.1 = 0))) := by
  rw [rowOperator, ladder_conj_ancillaZ]
  congr 1
  funext a
  rw [rowEdges_sum_eq_dot]

/-- On the ancilla-zero sector the row operator multiplies by the character multiplier
`zCoeff θ (dot p x = 0)` used by
`Qatlib.Papers.Instantaneous08.MainResults.ConstantAction.circuitOp_char`. -/
theorem rowOperator_mulVec_zero {n : ℕ} (p : F2Vec n) (θ : ℝ) (ψ : DataBus n → ℂ)
    (x : F2Vec n) :
    (rowOperator p θ *ᵥ ψ) (x, 0) = zCoeff θ (decide (dot p x = 0)) * ψ (x, 0) := by
  rw [rowOperator_eq_diagonal, Matrix.mulVec_diagonal]
  simp

end Qatlib.Papers.Instantaneous08.MainResults
