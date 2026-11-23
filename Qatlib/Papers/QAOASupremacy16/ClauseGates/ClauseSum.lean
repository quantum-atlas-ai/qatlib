/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Data.Sym.Sym2

@[expose] public section

/-!
# Finite CSP clause costs and the diagonal MAX-CUT cost operator

Section 2.1 of [FarhiHarrow2016] presents a constraint satisfaction problem as `m` clauses
`C_a : {0,1}^n → {0,1}` (Eq. (1)) together with the cost `C(z) = ∑_a C_a(z)` that counts the
satisfied clauses (Eq. (2)). The MAX-CUT special case indexes clauses by graph edges and sets
`C_{⟨i,j⟩}(z) = (z_i - z_j)^2` (Eq. (3)). Both QAOA and the adiabatic algorithm use the diagonal
operator `C|z⟩ = C(z)|z⟩` of Eq. (4) as their cost Hamiltonian.

This module formalizes those objects for finite Boolean registers `Reg n = Fin n → Bool`. A CSP
instance is a finite family of Boolean clauses. Its cost is the cardinality of the satisfied-clause
set, and it is bounded uniformly by the number of clauses, with the bound placed outside the
quantifier over registers. A MAX-CUT instance is a loopless family of distinct undirected edges.
Its clause is satisfied exactly when the endpoint bits disagree; the cut count is invariant under
complementing every bit, distinct edges contribute at most one each, some edge is cut whenever the
edge family is nonempty, and the count agrees with the Ising form
`(1/2) ∑_{⟨i,j⟩} (1 - s_i s_j)` of Eq. (3).

The cost operator `costOperator C` is the diagonal matrix with entries `C z`. It is Hermitian and
its ℓ² operator norm is the maximal entry `max_z |C z|`; applying it to a state
vector in `EuclideanSpace ℂ (Reg n)` bounds the output `ℓ²` norm by that constant times the
input norm.

The encoding of clauses, the size of a clause, and the polynomial-time evaluation of the cost are
not formalized here; the clause index is an abstract finite type and a clause is an arbitrary
Boolean function of the register.

## Main statements

* `Qatlib.Papers.QAOASupremacy16.ClauseGates.CspInstance.totalCost_eq_card_filter`
  counts the satisfied clauses.
* `Qatlib.Papers.QAOASupremacy16.ClauseGates.CspInstance.exists_uniform_totalCost_bound`
  gives a positive uniform bound outside `∀ z`.
* `Qatlib.Papers.QAOASupremacy16.ClauseGates.MaxCutInstance.cutCost_compl`
  proves that complementing every bit preserves the cut count.
* `Qatlib.Papers.QAOASupremacy16.ClauseGates.MaxCutInstance.two_mul_cutCost_eq_ising`
  gives the Ising form of Eq. (3).
* `Qatlib.Papers.QAOASupremacy16.ClauseGates.costOperator_isHermitian`
  establishes Hermiticity of the cost operator in Eq. (4).
* `Qatlib.Papers.QAOASupremacy16.ClauseGates.costOperator_l2_opNorm`
  gives its ℓ² operator norm as `max_z |C z|`.

## References

* [Farhi and Harrow, 2016][FarhiHarrow2016]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QAOASupremacy16.ClauseGates

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {n : ℕ}

/-- A finite constraint satisfaction problem on `n`-bit registers: one Boolean clause per index.
The clause index is the paper's `[m]`, and the clause value is Eq. (1). -/
structure CspInstance (n : ℕ) (α : Type*) where
  /-- The clause indexed by `a`. -/
  clause : α → Reg n → Bool

namespace CspInstance

variable {α : Type*} [Fintype α] (I : CspInstance n α)

/-- Eq. (1): the `0/1` value of clause `a` on the register `z`. -/
def clauseValue (a : α) (z : Reg n) : ℕ :=
  if I.clause a z = true then 1 else 0

/-- Eq. (2): the cost counts the satisfied clauses. -/
def totalCost (z : Reg n) : ℕ :=
  ∑ a, I.clauseValue a z

omit [Fintype α] in
/-- Every clause contributes at most one to the cost. -/
theorem clauseValue_le_one (a : α) (z : Reg n) : I.clauseValue a z ≤ 1 := by
  unfold clauseValue
  split <;> omega

omit [Fintype α] in
/-- The clause value is one exactly on the satisfying registers. -/
theorem clauseValue_eq_one_iff (a : α) (z : Reg n) :
    I.clauseValue a z = 1 ↔ I.clause a z = true := by
  unfold clauseValue
  split <;> simp_all

/-- The cost is the cardinality of the satisfied-clause set. -/
theorem totalCost_eq_card_filter (z : Reg n) :
    I.totalCost z = (Finset.univ.filter fun a => I.clause a z = true).card := by
  simp [totalCost, clauseValue]

/-- A uniformly bounded cost, with the bound outside the register quantifier. -/
theorem totalCost_le_card (z : Reg n) : I.totalCost z ≤ Fintype.card α := by
  rw [totalCost_eq_card_filter]
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- The Eq. (2) cost admits a positive uniform bound when at least one clause exists. -/
theorem exists_uniform_totalCost_bound [Nonempty α] :
    ∃ m : ℕ, 0 < m ∧ ∀ z : Reg n, I.totalCost z ≤ m :=
  ⟨Fintype.card α, Fintype.card_pos_iff.mpr inferInstance, I.totalCost_le_card⟩

end CspInstance

/-! ## MAX-CUT instances -/

/-- A MAX-CUT instance on `n` bits: a loopless family of distinct undirected edges, with clause
`C_{⟨i,j⟩}(z) = (z_i - z_j)^2` as in Eq. (3). The injectivity field records that the index is a
set of edges, not a multiset. -/
structure MaxCutInstance (n : ℕ) (ι : Type*) where
  /-- One endpoint of the edge indexed by `a`. -/
  fst : ι → Fin n
  /-- The other endpoint of the edge indexed by `a`. -/
  snd : ι → Fin n
  /-- There are no self-loops: an edge joins two distinct vertices. -/
  loopless : ∀ a, fst a ≠ snd a
  /-- Distinct indices give distinct undirected edges. -/
  edge_injective : Function.Injective fun a => s(fst a, snd a)

namespace MaxCutInstance

variable {ι : Type*} [Fintype ι] (G : MaxCutInstance n ι)

/-- Bitwise complement of a register. -/
def registerCompl (z : Reg n) : Reg n :=
  fun i => !z i

/-- The `±1` spin encoding of a bit. -/
def spinBit (z : Reg n) (i : Fin n) : ℤ :=
  if z i then -1 else 1

/-- The undirected edge set of a MAX-CUT instance. -/
def edgeSet : Finset (Sym2 (Fin n)) :=
  Finset.univ.image fun a => s(G.fst a, G.snd a)

/-- The index type is exactly the edge set of the instance. -/
theorem card_edgeSet : G.edgeSet.card = Fintype.card ι := by
  unfold edgeSet
  rw [Finset.card_image_of_injective _ G.edge_injective]
  exact Finset.card_univ

/-- Eq. (3): the edge clause is satisfied exactly when the endpoint bits disagree. -/
def clause (a : ι) (z : Reg n) : Bool :=
  decide (z (G.fst a) ≠ z (G.snd a))

/-- The `0/1` value of the MAX-CUT edge clause. -/
def clauseValue (a : ι) (z : Reg n) : ℕ :=
  if G.clause a z = true then 1 else 0

/-- The number of cut edges of the string `z`. -/
def cutCost (z : Reg n) : ℕ :=
  ∑ a, G.clauseValue a z

omit [Fintype ι] in
/-- Disagreement of the endpoint bits is unaffected by complementing the whole register. -/
theorem clause_compl (a : ι) (z : Reg n) :
    G.clause a (registerCompl z) = G.clause a z := by
  unfold clause registerCompl
  cases h₁ : z (G.fst a) <;> cases h₂ : z (G.snd a) <;> simp_all

/-- Complementing every bit preserves the cut count. -/
theorem cutCost_compl (z : Reg n) : G.cutCost (registerCompl z) = G.cutCost z := by
  unfold cutCost clauseValue
  exact Finset.sum_congr rfl fun a _ => by rw [G.clause_compl]

omit [Fintype ι] in
/-- A single edge contributes at most one to the cut count. -/
theorem clauseValue_le_one (a : ι) (z : Reg n) : G.clauseValue a z ≤ 1 := by
  unfold clauseValue
  split <;> omega

/-- The cut count is at most the number of edges. -/
theorem cutCost_le_card (z : Reg n) : G.cutCost z ≤ Fintype.card ι := by
  unfold cutCost
  calc (∑ a, G.clauseValue a z) ≤ ∑ _a : ι, 1 :=
        Finset.sum_le_sum fun a _ => G.clauseValue_le_one a z
    _ = Fintype.card ι := by simp

/-- Any nonempty edge family can be cut by some string: take the indicator of one endpoint. -/
theorem exists_pos_cutCost [Nonempty ι] : ∃ z : Reg n, 0 < G.cutCost z := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty ι›
  refine ⟨fun i => decide (i = G.fst a₀), ?_⟩
  have hpos : G.clauseValue a₀ (fun i => decide (i = G.fst a₀)) = 1 := by
    have hne : ¬ (G.fst a₀ = G.snd a₀) := G.loopless a₀
    have hbit : (decide (G.snd a₀ = G.fst a₀)) = false := by
      simp [Ne.symm hne]
    unfold clauseValue clause
    simp [hbit]
  calc 0 < G.clauseValue a₀ (fun i => decide (i = G.fst a₀)) := by omega
    _ ≤ G.cutCost (fun i => decide (i = G.fst a₀)) :=
        Finset.single_le_sum (f := fun a => G.clauseValue a (fun i => decide (i = G.fst a₀)))
          (fun a _ => Nat.zero_le _) (Finset.mem_univ a₀)

omit [Fintype ι] in
/-- The Ising form of a single MAX-CUT clause: twice the clause value is
`1 - s_i s_j`. -/
theorem two_mul_clauseValue_eq_ising (a : ι) (z : Reg n) :
    (2 : ℤ) * (G.clauseValue a z : ℤ)
      = 1 - spinBit z (G.fst a) * spinBit z (G.snd a) := by
  unfold clauseValue clause spinBit
  cases h₁ : z (G.fst a) <;> cases h₂ : z (G.snd a) <;> simp_all

/-- Eq. (3) in Ising form: twice the cut count is the number of edges minus the sum of the
endpoint spin products. -/
theorem two_mul_cutCost_eq_ising (z : Reg n) :
    (2 : ℤ) * (G.cutCost z : ℤ)
      = (Fintype.card ι : ℤ) - ∑ a, spinBit z (G.fst a) * spinBit z (G.snd a) := by
  unfold cutCost
  push_cast
  rw [Finset.mul_sum]
  calc ∑ a, (2 : ℤ) * (G.clauseValue a z : ℤ)
      = ∑ a, (1 - spinBit z (G.fst a) * spinBit z (G.snd a)) :=
        Finset.sum_congr rfl fun a _ => G.two_mul_clauseValue_eq_ising a z
    _ = (Fintype.card ι : ℤ) - ∑ a, spinBit z (G.fst a) * spinBit z (G.snd a) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
        simp

end MaxCutInstance

/-! ## The diagonal cost operator of Eq. (4) -/

/-- Eq. (4): the diagonal cost operator `C|z⟩ = C(z)|z⟩` with real entries `C z`. -/
noncomputable def costOperator (C : Reg n → ℕ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun z => (C z : ℂ)

/-- The cost operator acts on a state by multiplying each amplitude by its cost. -/
theorem costOperator_mulVec_apply (C : Reg n → ℕ) (ψ : Reg n → ℂ) (z : Reg n) :
    (costOperator C).mulVec ψ z = (C z : ℂ) * ψ z := by
  simp [costOperator, Matrix.mulVec_diagonal]

/-- The cost operator is Hermitian, since its diagonal entries are real. -/
theorem costOperator_isHermitian (C : Reg n → ℕ) : (costOperator C).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  rw [IsSelfAdjoint, Pi.star_def]
  funext z
  simp

/-- The ℓ² operator norm of the cost operator is the maximal diagonal entry. -/
theorem costOperator_l2_opNorm (C : Reg n → ℕ) :
    ‖costOperator C‖ = ‖(fun z => (C z : ℂ))‖ := by
  exact Matrix.l2_opNorm_diagonal fun z => (C z : ℂ)

/-- The output `ℓ²` norm is at most the maximal cost times the input `ℓ²` norm. -/
theorem costOperator_mulVec_norm_le (C : Reg n → ℕ) (ψ : EuclideanSpace ℂ (Reg n)) :
    ‖(EuclideanSpace.equiv (Reg n) ℂ).symm ((costOperator C) *ᵥ ψ)‖
      ≤ ‖(fun z => (C z : ℂ))‖ * ‖ψ‖ :=
  (Matrix.l2_opNorm_mulVec (costOperator C) ψ).trans (by rw [costOperator_l2_opNorm])

end Qatlib.Papers.QAOASupremacy16.ClauseGates
