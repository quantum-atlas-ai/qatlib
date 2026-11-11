/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# AdiabaticNP01 — Exact Cover instance model and the diagonal Hamiltonian `H_P`

Source: E. Farhi, J. Goldstone, S. Gutmann, J. Lapan, A. Lundgren, D. Preda,
*"A Quantum Adiabatic Evolution Algorithm Applied to Random Instances of an
NP-Complete Problem"*, arXiv:quant-ph/0104129 (fixed version: the 2001 arXiv v1,
which is the only version; PDF `quant-ph_0104129.pdf`), §2–§3 and §11.

This file fixes the combinatorial vocabulary of the paper:

* an `ExactCoverInstance n` is a finite set of three-bit clauses over `n` bits;
* `violationCount I z` is the classical energy `h(z)` of Eqs. (5)–(6): the number
  of clauses violated by the assignment `z`;
* `minViolation I` is `min_z h(z)`;
* `hamiltonian I` is the operator `H_P` of §2, diagonal in the `z` basis with
  eigenvalue `h(z)`, and `stateEnergy I ψ` is `⟨ψ|H_P|ψ⟩` for a real amplitude
  vector `ψ` (the model is real because `H_P` is real diagonal).

The ground-state and measurement statements that formalise Claim `c002` are in
`SourceGroundState.lean`; the running-time statements for Claim `c001` are in
`SourceQuadraticRuntime.lean`, and the repetition/amplification argument of §10
is in `SourceRepetition.lean`.

No `sorry`, no `admit`, no additional axioms.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticNP01.MainResults

/-- Bit assignments on `n` bits: the basis `z₁z₂…zₙ` of Eq. (2), p. 4. -/
abbrev Bitstring (n : ℕ) := Fin n → Bool

/-- An instance of Exact Cover over `n` bits: a finite family of clauses, each of
which contains exactly three bits.  This is the instance format of §2 and §8
(arXiv:quant-ph/0104129v1, pp. 4 and 7). -/
structure ExactCoverInstance (n : ℕ) where
  /-- The clauses of the instance. -/
  clauses : Finset (Finset (Fin n))
  /-- Every clause involves exactly three bits ("Exact Cover" is a restriction of
  3-SAT in which each clause contains three bits, §1, p. 2 and §8, p. 7). -/
  clause_card : ∀ C ∈ clauses, C.card = 3

variable {n : ℕ}

/-- The clause `C` is *satisfied* by the assignment `z` exactly when exactly one
bit of `C` is set to `1` — the Exact Cover condition behind Eq. (5), p. 4. -/
def exactlyOneTrue (z : Bitstring n) (C : Finset (Fin n)) : Prop :=
  (C.filter fun i => z i = true).card = 1

/-- Exact satisfaction of a finite clause is decidable. -/
instance (z : Bitstring n) (C : Finset (Fin n)) : Decidable (exactlyOneTrue z C) :=
  inferInstanceAs (Decidable (_ = 1))

/-- The classical energy cost `h(z)` of Eqs. (5)–(6), p. 4: the number of clauses
of `I` violated by `z`.  A clause costs `1` when violated and `0` when satisfied. -/
def ExactCoverInstance.violationCount (I : ExactCoverInstance n) (z : Bitstring n) : ℕ :=
  (I.clauses.filter fun C => ¬ exactlyOneTrue z C).card

/-- `min_z h(z)`: the minimum number of violated clauses, the ground-state energy
of `H_P` (§11, p. 9). -/
def ExactCoverInstance.minViolation (I : ExactCoverInstance n) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun z : Bitstring n => I.violationCount z)

/-- `z` is a minimum-violation assignment: `h(z) = min_z h(z)`.  These are exactly
the assignments the quantum algorithm is meant to output on unsatisfiable
instances (§11, p. 9). -/
def ExactCoverInstance.IsMinViolation (I : ExactCoverInstance n) (z : Bitstring n) : Prop :=
  I.violationCount z = I.minViolation

/-- Minimum violation among finitely many bitstrings is decidable. -/
instance (I : ExactCoverInstance n) (z : Bitstring n) : Decidable (I.IsMinViolation z) :=
  inferInstanceAs (Decidable (I.violationCount z = I.minViolation))

/-- The minimum-violation predicate is decidable on all assignments. -/
instance (I : ExactCoverInstance n) : DecidablePred (fun z : Bitstring n => I.IsMinViolation z) :=
  fun z => inferInstanceAs (Decidable (I.IsMinViolation z))

/-- Every assignment violates at least `minViolation I` clauses. -/
theorem minViolation_le (I : ExactCoverInstance n) (z : Bitstring n) :
    I.minViolation ≤ I.violationCount z :=
  Finset.inf'_le _ (Finset.mem_univ z)

/-- A minimum-violation assignment always exists (the assignment space is finite
and nonempty): the minimum in `minViolation` is attained. -/
theorem exists_isMinViolation (I : ExactCoverInstance n) :
    ∃ z : Bitstring n, I.IsMinViolation z := by
  obtain ⟨z, _, hz⟩ :=
    Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Bitstring n)))
      Finset.univ_nonempty (fun z => I.violationCount z)
  exact ⟨z, hz.symm⟩

/-- `h(z) = 0` iff every clause is satisfied, i.e. `z` is a satisfying assignment
of the Exact Cover instance (Eq. (6), p. 4). -/
theorem violationCount_eq_zero_iff (I : ExactCoverInstance n) (z : Bitstring n) :
    I.violationCount z = 0 ↔ ∀ C ∈ I.clauses, exactlyOneTrue z C := by
  simp only [ExactCoverInstance.violationCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    not_not]

/-- An instance has a satisfying assignment iff its minimum violation count is
zero.  This is the semantic link used by §11 (p. 9): on satisfiable instances the
minimisation problem is the original USA problem, while on unsatisfiable ones the
minimum-violation assignments are the best possible outputs. -/
theorem exists_satisfying_iff_minViolation_eq_zero (I : ExactCoverInstance n) :
    (∃ z : Bitstring n, I.violationCount z = 0) ↔ I.minViolation = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    have hle := minViolation_le I z
    omega
  · intro hmin
    obtain ⟨z, hz⟩ := exists_isMinViolation I
    exact ⟨z, by rw [hz, hmin]⟩

/-- A minimiser of a satisfiable instance is a satisfying assignment. -/
theorem satisfies_of_minViolation_eq_zero (I : ExactCoverInstance n)
    (hmin : I.minViolation = 0) (z : Bitstring n) (hz : I.IsMinViolation z) :
    ∀ C ∈ I.clauses, exactlyOneTrue z C := by
  rw [← violationCount_eq_zero_iff]
  unfold ExactCoverInstance.IsMinViolation at hz
  rw [hz, hmin]

/-- `H_P`, the final Hamiltonian of §2, p. 4: diagonal in the `z` basis with
eigenvalue `h(z)` on the basis vector `z` (Eqs. (5)–(6)). -/
def ExactCoverInstance.hamiltonian (I : ExactCoverInstance n) : Matrix (Bitstring n) (Bitstring n) ℝ :=
  Matrix.diagonal (fun z => (I.violationCount z : ℝ))

/-- The diagonal entries of `H_P` are the classical energies `h(z)`. -/
@[simp]
theorem hamiltonian_apply (I : ExactCoverInstance n) (z : Bitstring n) :
    I.hamiltonian z z = (I.violationCount z : ℝ) := by
  simp [ExactCoverInstance.hamiltonian]

/-- The expectation `⟨ψ|H_P|ψ⟩` of the diagonal Hamiltonian on a real amplitude
vector `ψ`.  Because `H_P` is diagonal this is `∑_z ψ(z)² h(z)`. -/
def ExactCoverInstance.stateEnergy (I : ExactCoverInstance n) (ψ : Bitstring n → ℝ) : ℝ :=
  ∑ z, ψ z ^ 2 * (I.violationCount z : ℝ)

/-- `stateEnergy` is the matrix expectation `⟨ψ|H_P|ψ⟩`. -/
theorem stateEnergy_eq_dotProduct (I : ExactCoverInstance n) (ψ : Bitstring n → ℝ) :
    dotProduct ψ (I.hamiltonian.mulVec ψ) = I.stateEnergy ψ := by
  have hmv : I.hamiltonian.mulVec ψ
      = fun z => (I.violationCount z : ℝ) * ψ z := by
    funext z
    simp [ExactCoverInstance.hamiltonian, Matrix.mulVec_diagonal]
  rw [hmv]
  simp only [dotProduct, ExactCoverInstance.stateEnergy]
  apply Finset.sum_congr rfl
  intro z _
  ring

end Qatlib.Papers.AdiabaticNP01.MainResults
