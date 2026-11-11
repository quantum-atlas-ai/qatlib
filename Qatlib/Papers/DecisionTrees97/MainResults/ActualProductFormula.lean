/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DecisionTrees97.MainResults.RaisingHamiltonian
import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula

/-!
# Indexed product formula for the tree Hamiltonian

This module reindexes the local tree Hamiltonian terms by finite ordinals and converts their
register basis to a finite matrix basis. It proves that the resulting product formula is
unitary, has the stated word length, and satisfies a commutator error bound.

These constructions accompany the results of [FarhiGutmann1998].

## Main statements

* `source_term_count`: counts the Hamiltonian terms as `2 * n + 1`.
* `sum_indexedTerm`: identifies the sum of indexed terms with the indexed Hamiltonian.
* `actual_word_and_error`: collects unitarity, word length, and approximation error.

## References

* [Farhi and Gutmann, 1998][FarhiGutmann1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.LieStrang
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.DecisionTrees97.MainResults.ActualProductFormula

open RaisingHamiltonian

/-- An equivalence enumerating `TermIndex n` by the finite ordinal of its cardinality. -/
def termEnumeration (n : ℕ) : Fin (Fintype.card (TermIndex n)) ≃ TermIndex n :=
  (Fintype.equivFin (TermIndex n)).symm

/-- The tree Hamiltonian decomposition has `2 * n + 1` terms. -/
theorem source_term_count (n : ℕ) : Fintype.card (TermIndex n) = 2 * n + 1 := by
  simp only [TermIndex, Fintype.card_sum, Fintype.card_fin]
  omega

/-- A tree Hamiltonian term enumerated by a finite ordinal and reindexed in the finite
bit-vector basis. -/
def indexedTerm (n : ℕ) (j : Fin (Fintype.card (TermIndex n))) :
    Matrix (Fin (2 ^ (2 * n + 1))) (Fin (2 ^ (2 * n + 1))) ℂ :=
  Matrix.reindex (bitVecEquiv (2 * n + 1)) (bitVecEquiv (2 * n + 1))
    (term n (termEnumeration n j))

/-- The full tree Hamiltonian reindexed in the finite bit-vector basis. -/
def indexedTarget (n : ℕ) : Matrix (Fin (2 ^ (2 * n + 1))) (Fin (2 ^ (2 * n + 1))) ℂ :=
  Matrix.reindex (bitVecEquiv (2 * n + 1)) (bitVecEquiv (2 * n + 1)) (fullTreeHamiltonian n)

/-- Every indexed tree Hamiltonian term is Hermitian. -/
theorem indexedTerm_hermitian (n : ℕ) (j : Fin (Fintype.card (TermIndex n))) :
    (indexedTerm n j).IsHermitian := by
  change (indexedTerm n j)ᴴ = indexedTerm n j
  rw [indexedTerm, Matrix.conjTranspose_reindex, (term_hermitian n (termEnumeration n j)).eq]

/-- The sum of the indexed terms equals the indexed full tree Hamiltonian. -/
theorem sum_indexedTerm (n : ℕ) : (∑ j, indexedTerm n j) = indexedTarget n := by
  ext x y
  simp only [indexedTerm, indexedTarget, Matrix.sum_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]
  rw [(source_sum_three_local n).1]
  simp only [Matrix.sum_apply]
  apply Fintype.sum_equiv (termEnumeration n)
  intro j
  rfl

/-- For a positive number of repetitions, the indexed product formula is unitary, has word
length `(2 * n + 1) * r`, and has error at most `t ^ 2 / (2 * r)` times the commutator sum.
See [FarhiGutmann1998]. -/
theorem actual_word_and_error (n r : ℕ) (t : ℝ) (hr : 0 < r) :
    pfFamily (indexedTerm n) t r ∈ Matrix.unitaryGroup (Fin (2 ^ (2 * n + 1))) ℂ ∧
      (pfFamilyWord (indexedTerm n) t r).length = (2 * n + 1) * r ∧
      ‖pfFamily (indexedTerm n) t r - HamiltonianEvolution (indexedTarget n) t‖ ≤
        t ^ 2 / (2 * r) * pfCommutatorSum (indexedTerm n) := by
  have hw := product_formula_actual_word_and_tariffs (2 ^ (2 * n + 1))
    (Fintype.card (TermIndex n)) r (indexedTerm n) t (fun _ => 1) (indexedTerm_hermitian n)
  have he := product_formula_finite_family_segmented (2 ^ (2 * n + 1))
    (Fintype.card (TermIndex n)) r (indexedTerm n) t hr (indexedTerm_hermitian n)
  rw [sum_indexedTerm] at he
  exact ⟨hw.1, by rw [hw.2.1, source_term_count], he⟩

end Qatlib.Papers.DecisionTrees97.MainResults.ActualProductFormula
