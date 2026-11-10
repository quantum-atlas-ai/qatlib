/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DecisionTrees97.MainResults.RaisingHamiltonian
import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula
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

def termEnumeration (n : ℕ) : Fin (Fintype.card (TermIndex n)) ≃ TermIndex n :=
  (Fintype.equivFin (TermIndex n)).symm

theorem source_term_count (n : ℕ) : Fintype.card (TermIndex n) = 2 * n + 1 := by
  simp only [TermIndex, Fintype.card_sum, Fintype.card_fin]
  omega

def indexedTerm (n : ℕ) (j : Fin (Fintype.card (TermIndex n))) :
    Matrix (Fin (2 ^ (2 * n + 1))) (Fin (2 ^ (2 * n + 1))) ℂ :=
  Matrix.reindex (bitVecEquiv (2 * n + 1)) (bitVecEquiv (2 * n + 1))
    (term n (termEnumeration n j))

def indexedTarget (n : ℕ) : Matrix (Fin (2 ^ (2 * n + 1))) (Fin (2 ^ (2 * n + 1))) ℂ :=
  Matrix.reindex (bitVecEquiv (2 * n + 1)) (bitVecEquiv (2 * n + 1)) (fullTreeHamiltonian n)

theorem indexedTerm_hermitian (n : ℕ) (j : Fin (Fintype.card (TermIndex n))) :
    (indexedTerm n j).IsHermitian := by
  change (indexedTerm n j)ᴴ = indexedTerm n j
  rw [indexedTerm, Matrix.conjTranspose_reindex, (term_hermitian n (termEnumeration n j)).eq]

theorem sum_indexedTerm (n : ℕ) : (∑ j, indexedTerm n j) = indexedTarget n := by
  ext x y
  simp only [indexedTerm, indexedTarget, Matrix.sum_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]
  rw [(source_sum_three_local n).1]
  simp only [Matrix.sum_apply]
  apply Fintype.sum_equiv (termEnumeration n)
  intro j
  rfl

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
