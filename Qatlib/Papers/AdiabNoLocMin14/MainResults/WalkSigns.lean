/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabNoLocMin14.MainResults.SourceMainResults
public import Mathlib.Tactic.Positivity

@[expose] public section


/-! # The missing sign conditions in the ground-state walk
Row sums alone do not certify transition probabilities. The shifted-potential
and negative-energy hypotheses below give the required entrywise signs.
-/
set_option autoImplicit false
namespace Qatlib.Papers.AdiabNoLocMin14.MainResults
open Qatlib.Papers.AdiabNoLocMin14.MainResults
open scoped BigOperators

/-- The source similarity transform has nonnegative entries under its sign conditions. -/
theorem walkNonneg {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (W ψ : V → ℝ) (E : ℝ)
    (hdiag : ∀ x, (G.degree x : ℝ) + W x ≤ 0)
    (hpos : ∀ x, 0 < ψ x) (hE : E < 0) (x y : V) :
    0 ≤ walkMatrix G W ψ E x y := by
  have hentry : hamiltonian G W x y ≤ 0 := by
    rw [hamiltonian_apply]
    split_ifs with hxy hadj
    · exact hdiag x
    · norm_num
    · exact le_rfl
  exact div_nonneg_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hentry (hpos y).le)
    (mul_nonpos_of_nonpos_of_nonneg hE.le (hpos x).le)

/-- A positive eigenstate gives both stochastic conditions, with the source sign assumptions. -/
theorem walkStochastic {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (W ψ : V → ℝ) (E : ℝ)
    (hdiag : ∀ x, (G.degree x : ℝ) + W x ≤ 0)
    (hpos : ∀ x, 0 < ψ x) (hE : E < 0) (heig : IsEigenstate G W ψ E) :
    (∀ x y, 0 ≤ walkMatrix G W ψ E x y) ∧
      (∀ x, ∑ y, walkMatrix G W ψ E x y = 1) :=
  ⟨walkNonneg G W ψ E hdiag hpos hE,
    walkMatrix_row_sum G heig hpos (ne_of_lt hE)⟩

end Qatlib.Papers.AdiabNoLocMin14.MainResults
