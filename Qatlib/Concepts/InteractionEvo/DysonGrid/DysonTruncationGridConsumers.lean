/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.DysonGrid.DysonTruncationGrid

/-!
# State error and grid budgets for Dyson products

This module transfers the Dyson grid operator estimate to an error bound on every input vector.
`dysonGridBudget` chooses a positive grid from a real error coefficient and tolerance, with
`dysonGridBudget_error` proving the resulting scalar bound. The simulation context is the
truncated Dyson framework of [LowWiebe2018].

## Main statements

* `dyson_grid_same_output_precision_consumer`: vector error at the supplied operator precision.
* `dysonGridBudget_error`: positivity and accuracy of the ceiling-based grid budget.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.DysonGrid
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- If the bounded Hermitian Lipschitz grid estimate is at most `ε`, applying the grid to any
input vector has Euclidean error at most `ε` times its norm. This transfers the grid
estimate in the setting of [LowWiebe2018] to states. -/
theorem dyson_grid_same_output_precision_consumer :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (H : ℝ → Matrix I I ℂ)
      (t Λ L ε : ℝ) (M : ℕ), Continuous H → 0 ≤ t → 0 ≤ Λ → 0 ≤ L → 0 < ε →
      0 < M → Real.exp (Λ * t) * (Λ ^ 2 + L) * t ^ 2 / (2 * M) ≤ ε →
      (∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ) →
      (∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t, ‖H u - H v‖ ≤ L * |u - v|) →
      ∀ ψ : I → ℂ,
        ‖toEuclidean_fromVec ((dysonGridRun H t M).mulVec ψ) -
          toEuclidean_fromVec ((orderedEvolution (fun u => Complex.I • H u) 0 t).mulVec ψ)‖ ≤
          ε * ‖toEuclidean_fromVec ψ‖ := by
  intro I _ _ H t Λ L ε M hH ht hΛ hL _hε hM hbudget hbound hLip ψ
  have herr := (dyson_sorted_grid_actual_error_and_cost I H t Λ L M hH ht hΛ hL
    hM hbound hLip).1
  have h := (Matrix.l2_opNorm_mulVec
    (dysonGridRun H t M - orderedEvolution (fun u => Complex.I • H u) 0 t)
    (toEuclidean_fromVec ψ)).trans
    (mul_le_mul_of_nonneg_right (herr.trans hbudget) (norm_nonneg _))
  simpa only [Matrix.sub_mulVec] using! h

/-- Choose `max 1 ⌈C / (2 ε)⌉₊` as the grid size for coefficient `C` and tolerance `ε`. -/
noncomputable def dysonGridBudget (C ε : ℝ) : ℕ := max 1 ⌈C / (2 * ε)⌉₊

/-- For nonnegative `C` and positive `ε`, the chosen grid is positive and satisfies `C / (2 M) ≤
ε`. -/
theorem dysonGridBudget_error (C ε : ℝ) (_hC : 0 ≤ C) (hε : 0 < ε) :
    0 < dysonGridBudget C ε ∧ C / (2 * (dysonGridBudget C ε : ℝ)) ≤ ε := by
  have hpos : 0 < dysonGridBudget C ε := by
    exact lt_of_lt_of_le (by omega : 0 < (1 : ℕ)) (le_max_left _ _)
  refine ⟨hpos, ?_⟩
  have hceil : C / (2 * ε) ≤ (⌈C / (2 * ε)⌉₊ : ℝ) := Nat.le_ceil _
  have hle : (⌈C / (2 * ε)⌉₊ : ℝ) ≤ (dysonGridBudget C ε : ℝ) := by
    exact_mod_cast le_max_right 1 ⌈C / (2 * ε)⌉₊
  have hh := (div_le_iff₀ (by positivity : 0 < 2 * ε)).mp (hceil.trans hle)
  apply (div_le_iff₀ (by positivity : 0 < 2 * (dysonGridBudget C ε : ℝ))).mpr
  nlinarith

end Qatlib.Concepts.InteractionEvo.DysonGrid
