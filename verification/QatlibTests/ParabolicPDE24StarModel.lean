module

public import Qatlib.Papers.ParabolicPDE24.Resources.StarModel

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Papers.ParabolicPDE24.Resources
open scoped BigOperators Matrix.Norms.L2Operator

namespace QatlibTests.ParabolicPDE24StarModel

/-- The center and three leaves give an operator norm of exactly `√3`. -/
theorem star_three_norm_eq : ‖starTransition 3‖ = Real.sqrt 3 :=
  starTransition_norm_eq 3

/-- The non-degenerate three-direction model has star coupling norm between `√3` and `3`. -/
theorem star_three_norm_bounds :
    Real.sqrt 3 ≤ ‖starTransition 3‖ ∧ ‖starTransition 3‖ ≤ 3 :=
  starTransition_norm_bounds (by norm_num)

/-- The same non-degenerate three-direction instance uses four internal levels and six oriented
star transition entries. -/
theorem star_three_resource_count :
    Fintype.card (Fin 1 ⊕ Fin 3) = 3 + 1 ∧
      ∑ i, ∑ j, (if starTransition 3 i j ≠ 0 then (1 : ℕ) else 0) = 2 * 3 :=
  starTransition_resource_count 3

/-- The dimension-uniform linear bound applies to the concrete three-direction model. -/
theorem star_three_uniform_consumer :
    ∃ C > (0 : ℝ), ‖starTransition 3‖ ≤ C * (3 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := starTransition_norm_le_uniform
  exact ⟨C, hC, hbound 3 (by norm_num)⟩

end QatlibTests.ParabolicPDE24StarModel
