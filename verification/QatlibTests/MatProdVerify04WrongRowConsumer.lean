module

public import Qatlib.Papers.MatProdVerify04.MainResults.WrongRowWitness
public import Qatlib.Papers.MatProdVerify04.MainResults.BooleanProductFormula
import Mathlib.Tactic.FinCases

open Qatlib.Papers.MatProdVerify04.MainResults
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false

namespace QatlibTests.MatProdVerify04WrongRowConsumer

private def rowValues (i : Fin 3) : ZMod 2 := if i = 0 then 1 else 0

/-- The proposed output differs from the zero product in row zero. -/
private theorem single_mismatch (i : Fin 3) :
    (∑ l, (0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i l) ≠ rowValues i ↔ i = 0 := by
  fin_cases i <;> decide

example (i j : Fin 3) :
    ((0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Matrix.of (fun _ _ : Fin 3 => (1 : ZMod 2)))
      i j ≠ rowValues i ↔ i = 0 :=
  parity_product_wrong_row 0 rowValues 0 single_mismatch i j

example (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    x * Matrix.of (fun _ _ : Fin 3 => (1 : ZMod 2)) =
      Matrix.of (fun i (_ : Fin 3) => ∑ l, x i l) :=
  parity_product_correct x (fun i => ∑ l, x i l) (fun _ => rfl)

example : ‖wrongRowState 3 (0 : Fin 3)‖ = 1 := wrongRowState_norm 3 0

example : ‖wrongRowState 3 (0 : Fin 3) - wrongRowState 3 (1 : Fin 3)‖ ^ 2 = 2 :=
  wrongRowState_distance_sq 3 0 1 (by norm_num)

example : ‖parityErrorProjection 0 rowValues‖ = 1 :=
  wrongRow_operator_norm 0 rowValues 0 single_mismatch

example (i : Fin 3) : parityErrorProjection 0 rowValues i i = wrongRowState 3 0 i :=
  parity_error_projection_diag 0 rowValues 0 single_mismatch i

example : ∃ C : ℝ, 0 < C ∧ C ≤ ‖wrongRowState 3 0 - wrongRowState 3 1‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := wrongRowState_uniform_separation
  exact ⟨C, hC, h 3 0 1 (by decide)⟩

example (A : Matrix (Fin 2) (Fin 3) Bool) (B : Matrix (Fin 3) (Fin 2) Bool)
    (C : Matrix (Fin 2) (Fin 2) Bool) (h : booleanProductFormula A B C = true)
    (hC : C 0 1 = true) : ∃ l, A 0 l = true ∧ B l 1 = true :=
  ((boolean_product_formula_eq_true_iff A B C).mp h 0 1).mp hC

example : Fintype.card (BooleanProductTerm 2 3) = 12 := boolean_product_term_count 2 3

example : ∃ K : ℝ, 0 < K ∧ Real.sqrt (Fintype.card (BooleanProductTerm 2 3) : ℝ) ≤
    K * 2 * Real.sqrt 3 := by
  obtain ⟨K, hK, h⟩ := boolean_product_sqrt_size_bound
  exact ⟨K, hK, h 2 3 (by decide) (by decide)⟩

end QatlibTests.MatProdVerify04WrongRowConsumer
