module

import Qatlib.Papers.TrotterError19.MainResults.Appendices.MonomialIntegrals
import Qatlib.Papers.TrotterError19.MainResults.Appendices.AppendixJ
import Mathlib.Tactic

/-!
# Consumer regression for the Trotter error appendices

Exercise the order rules on noncommuting two-dimensional operators and the
coefficient bounds on the fourfold commutators of a three-term Hamiltonian.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QatlibTests.TrotterError19AppendicesRegression

open Qatlib.Papers.TrotterError19.MainResults (NestedCommutator OrderCondition)
open Qatlib.Papers.TrotterError19.MainResults.Appendices (propB3_addition propB3_multiplication)
open Qatlib.Papers.TrotterError19.MainResults.Appendices
open scoped Matrix.Norms.L2Operator

/-- The Pauli X matrix. -/
private def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli Z matrix. -/
private def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The order condition for a sum of two operator-valued powers. -/
example :
    OrderCondition (fun τ : ℝ => τ ^ 2 • X + τ ^ 3 • Z) (min 2 3) :=
  propB3_addition _ _ _ _ (pow_smul_orderCondition X 2) (pow_smul_orderCondition Z 3)

/-- The order condition for a product in the spectral operator norm. -/
example :
    OrderCondition (fun τ : ℝ => (τ ^ 2 • X) * (τ ^ 3 • Z)) (2 + 3) :=
  propB3_multiplication _ _ _ _ (pow_smul_orderCondition X 2) (pow_smul_orderCondition Z 3)

/-- Exact iterated monomial integral at `p = 1`, `q = 2`, `t = 2`. -/
example :
    (∫ τ₁ in (0 : ℝ)..2, τ₁ ^ 1 * (∫ τ₂ in (0 : ℝ)..τ₁, τ₂ ^ 2)) = 32 / 15 := by
  rw [iterated_monomial_integral_eq]
  norm_num

/-- The same iterated integral satisfies a fifth-order bound near zero. -/
example :
    OrderCondition
      (fun t : ℝ => ∫ τ₁ in (0 : ℝ)..t, τ₁ ^ 1 * (∫ τ₂ in (0 : ℝ)..τ₁, τ₂ ^ 2))
      5 :=
  iterated_monomial_orderCondition 1 2

/-- Coefficients with `l ≤ m` vanish, here `(l, m) = (1, 2)` in the paper. -/
example : cTable 0 0 0 0 1 = 0 :=
  cTable_eq_zero_of_le 0 0 0 (by decide)

/-- The coefficient at a maximizing index lies in the bound and attains it. -/
example : (0 ≤ cTable 2 2 1 1 0 ∧ cTable 2 2 1 1 0 ≤ 0.0681) ∧
    cTable 2 2 1 1 0 = 0.0681 := by
  refine ⟨cTable_nonneg_and_le 2 2 1 1 0, ?_⟩
  norm_num [cTable, tableCoeff]

/-- The complete coefficient sum. -/
example : (∑ i, ∑ j, ∑ k, ∑ l, ∑ m, cTable i j k l m) = 1.8776 := cTable_sum

/-- Three Hermitian summands for the coefficient-weighted error formula. -/
private def H : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![X, Z, 1]

/-- A supported fourfold commutator equals `16 • X` and has a nonzero entry. -/
example : NestedCommutator [H 0, H 1, H 1, H 1, H 1] 0 1 = 16 := by
  norm_num [NestedCommutator, H, X, Z, Matrix.mul_apply, Fin.sum_univ_two]

/-- Apply the conditional error corollary to the same Hamiltonian and
commutator weights that occur in its hypothesis. -/
example {t M : ℝ} (ht : 0 ≤ t)
    (hw : ∀ i j k l m, tableCommutatorNorm H i j k l m ≤ M)
    (hmain : suzukiFourthThreeTermError H t ≤ t ^ 5 * ∑ i, ∑ j, ∑ k, ∑ l, ∑ m,
      cTable i j k l m * tableCommutatorNorm H i j k l m) :
    suzukiFourthThreeTermError H t ≤ 1.8776 * t ^ 5 * M :=
  suzuki_fourth_error_le_of_table_bound H ht hw hmain

end QatlibTests.TrotterError19AppendicesRegression
