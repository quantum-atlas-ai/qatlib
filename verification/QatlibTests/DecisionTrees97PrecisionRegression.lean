module

public import Qatlib.Papers.DecisionTrees97.MainResults.ProductPrecision
public import Qatlib.Foundations.PureStateMath.Qubit

@[expose] public section

/-!
# Consumer regression for the DecisionTrees97 product-formula precision increment

The concrete instance is the smallest non-degenerate tree family, `n = 1`, whose encoded
register has `2 ^ (2 * 1 + 1) = 8` basis states. The state `|0⟩` on those eight basis states is
normalized, so the `EuclideanSpace` norm in `actual_state_error` and `actual_state_precision` is
the genuine Hilbert-space norm rather than a coordinate supremum. The examples invoke the
uniform precision budget and both state-level statements on this instance.
-/

set_option autoImplicit false

open Qatlib.Papers.DecisionTrees97.MainResults
open Qatlib.Papers.DecisionTrees97.MainResults.ActualProductFormula
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Matrix
open scoped Matrix.Norms.L2Operator

namespace Tests.DecisionTrees97PrecisionRegression

/-- The uniform precision theorem at `n = 1`, time `1`, and precision `1 / 4` supplies a
positive segment count with the segment budget, unitarity, exact word length, and operator
error at most `1 / 4`. -/
example :
    ∃ C : ℝ, 0 < C ∧
      ∃ r : ℕ, 0 < r ∧
        (r : ℝ) ≤ C * ((1 : ℝ) ^ 2 * pfCommutatorSum (indexedTerm 1) / (1 / 4) + 1) ∧
        pfFamily (indexedTerm 1) 1 r ∈ Matrix.unitaryGroup (Fin (2 ^ (2 * 1 + 1))) ℂ ∧
        (pfFamilyWord (indexedTerm 1) 1 r).length = (2 * 1 + 1) * r ∧
        ‖pfFamily (indexedTerm 1) 1 r - HamiltonianEvolution (indexedTarget 1) 1‖ ≤ 1 / 4 := by
  obtain ⟨C, hC, h⟩ := actual_word_precision_uniform
  exact ⟨C, hC, h 1 (by norm_num) 1 (1 / 4) (by norm_num)⟩

/-- The Euclidean state-level error inherits the operator estimate for the concrete `n = 1`
instance and the normalized basis state `|0⟩`. -/
example (r : ℕ) (hr : 0 < r) :
    ‖toEuclidean_fromVec
        (ApplyGate (pfFamily (indexedTerm 1) 1 r) (Ket (0 : Fin 8))) -
      toEuclidean_fromVec
        (ApplyGate (HamiltonianEvolution (indexedTarget 1) 1) (Ket (0 : Fin 8)))‖ ≤
      1 ^ 2 / (2 * (r : ℝ)) * pfCommutatorSum (indexedTerm 1) :=
  actual_state_error 1 r 1 hr (Ket (0 : Fin 8)) (normalized_ket 0)

/-- The state-level precision theorem is invoked at `n = 1` on the normalized state `|0⟩`. -/
example :
    ∃ r : ℕ, 0 < r ∧
      ‖toEuclidean_fromVec
          (ApplyGate (pfFamily (indexedTerm 1) 1 r) (Ket (0 : Fin 8))) -
        toEuclidean_fromVec
          (ApplyGate (HamiltonianEvolution (indexedTarget 1) 1) (Ket (0 : Fin 8)))‖ ≤ 1 / 4 :=
  actual_state_precision 1 (by norm_num) 1 (1 / 4) (by norm_num) (Ket (0 : Fin 8))
    (normalized_ket 0)

end Tests.DecisionTrees97PrecisionRegression
