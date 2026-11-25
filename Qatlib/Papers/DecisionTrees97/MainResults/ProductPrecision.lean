/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DecisionTrees97.MainResults.ActualProductFormula
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic

@[expose] public section

/-!
# Precision-driven product-formula depth for the tree Hamiltonian

For the indexed branching-tree Hamiltonian of [FarhiGutmann1998], §IV, the theorem
`Qatlib.Papers.DecisionTrees97.MainResults.ActualProductFormula.actual_word_and_error`
bounds the Lie-product error by `t ^ 2 / (2 * r) * pfCommutatorSum`, where `r` is the number of
repetition segments.
That bound is stated with `r` supplied by the caller, so it does not yet say that a *desired*
target precision can be met by choosing `r`. This module closes that arithmetic gap for the
concrete `(2 * n + 1)`-term tree family.

The two main statements separate the two roles of the product formula:

* `actual_word_precision_uniform` chooses, for every size, time and precision, a positive segment
  count whose operator error is at most the requested precision. A single uniform constant
  `C = 2` controls that count outside all universal quantifiers; no asymptotic notation and no
  dimension-dependent constant is used.
* `actual_state_error` transfers the operator estimate to normalized `EuclideanSpace` states.
  The matrix ℓ² operator norm agrees with the norm of its action as a continuous linear map on
  those states.

The Lean bound leaves `pfCommutatorSum` symbolic. For the full grouped tree family
with `n ≥ 1`, an analytic evaluation gives `K = (6n - 3)√2 + 2(n - 1)`: incident
degree and hop terms contribute `(6n - 3)√2`, and the `n - 1` adjacent hop pairs
contribute `2` each. All other commutators vanish.

For example, at `n = 2`, `t = 1`, and tolerance `1/4`, the bound certifies `r = 30`
segments, or `150` grouped local exponentials. This is not a native gate count.
The commutator evaluation is not formalized here. Neither valid-node invariance
nor a native implementation of the exponentials is asserted by the Lean results.

## References

* [Farhi and Gutmann, 1998][FarhiGutmann1998]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Papers.DecisionTrees97.MainResults.ActualProductFormula
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.BornBridge
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.DecisionTrees97.MainResults

/-- The pairwise commutator sum of a finite matrix family is nonnegative. -/
private theorem pfCommutatorSum_nonneg {D m : ℕ} (H : Fin m → Operator D) :
    0 ≤ pfCommutatorSum H := by
  unfold pfCommutatorSum
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro k _
  split_ifs with h
  · exact norm_nonneg _
  · exact le_refl 0

/-- One positive segment count meets both the budget and the scalar commutator error bound. -/
private theorem exists_segment_budget_and_error_le
    (n : ℕ) (t ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧
      (r : ℝ) ≤ 2 * (t ^ 2 * pfCommutatorSum (indexedTerm n) / ε + 1) ∧
      t ^ 2 / (2 * (r : ℝ)) * pfCommutatorSum (indexedTerm n) ≤ ε := by
  have hK : 0 ≤ pfCommutatorSum (indexedTerm n) := pfCommutatorSum_nonneg _
  have hden : 0 < 2 * ε := by positivity
  set x : ℝ := t ^ 2 * pfCommutatorSum (indexedTerm n) / (2 * ε) with hx
  have hx0 : 0 ≤ x := by
    rw [hx]
    exact div_nonneg (mul_nonneg (sq_nonneg t) hK) hden.le
  set r : ℕ := ⌊x⌋₊ + 2 with hr
  have hrpos : 0 < r := by
    rw [hr]
    exact Nat.succ_pos _
  have hxr : x ≤ (r : ℝ) := by
    have hlt : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
    have hcast : (r : ℝ) = ((⌊x⌋₊ : ℕ) : ℝ) + 2 := by
      rw [hr]; push_cast; ring
    rw [hcast]; linarith
  have hrub : (r : ℝ) ≤ x + 2 := by
    have hfl : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
    have hcast : (r : ℝ) = ((⌊x⌋₊ : ℕ) : ℝ) + 2 := by
      rw [hr]; push_cast; ring
    rw [hcast]; linarith
  have hxr' : t ^ 2 * pfCommutatorSum (indexedTerm n) ≤ (r : ℝ) * (2 * ε) := by
    have h := (div_le_iff₀ hden).mp hxr
    exact h
  have hgoal : t ^ 2 / (2 * (r : ℝ)) * pfCommutatorSum (indexedTerm n) ≤ ε := by
    have hr2 : (0 : ℝ) < 2 * (r : ℝ) := by
      have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpos
      positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hr2]
    have hsplit : (r : ℝ) * (2 * ε) = ε * (2 * (r : ℝ)) := by ring
    linarith
  have hbudget : (r : ℝ) ≤ 2 * (t ^ 2 * pfCommutatorSum (indexedTerm n) / ε + 1) := by
    have hxle : x ≤ t ^ 2 * pfCommutatorSum (indexedTerm n) / ε := by
      rw [hx]
      have hnum : 0 ≤ t ^ 2 * pfCommutatorSum (indexedTerm n) :=
        mul_nonneg (sq_nonneg t) hK
      calc t ^ 2 * pfCommutatorSum (indexedTerm n) / (2 * ε)
          ≤ t ^ 2 * pfCommutatorSum (indexedTerm n) / ε := by
            apply div_le_div_of_nonneg_left hnum (by positivity) (by linarith)
        _ = t ^ 2 * pfCommutatorSum (indexedTerm n) / ε := rfl
    have hnonneg : 0 ≤ t ^ 2 * pfCommutatorSum (indexedTerm n) / ε :=
      div_nonneg (mul_nonneg (sq_nonneg t) hK) hε.le
    linarith
  exact ⟨r, hrpos, hbudget, hgoal⟩

/-- For the indexed tree Hamiltonian, every size `0 < n`, time `t`, and target precision `ε > 0`
yield a positive segment count `r` whose product formula is unitary, has word length
`(2 * n + 1) * r`, and has operator error at most `ε`. One uniform constant, witnessed by `2`,
bounds `r` by `C * (t ^ 2 * pfCommutatorSum / ε + 1)` for all sizes, times, and precisions. -/
theorem actual_word_precision_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (_ : 0 < n) (t ε : ℝ), 0 < ε →
        ∃ r : ℕ, 0 < r ∧
          (r : ℝ) ≤ C *
              (t ^ 2 * pfCommutatorSum (indexedTerm n) / ε + 1) ∧
          pfFamily (indexedTerm n) t r ∈ Matrix.unitaryGroup (Fin (2 ^ (2 * n + 1))) ℂ ∧
          (pfFamilyWord (indexedTerm n) t r).length = (2 * n + 1) * r ∧
          ‖pfFamily (indexedTerm n) t r - HamiltonianEvolution (indexedTarget n) t‖ ≤ ε := by
  refine ⟨2, by norm_num, ?_⟩
  intro n _hn t ε hε
  obtain ⟨r, hrpos, hbudget, hgoal⟩ := exists_segment_budget_and_error_le n t ε hε
  obtain ⟨huni, hlen, herr⟩ := actual_word_and_error n r t hrpos
  exact ⟨r, hrpos, hbudget, huni, hlen, herr.trans hgoal⟩

/-- The state-level error of the indexed tree product formula in the `EuclideanSpace` norm
inherits the matrix ℓ² operator estimate of
`Qatlib.Papers.DecisionTrees97.MainResults.ActualProductFormula.actual_word_and_error`. -/
theorem actual_state_error
    (n r : ℕ) (t : ℝ) (hr : 0 < r)
    (ψ : QState (Fin (2 ^ (2 * n + 1)))) (hψ : Normalized ψ) :
    ‖toEuclidean_fromVec (ApplyGate (pfFamily (indexedTerm n) t r) ψ) -
        toEuclidean_fromVec (ApplyGate (HamiltonianEvolution (indexedTarget n) t) ψ)‖ ≤
      t ^ 2 / (2 * (r : ℝ)) * pfCommutatorSum (indexedTerm n) := by
  have hA : ‖pfFamily (indexedTerm n) t r - HamiltonianEvolution (indexedTarget n) t‖ ≤
      t ^ 2 / (2 * (r : ℝ)) * pfCommutatorSum (indexedTerm n) :=
    (actual_word_and_error n r t hr).2.2
  have hψn : ‖toEuclidean_fromVec ψ‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ
  have hbridge :
      toEuclidean_fromVec (ApplyGate (pfFamily (indexedTerm n) t r) ψ) -
        toEuclidean_fromVec (ApplyGate (HamiltonianEvolution (indexedTarget n) t) ψ) =
        toEuclideanCLM (𝕜 := ℂ)
          (pfFamily (indexedTerm n) t r - HamiltonianEvolution (indexedTarget n) t)
          (toEuclidean_fromVec ψ) := by
    rw [← toEuclideanCLM_applyGate (pfFamily (indexedTerm n) t r) ψ,
      ← toEuclideanCLM_applyGate (HamiltonianEvolution (indexedTarget n) t) ψ,
      map_sub]
    simp only [_root_.sub_apply]
  rw [hbridge]
  calc ‖toEuclideanCLM (𝕜 := ℂ)
          (pfFamily (indexedTerm n) t r - HamiltonianEvolution (indexedTarget n) t)
          (toEuclidean_fromVec ψ)‖
      ≤ ‖toEuclideanCLM (𝕜 := ℂ)
            (pfFamily (indexedTerm n) t r - HamiltonianEvolution (indexedTarget n) t)‖ *
          ‖toEuclidean_fromVec ψ‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖pfFamily (indexedTerm n) t r - HamiltonianEvolution (indexedTarget n) t‖ *
          ‖toEuclidean_fromVec ψ‖ := by
        rw [Matrix.l2_opNorm_toEuclideanCLM]
    _ = ‖pfFamily (indexedTerm n) t r - HamiltonianEvolution (indexedTarget n) t‖ := by
        rw [hψn, mul_one]
    _ ≤ t ^ 2 / (2 * (r : ℝ)) * pfCommutatorSum (indexedTerm n) := hA

/-- For every non-degenerate tree size, time and state-level precision, some positive segment
count makes the normalized-state `EuclideanSpace` error of the product formula at most that
precision. -/
theorem actual_state_precision
    (n : ℕ) (_hn : 0 < n) (t ε : ℝ) (hε : 0 < ε)
    (ψ : QState (Fin (2 ^ (2 * n + 1)))) (hψ : Normalized ψ) :
    ∃ r : ℕ, 0 < r ∧
      ‖toEuclidean_fromVec (ApplyGate (pfFamily (indexedTerm n) t r) ψ) -
          toEuclidean_fromVec (ApplyGate (HamiltonianEvolution (indexedTarget n) t) ψ)‖ ≤ ε := by
  obtain ⟨r, hrpos, _, hgoal⟩ := exists_segment_budget_and_error_le n t ε hε
  exact ⟨r, hrpos, (actual_state_error n r t hrpos ψ hψ).trans hgoal⟩

end Qatlib.Papers.DecisionTrees97.MainResults
