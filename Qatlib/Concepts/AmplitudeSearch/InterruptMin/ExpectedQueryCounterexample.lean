/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Concepts.SearchStopping.QueryLowerBound.FixedQueryLowerBound
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Reflection.Basic
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# A counterexample using expected query cost

This module constructs a randomized search experiment on 64 indices. A biased coin selects
either four Grover iterations or a uniform output; `expected_query_counterexample64` proves
success at least one half with expected query count `8 / 3`.

The example distinguishes expected query cost from the fixed query threshold appearing in the
search setting of [BoyerEtAl1998].

## Main statements

* `expected_query_counterexample64`: Constructs normalized states and unitary search circuits
  whose joint outcome law succeeds with probability at least one half and has expected query
  count `8 / 3`, strictly below `⌊sin (π / 8) * √64⌋`. This tests the distinction between fixed
  and expected query bounds in the setting of [BoyerEtAl1998].

## References

* [Boyer et al., 1998][BoyerEtAl1998]
* [Grover, 1996][Grover1996]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open scoped BigOperators
open Qatlib.Concepts.SearchStopping.KnownCount

/-- A Boolean coin state assigning probabilities `2 / 3` to `true` and `1 / 3` to `false`. -/
noncomputable def BudgetCoin64 : QState Bool := fun b =>
  if b then (Real.sqrt (2 / 3) : ℂ) else (Real.sqrt (1 / 3) : ℂ)

/-- The uniform state on 64 indices tensored with the minus ancilla state. -/
noncomputable def BudgetStart64 : QState (Fin 64 × Bool) :=
  TensorState (Uniform (Fin 64)) Minus

/-- The branch circuit performing four lifted Grover iterations on `true` and no steps on
`false`. -/
noncomputable def BudgetBranch64 (b : Bool) : Circuit (Fin 64 × Bool) :=
  if b then LiftCircuit (GroverCircuit (Fin 64) 4) else []

/-- The Boolean oracle marking the single index `y` among 64 indices. -/
noncomputable def BudgetOracle64 (y : Fin 64) : Matrix (Fin 64 × Bool) (Fin 64 × Bool) ℂ :=
  BitOracleOn (fun i => decide (i ∈ ({y} : Finset (Fin 64))))

/-- The probability of observing index `z` after running the selected branch with marked index
`y`. -/
noncomputable def BudgetOutput64 (y : Fin 64) (b : Bool) (z : Fin 64) : ℝ :=
  MeasureProb (Run (BudgetOracle64 y) (BudgetBranch64 b) BudgetStart64)
    (({z} : Finset (Fin 64)) ×ˢ Finset.univ)

/-- The joint mass of the coin branch and its observed search output. -/
noncomputable def BudgetMass64 (y : Fin 64) (outcome : Bool × Fin 64) : ℝ :=
  BornProb BudgetCoin64 outcome.1 * BudgetOutput64 y outcome.1 outcome.2

/-- The query count of the circuit selected by an outcome's coin branch. -/
noncomputable def BudgetQueries64 (outcome : Bool × Fin 64) : ℕ :=
  QueryCount (BudgetBranch64 outcome.1)

/-- The coin's Born probability is `2 / 3` for `true` and `1 / 3` for `false`. -/
theorem budgetCoin64_born (b : Bool) :
    BornProb BudgetCoin64 b = if b then (2 / 3 : ℝ) else 1 / 3 := by
  cases b <;> norm_num [BudgetCoin64, BornProb, Complex.norm_real, Real.norm_eq_abs,
    div_pow, sq_abs, Real.sq_sqrt]

/-- The biased Boolean coin state is normalized. -/
theorem budgetCoin64_normalized : Normalized BudgetCoin64 := by
  change (∑ b : Bool, BornProb BudgetCoin64 b) = 1
  simp [budgetCoin64_born]
  norm_num

/-- The uniform index state with minus ancilla is normalized. -/
theorem budgetStart64_normalized : Normalized BudgetStart64 :=
  normalized_tensorState (normalized_uniform (by norm_num)) normalized_minus

/-- Both selected branch circuits consist of unitary steps. -/
theorem budgetBranch64_valid (b : Bool) : IsUnitaryCircuit (BudgetBranch64 b) := by
  cases b with
  | false => exact isUnitaryCircuit_nil
  | true => exact (isUnitaryCircuit_groverCircuit (by norm_num) 4).lift

/-- The single-marked-index Boolean oracle is unitary. -/
theorem budgetOracle64_unitary (y : Fin 64) :
    BudgetOracle64 y ∈ Matrix.unitaryGroup (Fin 64 × Bool) ℂ := bitOracleOn_unitary _

/-- The query cost is four on the `true` branch and zero on the `false` branch. -/
theorem budgetQueries64_eq (o : Bool × Fin 64) :
    BudgetQueries64 o = if o.1 then 4 else 0 := by
  rcases o with ⟨b, z⟩
  cases b <;> simp [BudgetQueries64, BudgetBranch64, queryCount_liftCircuit,
    queryCount_groverCircuit]

/-- The `true` branch's output probability equals the Born probability after four Grover
iterations. -/
theorem budgetOutput64_true (y z : Fin 64) :
    BudgetOutput64 y true z = BornProb (GroverState {y} 4) z := by
  unfold BudgetOutput64 BudgetOracle64 BudgetBranch64 BudgetStart64
  simp only [if_true]
  rw [measureProb_run_liftCircuit_bitOracleOn]
  simp only [MeasureProb, Finset.sum_singleton, GroverState, SetOracle]

/-- The `false` branch outputs every index with probability `1 / 64`. -/
theorem budgetOutput64_false (y z : Fin 64) :
    BudgetOutput64 y false z = 1 / 64 := by
  unfold BudgetOutput64 BudgetBranch64 BudgetStart64
  simp only [Bool.false_eq_true, if_false, run_nil]
  rw [measureProb_tensorState_left normalized_minus, measureProb_uniform]
  norm_num

/-- The four-iteration branch returns the marked index with probability `224404006369 /
274877906944`. -/
theorem budgetOutput64_four_success (y : Fin 64) :
    BudgetOutput64 y true y = (224404006369 : ℝ) / 274877906944 := by
  have hN : 0 < Fintype.card (Fin 64) := by norm_num
  have hinit : Uniform (Fin 64) = MarkedVector {y} (1 / 8) (1 / 8) := by
    funext i
    norm_num [Uniform, MarkedVector]
  have hstep (a b : ℂ) := run_groverStep_markedVector hN ({y} : Finset (Fin 64)) a b
  simp only [Finset.card_singleton, Fintype.card_fin, Nat.cast_one] at hstep
  have hstate : GroverState ({y} : Finset (Fin 64)) 4 =
      MarkedVector {y} (473713 / 524288) (28305 / 524288) := by
    unfold GroverState GroverCircuit
    rw [hinit]
    simp only [RepeatCircuit, run_append]
    rw [hstep, hstep, hstep, hstep]
    norm_num [Run]
  rw [budgetOutput64_true, hstate]
  norm_num [BornProb, MarkedVector, norm_div]

/-- Each branch output law is nonnegative and sums to one. -/
theorem budgetOutput64_mass (y : Fin 64) (b : Bool) :
    (∀ z, 0 ≤ BudgetOutput64 y b z) ∧ (∑ z, BudgetOutput64 y b z) = 1 := by
  cases b with
  | false => constructor <;> simp [budgetOutput64_false]
  | true =>
    simp only [budgetOutput64_true]
    exact ⟨fun z => by unfold BornProb; positivity,
      bornProb_sum_eq_one (normalized_groverState (by norm_num) {y} 4)⟩

/-- The integer floor of `sin (π / 8) * √64` is three. -/
theorem source_floor64 : ⌊Real.sin (Real.pi / 8) * Real.sqrt 64⌋ = (3 : ℤ) := by
  have htwo := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have htpos := Real.sqrt_nonneg (2 : ℝ)
  have htlo : 1 < Real.sqrt 2 := by nlinarith
  have hthi : Real.sqrt 2 ≤ (23 / 16 : ℝ) := by nlinarith
  have hn : 0 ≤ 2 - Real.sqrt 2 := by linarith
  have hs := Real.sq_sqrt hn
  have hsp := Real.sqrt_nonneg (2 - Real.sqrt 2)
  apply Int.floor_eq_iff.mpr
  rw [Real.sin_pi_div_eight]
  norm_num
  constructor <;> nlinarith

/-- Constructs normalized states and unitary search circuits whose joint outcome law succeeds
with probability at least one half and has expected query count `8 / 3`, strictly below
`⌊sin (π / 8) * √64⌋`. This tests the distinction between fixed and expected query bounds in
the setting of [BoyerEtAl1998]. -/
theorem expected_query_counterexample64 :
    Normalized BudgetCoin64 ∧ Normalized BudgetStart64 ∧
    (∀ b, IsUnitaryCircuit (BudgetBranch64 b)) ∧
    (∀ y : Fin 64, BudgetOracle64 y ∈ Matrix.unitaryGroup (Fin 64 × Bool) ℂ ∧
      (∀ o, 0 ≤ BudgetMass64 y o) ∧
      (∑ o : Bool × Fin 64, BudgetMass64 y o) = 1 ∧
      (1 / 2 : ℝ) ≤ ∑ b : Bool, BudgetMass64 y (b, y) ∧
      (∑ o : Bool × Fin 64, BudgetMass64 y o * (BudgetQueries64 o : ℝ)) = 8 / 3 ∧
      (∑ o : Bool × Fin 64, BudgetMass64 y o * (BudgetQueries64 o : ℝ)) <
        (⌊Real.sin (Real.pi / 8) * Real.sqrt 64⌋ : ℤ)) := by
  refine ⟨budgetCoin64_normalized, budgetStart64_normalized, budgetBranch64_valid, ?_⟩
  intro y
  have hnorm := budgetOutput64_mass y
  have hm0 (z : Fin 64) : BudgetMass64 y (false, z) = (1 / 3 : ℝ) * (1 / 64) := by
    simp [BudgetMass64, budgetCoin64_born, budgetOutput64_false]
  have hm1 (z : Fin 64) : BudgetMass64 y (true, z) =
      (2 / 3 : ℝ) * BudgetOutput64 y true z := by
    simp [BudgetMass64, budgetCoin64_born]
  have he : (∑ o : Bool × Fin 64, BudgetMass64 y o * (BudgetQueries64 o : ℝ)) = 8 / 3 := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp [budgetQueries64_eq, hm0, hm1, ← Finset.mul_sum, ← Finset.sum_mul, (hnorm true).2]
    ring
  refine ⟨budgetOracle64_unitary y, ?_, ?_, ?_, he, ?_⟩
  · intro o
    exact mul_nonneg (by unfold BornProb; positivity) ((hnorm o.1).1 o.2)
  · simp [Fintype.sum_prod_type, hm0, hm1, ← Finset.mul_sum, (hnorm true).2]
    norm_num
  · simp only [Fintype.sum_bool, hm0, hm1]
    rw [budgetOutput64_four_success]
    norm_num
  · rw [he, source_floor64]
    norm_num

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
