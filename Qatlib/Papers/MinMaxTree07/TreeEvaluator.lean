/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Qatlib.Papers.MinMaxTree07.ThresholdTree

/-!
# Min-Max evaluation outputs and cost bounds

This module combines arithmetic query bounds, output specifications, and asymptotic estimates
for Min-Max tree evaluation as studied in [CleveGavinskyYongeMallo2007]. `ValueOutput` specifies
the returned value, while `IndexOutput` specifies an input index attaining that value.

The cost estimates bound a pivot iteration and its repetitions, absorb a logarithmic overhead
into any positive power slack, and transfer an And-Or lower bound along an assumed query
comparison.

## Main statements

* `total_cost_le`: Bound repeated pivot costs by three times the And-Or cost per iteration.
* `minmax_cost_isBigO_rpow`: Absorb logarithmic overhead into a positive exponent slack.
* `exists_index_output`: An input index attaining the tree value exists.

## References

* [Cleve et al., 2007][CleveGavinskyYongeMallo2007]
-/

set_option autoImplicit false

namespace Qatlib.Papers.MinMaxTree07.TreeEvaluator

open Qatlib.Papers.MinMaxTree07.ThresholdTree

/-- If the search cost is at most the And-Or cost, one search and two And-Or calls cost at most
three And-Or calls; see [CleveGavinskyYongeMallo2007]. -/
theorem iteration_cost_le_three (qSearch qAndOr : ℕ) (hsearch : qSearch ≤ qAndOr) :
    qSearch + 2 * qAndOr ≤ 3 * qAndOr := by
  omega

/-- Under the same per-call comparison, the total cost of the given number of iterations is at
most `3 * iterations * qAndOr`; see [CleveGavinskyYongeMallo2007]. -/
theorem total_cost_le (iterations qSearch qAndOr : ℕ) (hsearch : qSearch ≤ qAndOr) :
    iterations * (qSearch + 2 * qAndOr) ≤ 3 * iterations * qAndOr := by
  have := iteration_cost_le_three qSearch qAndOr hsearch
  calc iterations * (qSearch + 2 * qAndOr)
      ≤ iterations * (3 * qAndOr) := Nat.mul_le_mul_left _ this
    _ = 3 * iterations * qAndOr := by ring

/-- At infinity, the real logarithm is big-O of every strictly positive real power. -/
theorem log_isBigO_rpow {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℝ => Real.log N) =O[Filter.atTop] (fun N : ℝ => N ^ ε) :=
  (isLittleO_log_rpow_atTop hε).isBigO

/-- If `W` is big-O of `N^(1 / 2 + ε)` for every positive `ε`, then `W N * Real.log N` has the
same family of bounds; see [CleveGavinskyYongeMallo2007]. -/
theorem minmax_cost_isBigO_rpow {W : ℝ → ℝ}
    (hW : ∀ ε : ℝ, 0 < ε → W =O[Filter.atTop] (fun N : ℝ => N ^ (1 / 2 + ε)))
    {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℝ => W N * Real.log N) =O[Filter.atTop] (fun N : ℝ => N ^ (1 / 2 + ε)) := by
  have hε2 : 0 < ε / 2 := by linarith
  have hW' : W =O[Filter.atTop] (fun N : ℝ => N ^ (1 / 2 + ε / 2)) := hW (ε / 2) hε2
  have hlog : (fun N : ℝ => Real.log N) =O[Filter.atTop] (fun N : ℝ => N ^ (ε / 2)) :=
    log_isBigO_rpow hε2
  have hprod : (fun N : ℝ => W N * Real.log N)
      =O[Filter.atTop] (fun N : ℝ => N ^ (1 / 2 + ε / 2) * N ^ (ε / 2)) :=
    hW'.mul hlog
  refine hprod.trans ?_
  have heq : (fun N : ℝ => N ^ (1 / 2 + ε / 2) * N ^ (ε / 2))
      =ᶠ[Filter.atTop] (fun N : ℝ => N ^ (1 / 2 + ε)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with N hN
    rw [← Real.rpow_add hN]
    congr 1
    ring
  exact heq.trans_isBigO (Asymptotics.isBigO_refl _ _)

/-- The proposition that `v` equals the evaluated value of the Min-Max tree. -/
def ValueOutput (t : Tree) (x : ℕ → ℕ) (v : ℕ) : Prop := v = Tree.eval t x

/-- The proposition that the input at index `j` equals the evaluated value of the Min-Max tree. -/
def IndexOutput (t : Tree) (x : ℕ → ℕ) (j : ℕ) : Prop := x j = Tree.eval t x

/-- There exists an input index satisfying the Min-Max index-output specification; see
[CleveGavinskyYongeMallo2007]. -/
theorem exists_index_output (t : Tree) (x : ℕ → ℕ) : ∃ j, IndexOutput t x j := by
  obtain ⟨i, hi⟩ := Tree.exists_leaf_eq_eval t x
  exact ⟨i, hi.symm⟩

/-- There exists a value satisfying the Min-Max value-output specification. -/
theorem exists_value_output (t : Tree) (x : ℕ → ℕ) : ∃ v, ValueOutput t x v :=
  ⟨Tree.eval t x, rfl⟩

/-- An eventual square-root lower bound for `QAndOr` also bounds `QMinMax` when `QAndOr N ≤
QMinMax N` pointwise; see [CleveGavinskyYongeMallo2007]. -/
theorem lower_bound_transfers {QMinMax QAndOr : ℕ → ℝ}
    (hrestrict : ∀ N, QAndOr N ≤ QMinMax N) {c : ℝ}
    (hAndOr : ∀ᶠ N in Filter.atTop, c * N ^ (1 / 2 : ℝ) ≤ QAndOr N) :
    ∀ᶠ N in Filter.atTop, c * N ^ (1 / 2 : ℝ) ≤ QMinMax N :=
  hAndOr.mono fun N hN => le_trans hN (hrestrict N)

/-- On Boolean inputs, minimum gates act as conjunction and maximum gates act as disjunction;
see [CleveGavinskyYongeMallo2007]. -/
theorem bool_gate_minmax_eq_andor (g : Gate) (a b : Bool) :
    Tree.merge g a b = (match g with | .min => a && b | .max => a || b) := by
  cases g with
  | min => simp [Tree.merge_min, Tree.bool_min_eq_and]
  | max => simp [Tree.merge_max, Tree.bool_max_eq_or]

end Qatlib.Papers.MinMaxTree07.TreeEvaluator
