/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Qatlib.Papers.MinMaxTree07.ThresholdTree
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.MinMaxTree07.TreeEvaluator

open Qatlib.Papers.MinMaxTree07.ThresholdTree

theorem iteration_cost_le_three (qSearch qAndOr : ℕ) (hsearch : qSearch ≤ qAndOr) :
    qSearch + 2 * qAndOr ≤ 3 * qAndOr := by
  omega

theorem total_cost_le (iterations qSearch qAndOr : ℕ) (hsearch : qSearch ≤ qAndOr) :
    iterations * (qSearch + 2 * qAndOr) ≤ 3 * iterations * qAndOr := by
  have := iteration_cost_le_three qSearch qAndOr hsearch
  calc iterations * (qSearch + 2 * qAndOr)
      ≤ iterations * (3 * qAndOr) := Nat.mul_le_mul_left _ this
    _ = 3 * iterations * qAndOr := by ring

theorem log_isBigO_rpow {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℝ => Real.log N) =O[Filter.atTop] (fun N : ℝ => N ^ ε) :=
  (isLittleO_log_rpow_atTop hε).isBigO

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

def ValueOutput (t : Tree) (x : ℕ → ℕ) (v : ℕ) : Prop := v = Tree.eval t x

def IndexOutput (t : Tree) (x : ℕ → ℕ) (j : ℕ) : Prop := x j = Tree.eval t x

theorem exists_index_output (t : Tree) (x : ℕ → ℕ) : ∃ j, IndexOutput t x j := by
  obtain ⟨i, hi⟩ := Tree.exists_leaf_eq_eval t x
  exact ⟨i, hi.symm⟩

theorem exists_value_output (t : Tree) (x : ℕ → ℕ) : ∃ v, ValueOutput t x v :=
  ⟨Tree.eval t x, rfl⟩

theorem lower_bound_transfers {QMinMax QAndOr : ℕ → ℝ}
    (hrestrict : ∀ N, QAndOr N ≤ QMinMax N) {c : ℝ}
    (hAndOr : ∀ᶠ N in Filter.atTop, c * N ^ (1 / 2 : ℝ) ≤ QAndOr N) :
    ∀ᶠ N in Filter.atTop, c * N ^ (1 / 2 : ℝ) ≤ QMinMax N :=
  hAndOr.mono fun N hN => le_trans hN (hrestrict N)

theorem bool_gate_minmax_eq_andor (g : Gate) (a b : Bool) :
    Tree.merge g a b = (match g with | .min => a && b | .max => a || b) := by
  cases g with
  | min => simp [Tree.merge_min, Tree.bool_min_eq_and]
  | max => simp [Tree.merge_max, Tree.bool_max_eq_or]

end Qatlib.Papers.MinMaxTree07.TreeEvaluator
