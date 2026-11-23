module

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Qatlib.Papers.WeightEnum07.MainResults.WeightGeometry

@[expose] public section

/-! # Weight-enumerator geometry consumer -/

set_option autoImplicit false
set_option warningAsError true

open scoped Matrix.Norms.L2Operator
open Qatlib.Papers.WeightEnum07.MainResults
open Qatlib.Papers.WeightEnum07.MainResults

namespace QatlibTests.WeightEnum07Geometry

private def word : Fin 3 → ℤ := ![0, 2, -1]

/-- The example word has two nonzero coordinates. -/
private theorem word_weight : hammingWeightOf word = 2 := by
  change Nat.card {i : Fin 3 // word i ≠ 0} = 2
  rw [Nat.card_eq_fintype_card]
  decide

example : ‖supportVector word‖ ^ 2 = 2 := by
  rw [supportVector_norm_sq, word_weight]
  norm_num

open Classical in
example (code : ICQCode) :
    code.weightCounts 2 =
      (code.words.filter (fun w => ‖supportVector w‖ ^ 2 = (2 : ℝ))).card := by
  exact weightCounts_eq_card_filter_supportVector_norm_sq code 2

example : ‖supportProjector word‖ = (1 : ℝ) := by
  apply supportProjector_opNorm_eq_one
  exact ⟨1, by simp [word]⟩

example : ∀ w : Fin 3 → ℤ, ‖supportProjector w‖ ≤ (1 : ℝ) := by
  exact supportProjector_uniform_bound (by norm_num)

end QatlibTests.WeightEnum07Geometry
