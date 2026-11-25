/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PEPSPrep11.MainResults.AlternatingMeasurement
public import Qatlib.Papers.PEPSPrep11.MainResults.PreparationRuntime

@[expose] public section

/-!
# Success budget for the PEPS preparation loop

The proof of Theorem 1 in arXiv:1104.1410v2 instantiates Lemma 3 at
`s = |V|/(2 e ε)` and uses the lower bound on each squared ground-state
overlap. The product below uses the successive conditional success
probabilities in the alternating-measurement model.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Qatlib.Papers.PEPSPrep11.MainResults.AlternatingMeasurement
open Qatlib.Papers.PEPSPrep11.MainResults.PreparationRuntime

namespace Qatlib.Papers.PEPSPrep11.MainResults

/-- The rounded iteration budget bounds each vertex's failure by `ε/|V|`
whenever its squared ground-state overlap is at least `1/κ²`. -/
theorem theorem1_perVertex_uniform (κ : ℝ) (V : ℕ) (ε p : ℝ)
    (hκ : 1 ≤ κ) (hV : 1 ≤ V) (hε : 0 < ε) (hp : 1 / κ ^ 2 ≤ p) (hp1 : p ≤ 1) :
    1 - perVertexFailure V ε ≤ termProb p (innerRounds κ V ε) := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hκsq : 0 < κ ^ 2 := by positivity
  have hVpos : (0 : ℝ) < V := by exact_mod_cast hV
  have hpmin : 0 < 1 / κ ^ 2 := by positivity
  let s : ℝ := (V : ℝ) / (2 * Real.exp 1 * ε)
  have hs : 0 < s := by dsimp [s]; positivity
  have hm : s / p ≤ (innerRounds κ V ε : ℝ) := calc
    s / p ≤ s / (1 / κ ^ 2) := div_le_div_of_nonneg_left hs.le hpmin hp
    _ = κ ^ 2 * (V : ℝ) / (2 * Real.exp 1 * ε) := by
      dsimp [s]
      rw [div_div_eq_mul_div, div_one, div_mul_eq_mul_div, mul_comm (V : ℝ)]
    _ ≤ _ := Nat.le_ceil _
  have hfail : 1 / (2 * Real.exp 1 * s) = perVertexFailure V ε := by
    dsimp [s, perVertexFailure]
    field_simp [hVpos.ne', hε.ne', (Real.exp_pos 1).ne']
  rw [← hfail]
  exact lemma3_alternating_measurement p s (innerRounds κ V ε) (hpmin.trans_le hp) hp1 hs hm

/-- The worst-case overlap `1/κ²` obeys the per-vertex budget of Theorem 1. -/
theorem theorem1_perVertex (κ : ℝ) (V : ℕ) (ε : ℝ)
    (hκ : 1 ≤ κ) (hV : 1 ≤ V) (hε : 0 < ε) :
    1 - perVertexFailure V ε ≤ termProb (1 / κ ^ 2) (innerRounds κ V ε) := by
  apply theorem1_perVertex_uniform κ V ε _ hκ hV hε le_rfl
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  rw [div_le_one (by positivity)]
  exact one_le_pow₀ hκ

/-- The product of conditional vertex success probabilities is at least
`1 - ε`, allowing the overlaps to differ between vertices. -/
theorem theorem1_success_from_overlaps (κ : ℝ) (V : ℕ) (ε : ℝ) (p : Fin V → ℝ)
    (hκ : 1 ≤ κ) (hV : 1 ≤ V) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hp : ∀ v, 1 / κ ^ 2 ≤ p v) (hp1 : ∀ v, p v ≤ 1) :
    1 - ε ≤ ∏ v, termProb (p v) (innerRounds κ V ε) := by
  have hVone : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hVpos : (0 : ℝ) < V := zero_lt_one.trans_le hVone
  have hbase : 0 ≤ 1 - perVertexFailure V ε :=
    sub_nonneg.mpr ((div_le_one hVpos).mpr (hε1.trans hVone))
  calc
    1 - ε ≤ (1 - perVertexFailure V ε) ^ V := theorem1_success V ε hV hε.le hε1
    _ = ∏ _v : Fin V, (1 - perVertexFailure V ε) := by simp
    _ ≤ ∏ v, termProb (p v) (innerRounds κ V ε) :=
      Finset.prod_le_prod₀ (fun _ _ => hbase) (fun v _ =>
        theorem1_perVertex_uniform κ V ε (p v) hκ hV hε (hp v) (hp1 v))

end Qatlib.Papers.PEPSPrep11.MainResults
