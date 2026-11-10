/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ExactSimon97.MainResults

noncomputable def uniformOnSub {n : ℕ} (S : Submodule (ZMod 2) (BoolVec n)) (z : BoolVec n) : ℝ :=
  by
    classical
    exact if z ∈ S then ((Nat.card S : ℝ))⁻¹ else 0

lemma natCard_ortho_pos {n : ℕ} (H : Submodule (ZMod 2) (BoolVec n)) :
    0 < Nat.card (ortho H) := by
  haveI : Nonempty (ortho H) := ⟨0, by simp⟩
  exact Nat.card_pos

theorem theorem3_uniform_distribution {n : ℕ}
    (H0 : Submodule (ZMod 2) (BoolVec n)) :
    (∑ z, uniformOnSub (ortho H0) z) = 1 := by
  classical
  have hcard : ((Finset.univ.filter (fun z : BoolVec n => z ∈ ortho H0)).card : ℝ) =
      Nat.card (ortho H0) := by
    rw [← Fintype.card_subtype (fun z : BoolVec n => z ∈ ortho H0)]
    exact_mod_cast (Nat.card_eq_fintype_card (α := ortho H0)).symm
  have hsum : (∑ z, uniformOnSub (ortho H0) z) =
      ∑ z : BoolVec n, if z ∈ ortho H0 then ((Nat.card (ortho H0) : ℝ))⁻¹ else 0 := by
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [uniformOnSub]
  rw [hsum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard]
  exact mul_inv_cancel₀ (by exact_mod_cast (ne_of_gt (natCard_ortho_pos H0)))

end Qatlib.Papers.ExactSimon97.MainResults
