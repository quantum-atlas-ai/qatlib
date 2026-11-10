/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Setup
import Qatlib.Papers.ModularFunct00.MainResults.Approximation.ErrorBudget
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Approximation

open Matrix
open scoped Matrix.Norms.L2Operator

def blockDiagOne (k : ℕ) (g : CM 4) : CM (4 + k) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin k) (Fin k) ℂ))

theorem theorem2_1_word_length_budget {G : Type*} [Group G] {m : ℕ} {σ : Fin m → G}
    {l : ℕ} {bs : List G} (hbs : ∀ b ∈ bs, BraidWord σ l b) :
    BraidWord σ (bs.length * l) bs.prod :=
  braidWord_list_prod hbs

theorem theorem2_1_error_accumulation {R : Type*} [NormedRing R] [NormOneClass R]
    (u v : List R)
    (hlen : u.length = v.length) (hpos : 1 ≤ u.length)
    (hu : ∀ x ∈ u, ‖x‖ ≤ 1) (hv : ∀ x ∈ v, ‖x‖ ≤ 1)
    (hstep : ∀ p ∈ u.zipWith (fun a b => ‖a - b‖) v,
      p ≤ 1 / (10 * (u.length : ℝ))) :
    ‖u.prod - v.prod‖ ≤ 1 / 10 := by
  have h1 := norm_list_prod_sub_prod_le u v hlen hu hv
  have h2 : (u.zipWith (fun a b => ‖a - b‖) v).sum ≤ 1 / 10 := by
    have h3 := list_sum_le_length_mul hstep
    rw [List.length_zipWith, ← hlen, Nat.min_self, nat_mul_inv_ten u.length hpos] at h3
    exact h3
  exact le_trans h1 h2

theorem theorem2_1_success_from_error {err : ℝ} (h : err ≤ 1 / 10) :
    3 / 4 ≤ 1 - err :=
  success_ge_three_quarters h

end Qatlib.Papers.ModularFunct00.MainResults.Approximation
