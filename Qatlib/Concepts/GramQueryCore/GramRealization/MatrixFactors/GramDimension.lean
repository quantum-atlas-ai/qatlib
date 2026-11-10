/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Concepts.GramQueryCore.GramRealization.GramDimension

theorem p3_target_necessity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [Module.Finite ℂ E] {r : ℕ} (w : Fin r → E)
    (hw_ne : ∀ i, w i ≠ 0)
    (hw_orth : ∀ i j, i ≠ j → inner ℂ (w i) (w j) = 0) :
    r ≤ Module.finrank ℂ E := by
  have hli : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hin : inner ℂ (w i) (∑ j, g j • w j) = 0 := by
      rw [hg, inner_zero_right]
    rw [inner_sum] at hin
    rw [Finset.sum_eq_single i] at hin
    · have hgi : g i * inner ℂ (w i) (w i) = 0 := by
        rw [inner_smul_right] at hin; exact hin
      rcases mul_eq_zero.mp hgi with h | h
      · exact h
      · exact absurd h (inner_self_ne_zero.mpr (hw_ne i))
    · intro j _hj hji
      rw [inner_smul_right, hw_orth i j (Ne.symm hji), mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  simpa using hli.fintype_card_le_finrank

theorem p3_bits_bridge (r n : ℕ) (hr : r ≠ 0) (h : r ≤ 2 ^ n) :
    Nat.log2 r ≤ n := by
  by_cases h2 : Nat.log2 r ≤ n
  · exact h2
  · have h2' : n < Nat.log2 r := lt_of_not_ge h2
    have h3 := (Nat.le_log2 hr).mp (by omega : n + 1 ≤ Nat.log2 r)
    have h4 : 2 ^ n < 2 ^ (n + 1) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

end Qatlib.Concepts.GramQueryCore.GramRealization.GramDimension
