/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordProduct
import Mathlib.Algebra.BigOperators.Fin

/-! # Finite rational transport majorants with no highest-derivative query -/
set_option autoImplicit false
open Finset
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- The forcing convolution is evaluated as a finite lower-order sum. -/
theorem wordProductRemainderMajorant_transverse (F G : ℕ → ℝ) (n : ℕ) :
    wordProductRemainderMajorant F G (n+1)=
      ∑ j ∈ range (n+1), ((n+1).choose (j+1) : ℝ)*G (j+1)*F (n-j) := by
  rw [wordProductRemainderMajorant_eq]
  rw [← sum_range_reflect (fun j => ((n+1).choose j : ℝ)*F j*G (n+1-j)) (n+1)]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
  have hchoose := Nat.choose_symm (Nat.add_le_add_right hjn 1)
  rw [Nat.add_sub_add_right] at hchoose
  have ha : n+1-1-j=n-j := by omega
  have hb : n+1-(n-j)=j+1 := by omega
  rw [ha,hb,hchoose]
  ring


/-- The Python Q recurrence, evaluated by smaller natural indices only.
Both sums are finite and every recursive index is strictly smaller. -/
def transportWordMajorant (K : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | n+1 => max
      (7*∑ j : Fin (n+1), ((n+1).choose (j.val+1) : ℚ)*K (j.val+1)*
        transportWordMajorant K (n-j.val))
      (∑ j : Fin (n+1), (n.choose j.val : ℚ)*transportWordMajorant K j.val*K (n-j.val))
termination_by n => n

/-- Original `transportWordMajorant_nonneg` guarantee for the `TransportMajorant` construction; the complete source hypotheses are retained. -/
theorem transportWordMajorant_nonneg (K : ℕ → ℚ) (hK : ∀ j, 0 ≤ K j) (n : ℕ) :
    0 ≤ transportWordMajorant K n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [transportWordMajorant]
    | succ n =>
      rw [transportWordMajorant]
      apply le_max_of_le_right
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ih j.val j.isLt)) (hK _)

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
