/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Register dimensions and conditional recoupling compilation

This module studies the padded register dimension for recoupling blocks in
[GarneroneMarzuoliRasetti2007]. The function `sixJRegisterDim` rounds k + 1 up to a power of
two, with bounds between k + 1 and 2(k + 1), and the block-size definitions depend only on k.

The approximation theorem reuses a supplied approximation witness for `q6jBlockAtSize`, which is
the input matrix independently of the size parameters. The final counting lemma sums uniform
costs over 2n blocks.

## Main statements

* `sixJRegisterDim_le_two_mul`: The padded dimension is at most twice k + 1.
* `q6j_block_approximation`: An assumed approximation witness applies at every problem size.
* `recoupling_gate_count_linear`: Uniform block costs sum to at most 2nB.

## References

* [Garnerone et al., 2007][GarneroneMarzuoliRasetti2007]
-/

set_option autoImplicit false

open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ManifoldInv07.MainResults.SixJCompile

/-- The power-of-two padded dimension 2^ceil(log₂(k + 1)), expressed using `Nat.clog`. -/
def sixJRegisterDim (k : ℕ) : ℕ := 2 ^ Nat.clog 2 (k + 1)

/-- The padded recoupling register dimension is positive. -/
theorem sixJRegisterDim_pos (k : ℕ) : 0 < sixJRegisterDim k :=
  pow_pos (by norm_num) _

/-- The padded recoupling register dimension is a power of two. -/
theorem sixJRegisterDim_eq_pow (k : ℕ) : ∃ m, sixJRegisterDim k = 2 ^ m :=
  ⟨_, rfl⟩

/-- The padded recoupling register dimension is at least k + 1 [GarneroneMarzuoliRasetti2007]. -/
theorem le_sixJRegisterDim (k : ℕ) : k + 1 ≤ sixJRegisterDim k := by
  unfold sixJRegisterDim
  exact Nat.le_pow_clog (by norm_num) (k + 1)

/-- The padded recoupling register dimension is at most 2(k + 1) [GarneroneMarzuoliRasetti2007]. -/
theorem sixJRegisterDim_le_two_mul (k : ℕ) : sixJRegisterDim k ≤ 2 * (k + 1) := by
  unfold sixJRegisterDim
  by_cases hk : k + 1 = 1
  · rw [hk, Nat.clog_one_right]
    norm_num
  · have hx : 1 < k + 1 := by omega
    have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hx
    have hpos : 0 < Nat.clog 2 (k + 1) := Nat.clog_pos (by norm_num) hx
    have hpow : 2 ^ Nat.clog 2 (k + 1)
        = 2 ^ (Nat.clog 2 (k + 1)).pred * 2 := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
      rw [Nat.pow_succ]
    calc 2 ^ Nat.clog 2 (k + 1)
        = 2 ^ (Nat.clog 2 (k + 1)).pred * 2 := hpow
      _ ≤ (k + 1) * 2 := Nat.mul_le_mul_right 2 (Nat.le_of_lt hlt)
      _ = 2 * (k + 1) := by ring

/-- The padded recoupling register dimension is monotone in the level k
[GarneroneMarzuoliRasetti2007]. -/
theorem sixJRegisterDim_mono : Monotone sixJRegisterDim := by
  intro a b hab
  unfold sixJRegisterDim
  exact Nat.pow_le_pow_right (by norm_num) (Nat.clog_mono_right 2 (Nat.succ_le_succ hab))

/-- The recoupling block dimension given by `sixJRegisterDim k`, independently of the six
entries. -/
def sixJBlockDim (k : ℕ) (_entries : Fin 6 → ℕ) : ℕ := sixJRegisterDim k

/-- The recoupling block dimension given by `sixJRegisterDim k`, independently of the
problem-size parameters and six entries. -/
def sixJBlockDimAtSize (k : ℕ) (_n _c : ℕ) (_entries : Fin 6 → ℕ) : ℕ :=
  sixJRegisterDim k

/-- At fixed level and entries, changing either problem-size parameter leaves the block
dimension unchanged [GarneroneMarzuoliRasetti2007]. -/
theorem sixJBlockDim_independent_of_problem_size (k : ℕ) (entries : Fin 6 → ℕ)
    (n c n' c' : ℕ) :
    sixJBlockDimAtSize k n c entries = sixJBlockDimAtSize k n' c' entries := rfl

/-- At fixed level, changing the six entries leaves the block dimension unchanged. -/
theorem sixJBlockDim_independent_of_entries (k : ℕ) (e e' : Fin 6 → ℕ) :
    sixJBlockDim k e = sixJBlockDim k e' := rfl

/-- The supplied matrix regarded as a block at arbitrary level and problem-size parameters,
without changing its entries. -/
def q6jBlockAtSize (_k _n _c : ℕ) {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ := A

/-- A supplied word of cost at most L approximating A within ε also approximates `q6jBlockAtSize
k n c A` within ε for every n and c [GarneroneMarzuoliRasetti2007]. -/
theorem q6j_block_approximation {Word : Type*} {k : ℕ}
    (cost : Word → ℕ)
    (eval : Word → Matrix (Fin (sixJRegisterDim k)) (Fin (sixJRegisterDim k)) ℂ)
    (ε : ℝ) (L : ℕ) (A : Matrix (Fin (sixJRegisterDim k)) (Fin (sixJRegisterDim k)) ℂ)
    (hScheme : ∃ w : Word, cost w ≤ L ∧ ‖eval w - A‖ ≤ ε) :
    ∀ n c : ℕ, ∃ w : Word, cost w ≤ L ∧
      ‖eval w - q6jBlockAtSize k n c A‖ ≤ ε := by
  intro n c
  exact hScheme

/-- If each of 2n blocks has cost at most B, their total cost is at most 2nB
[GarneroneMarzuoliRasetti2007]. -/
theorem recoupling_gate_count_linear {Word : Type*} (cost : Word → ℕ) (n B : ℕ)
    (block : Fin (2 * n) → Word) (hblock : ∀ i, cost (block i) ≤ B) :
    (∑ i, cost (block i)) ≤ (2 * n) * B := by
  calc (∑ i : Fin (2 * n), cost (block i)) ≤ ∑ _i : Fin (2 * n), B :=
        Finset.sum_le_sum (fun i _ => hblock i)
    _ = (2 * n) * B := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

end Qatlib.Papers.ManifoldInv07.MainResults.SixJCompile
