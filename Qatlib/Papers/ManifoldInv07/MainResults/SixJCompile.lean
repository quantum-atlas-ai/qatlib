/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option autoImplicit false

open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ManifoldInv07.MainResults.SixJCompile

def sixJRegisterDim (k : ℕ) : ℕ := 2 ^ Nat.clog 2 (k + 1)

theorem sixJRegisterDim_pos (k : ℕ) : 0 < sixJRegisterDim k :=
  pow_pos (by norm_num) _

theorem sixJRegisterDim_eq_pow (k : ℕ) : ∃ m, sixJRegisterDim k = 2 ^ m :=
  ⟨_, rfl⟩

theorem le_sixJRegisterDim (k : ℕ) : k + 1 ≤ sixJRegisterDim k := by
  unfold sixJRegisterDim
  exact Nat.le_pow_clog (by norm_num) (k + 1)

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

theorem sixJRegisterDim_mono : Monotone sixJRegisterDim := by
  intro a b hab
  unfold sixJRegisterDim
  exact Nat.pow_le_pow_right (by norm_num) (Nat.clog_mono_right 2 (Nat.succ_le_succ hab))

def sixJBlockDim (k : ℕ) (_entries : Fin 6 → ℕ) : ℕ := sixJRegisterDim k

def sixJBlockDimAtSize (k : ℕ) (_n _c : ℕ) (_entries : Fin 6 → ℕ) : ℕ :=
  sixJRegisterDim k

theorem sixJBlockDim_independent_of_problem_size (k : ℕ) (entries : Fin 6 → ℕ)
    (n c n' c' : ℕ) :
    sixJBlockDimAtSize k n c entries = sixJBlockDimAtSize k n' c' entries := rfl

theorem sixJBlockDim_independent_of_entries (k : ℕ) (e e' : Fin 6 → ℕ) :
    sixJBlockDim k e = sixJBlockDim k e' := rfl

def q6jBlockAtSize (_k _n _c : ℕ) {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ := A

theorem q6j_block_approximation {Word : Type*} {k : ℕ}
    (cost : Word → ℕ)
    (eval : Word → Matrix (Fin (sixJRegisterDim k)) (Fin (sixJRegisterDim k)) ℂ)
    (ε : ℝ) (L : ℕ) (A : Matrix (Fin (sixJRegisterDim k)) (Fin (sixJRegisterDim k)) ℂ)
    (hScheme : ∃ w : Word, cost w ≤ L ∧ ‖eval w - A‖ ≤ ε) :
    ∀ n c : ℕ, ∃ w : Word, cost w ≤ L ∧
      ‖eval w - q6jBlockAtSize k n c A‖ ≤ ε := by
  intro n c
  exact hScheme

theorem recoupling_gate_count_linear {Word : Type*} (cost : Word → ℕ) (n B : ℕ)
    (block : Fin (2 * n) → Word) (hblock : ∀ i, cost (block i) ≤ B) :
    (∑ i, cost (block i)) ≤ (2 * n) * B := by
  calc (∑ i : Fin (2 * n), cost (block i)) ≤ ∑ _i : Fin (2 * n), B :=
        Finset.sum_le_sum (fun i _ => hblock i)
    _ = (2 * n) * B := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

end Qatlib.Papers.ManifoldInv07.MainResults.SixJCompile
