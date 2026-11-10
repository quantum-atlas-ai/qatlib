/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.UniqueCollision

theorem jw_optimized_scale_admissibility (k N : ℕ) (B : ℝ) (hk : 1 ≤ k)
    (hB : 4 * (k : ℝ) ≤ B) (hN : B ^ (k + 1) ≤ (N : ℝ)) :
    let X := (N : ℝ) ^ ((k : ℝ) / (k + 1))
    let r := Nat.floor X
    1 ≤ X ∧ X ^ (k + 1) = (N : ℝ) ^ k ∧
      k ≤ r ∧ 2 * k ≤ r + 1 ∧
      (B / 4) * ((r : ℝ) + 1) ≤ (N : ℝ) - r ∧
      X / 4 ≤ ((r + 1 - k : ℕ) : ℝ) := by
  let x := (N : ℝ) ^ (1 / ((k : ℝ) + 1))
  let X := (N : ℝ) ^ ((k : ℝ) / (k + 1))
  let r := Nat.floor X
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hB4 : 4 ≤ B := by linarith only [hB, hkR]
  have hBp : 0 < B := by linarith only [hB4]
  have hNp : (0 : ℝ) < N := (pow_pos hBp (k + 1)).trans_le hN
  have hx0 : 0 ≤ x := Real.rpow_nonneg hNp.le _
  have hden : (k : ℝ) + 1 ≠ 0 := by positivity
  have hxpow : x ^ (k + 1) = (N : ℝ) := by
    dsimp only [x]
    rw [← Real.rpow_mul_natCast hNp.le]
    have he : (1 / ((k : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [he, Real.rpow_one]
  have hxB : B ≤ x :=
    le_of_pow_le_pow_left₀ (by omega : k + 1 ≠ 0) hx0 (hN.trans_eq hxpow.symm)
  have hx1 : 1 ≤ x := by linarith only [hxB, hB4]
  have hXeq : x ^ k = X := by
    dsimp only [x, X]
    rw [← Real.rpow_mul_natCast hNp.le]
    congr 1
    ring
  have hxX : x ≤ X := by
    rw [← hXeq]
    exact le_self_pow₀ hx1 (by omega : k ≠ 0)
  have hXB : B ≤ X := hxB.trans hxX
  have hX1 : 1 ≤ X := by linarith only [hXB, hB4]
  have hX0 : 0 ≤ X := by linarith only [hX1]
  have hX4k : 4 * (k : ℝ) ≤ X := hB.trans hXB
  have hXpow : X ^ (k + 1) = (N : ℝ) ^ k := by
    rw [← hXeq, ← pow_mul, Nat.mul_comm k (k + 1), pow_mul, hxpow]
  have hNx : X * x = (N : ℝ) := by rw [← hXeq, ← pow_succ, hxpow]
  have hNBX : B * X ≤ (N : ℝ) := by
    calc
      _ ≤ x * X := mul_le_mul_of_nonneg_right hxB hX0
      _ = _ := by rw [mul_comm, hNx]
  have hrle : (r : ℝ) ≤ X := Nat.floor_le hX0
  have hXr : X < (r : ℝ) + 1 := Nat.lt_floor_add_one X
  have hkr : k ≤ r := (Nat.le_floor_iff hX0).mpr (by linarith only [hX4k, hkR])
  have h2kr : 2 * k ≤ r := (Nat.le_floor_iff hX0).mpr (by
    push_cast
    linarith only [hX4k, hkR])
  have hsize : (B / 4) * ((r : ℝ) + 1) ≤ (N : ℝ) - r := by
    have hr2 : (r : ℝ) + 1 ≤ 2 * X := by linarith only [hrle, hX1]
    calc
      _ ≤ (B / 4) * (2 * X) := mul_le_mul_of_nonneg_left hr2 (by positivity)
      _ = (B / 2) * X := by ring
      _ ≤ (B - 1) * X := mul_le_mul_of_nonneg_right (by linarith only [hB4]) hX0
      _ ≤ _ := by nlinarith only [hNBX, hrle]
  have hremaining : X / 4 ≤ ((r + 1 - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ r + 1), Nat.cast_add, Nat.cast_one]
    linarith only [hXr, hX4k, hX0]
  exact ⟨hX1, hXpow, hkr, Nat.le_succ_of_le h2kr, hsize, hremaining⟩

theorem jw_query_threshold_ge_four_k (k : ℕ) (hk : 1 ≤ k) :
    4 * (k : ℝ) ≤ 32 * Real.pi ^ 2 * ((k : ℝ) ^ 3) *
      (2 ^ (k + 4)) * (k + 1) * k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith only [Real.pi_gt_three]
  have hk3 : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hkR
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 4) := one_le_pow₀ (by norm_num)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith only [hkR]
  have hprod := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hp hk3) htwo) hk1
  have h := mul_le_mul_of_nonneg_right hprod (by positivity : (0 : ℝ) ≤ 32 * k)
  have hlarge : (32 : ℝ) * k ≤ 32 * Real.pi ^ 2 * ((k : ℝ) ^ 3) *
      (2 ^ (k + 4)) * (k + 1) * k := by
    convert! h using 1 <;> ring
  linarith only [hlarge, hkR]

end Qatlib.Concepts.WalkFind.UniqueCollision
