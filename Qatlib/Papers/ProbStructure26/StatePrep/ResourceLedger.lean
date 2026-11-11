/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Recursive data and layerwise resource ledger

Formal core of Lemma S1 and of the resource half of Theorem 1 of *Harnessing
problem structure for end-to-end quantum speed-ups* (arXiv:2609.40105v1),
Supplementary Section II.1–II.3 (Eq. (S10), (S17), (S18)).

The paper bounds the records of a balanced split tree by following one
root-to-block path.  If every block of size `m` carries at most `C · m^d`
interface records (`Λ(I) = O(|I|^d)`, the definition of the recursive expansion
dimension `d`), then a block at depth `t` inherits at most
`1 + C · Σ_{s<t} m_s^d` records, and the geometric decay `m_s = 2^{h-s}` keeps
this bound `O(n^d)`.  Summing over the `O(n)` blocks of the physical tree gives
`O(n^{d+1})` records for `d > 0` and `O(n log n)` for `d = 0` (Lemma S1).

At the same time each block's `Λ` updates have depth and gate count `O(m)`, so
the recursion layer at depth `t` contributes depth `O(m_t^{d+1})` (disjoint
blocks run in parallel) and gate count `O(2^t · m_t^{d+1}) = O(n · m_t^d)`,
since `|I|^{d+1} ≤ m_t^d |I|` and the layer's blocks cover `n` variables.  The
geometric sums below reproduce the depth `O(n^{d+1})` and gate count
`O(n^{d+1} + n log n)` of Theorem 1 (Eq. (S17), Eq. (S18)).

All bounds are stated with explicit constants on a balanced bisection of `2^h`
variables, with `n = 2^h`; they are resource bounds, not gate-level synthesis.
-/

namespace Qatlib.Papers.ProbStructure26.StatePrep

open Finset

/-- Geometric series bound: `Σ_{s<t} r^s ≤ 2` whenever `0 ≤ r ≤ 1/2`. -/
theorem geom_sum_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (t : ℕ) :
    (∑ s ∈ Finset.range t, r ^ s) ≤ 2 := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    simp
  · have hne : r ≠ 1 := by linarith
    rw [geom_sum_eq hne]
    have hden : 0 < 1 - r := by linarith
    have hden' : r - 1 ≠ 0 := by linarith
    have hden1 : 1 - r ≠ 0 := by linarith
    have hrw : (r ^ t - 1) / (r - 1) = (1 - r ^ t) / (1 - r) := by
      rw [div_eq_div_iff hden' hden1]
      ring
    rw [hrw, div_le_iff₀ hden]
    nlinarith [pow_nonneg hr0 t, hr]

/-- Level block size: a balanced bisection of `2^h` variables has `2^h / 2^t`
variables per block at recursion depth `t`. -/
noncomputable def levelSize (h t : ℕ) : ℝ := (2 : ℝ) ^ h / 2 ^ t

/-- One layer of blocks covers the whole variable set: a layer's `2^t` blocks
of size `m_t` contain `2^h` variables in total. -/
theorem level_block_count_mul_size (h t : ℕ) :
    (2 : ℝ) ^ t * levelSize h t = (2 : ℝ) ^ h := by
  unfold levelSize
  field_simp

/-- The `d`-th power of a level block size factors into the root power and a
geometric factor. -/
theorem levelSize_pow_eq (h t d : ℕ) :
    levelSize h t ^ d = ((2 : ℝ) ^ h) ^ d * ((1 / 2 : ℝ) ^ d) ^ t := by
  unfold levelSize
  rw [div_pow, div_eq_mul_inv]
  have hinv : (((2 : ℝ) ^ t) ^ d)⁻¹ = ((1 / 2 : ℝ) ^ d) ^ t := by
    rw [← inv_pow, ← inv_pow, ← pow_mul, ← pow_mul]
    norm_num
    rw [mul_comm]
  rw [hinv]

/-- Per-level record masses decay geometrically: the sum of `m_t^d` over all
levels above a block is at most `2 · n^d`, the finite geometric sum of
Eq. (S17). -/
theorem level_pow_sum_le (h d t : ℕ) (hd : 1 ≤ d) :
    (∑ s ∈ Finset.range t, levelSize h s ^ d) ≤ 2 * ((2 : ℝ) ^ h) ^ d := by
  have hterm : ∀ s, levelSize h s ^ d = ((2 : ℝ) ^ h) ^ d * ((1 / 2 : ℝ) ^ d) ^ s :=
    fun s => levelSize_pow_eq h s d
  rw [Finset.sum_congr rfl (fun s _ => hterm s), ← Finset.mul_sum]
  have hr0 : 0 ≤ (1 / 2 : ℝ) ^ d := pow_nonneg (by norm_num) d
  have hr : (1 / 2 : ℝ) ^ d ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ d ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
      _ = 1 / 2 := by norm_num
  have hg := geom_sum_le_two hr0 hr t
  have hnh : 0 ≤ ((2 : ℝ) ^ h) ^ d := by positivity
  calc ((2 : ℝ) ^ h) ^ d * (∑ s ∈ Finset.range t, ((1 / 2 : ℝ) ^ d) ^ s)
      ≤ ((2 : ℝ) ^ h) ^ d * 2 := mul_le_mul_of_nonneg_left hg hnh
    _ = 2 * ((2 : ℝ) ^ h) ^ d := by ring

/-- Recursive record bound along one root-to-block path: level `t` adds the
`C · m_t^d` interface records of Eq. (S10). -/
noncomputable def recordBound (C : ℝ) (d h : ℕ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => recordBound C d h t + C * levelSize h t ^ d

/-- Closed form of the recursive record bound. -/
theorem recordBound_eq (C : ℝ) (d h t : ℕ) :
    recordBound C d h t = 1 + C * ∑ s ∈ Finset.range t, levelSize h s ^ d := by
  induction t with
  | zero => simp [recordBound]
  | succ t ih =>
      rw [recordBound, ih, Finset.sum_range_succ]
      ring

/-- Lemma S1, `d > 0` case along a path: a block at any depth inherits at most
`1 + 2 C n^d` records. -/
theorem recordBound_le (C : ℝ) (d h t : ℕ) (hC : 0 ≤ C) (hd : 1 ≤ d) :
    recordBound C d h t ≤ 1 + 2 * C * ((2 : ℝ) ^ h) ^ d := by
  rw [recordBound_eq]
  have hsum := level_pow_sum_le h d t hd
  nlinarith [mul_le_mul_of_nonneg_left hsum hC]

/-- The number of blocks in the first `h + 1` levels of a balanced binary tree
is at most `2^{h+1}`. -/
theorem sum_pow_two_range_le (h : ℕ) :
    (∑ t ∈ Finset.range (h + 1), (2 : ℝ) ^ t) ≤ (2 : ℝ) ^ (h + 1) := by
  induction h with
  | zero => norm_num
  | succ h ih =>
      rw [Finset.sum_range_succ]
      have hpow : (2 : ℝ) ^ (h + 1 + 1) = (2 : ℝ) ^ (h + 1) * 2 := pow_succ _ _
      have hle : (2 : ℝ) ^ (h + 1) ≤ (2 : ℝ) ^ (h + 1) := le_rfl
      rw [hpow]
      nlinarith [ih, pow_pos (by norm_num : (0:ℝ) < 2) (h + 1)]

/-- Lemma S1, `d > 0`: the whole balanced tree carries at most
`2 (1 + 2C) n^{d+1}` block and interface records, i.e. `O(n^{d+1})`. -/
theorem total_records_le (C : ℝ) (d h : ℕ) (hC : 0 ≤ C) (hd : 1 ≤ d) :
    (∑ t ∈ Finset.range (h + 1), (2 : ℝ) ^ t * recordBound C d h t) ≤
      2 * (1 + 2 * C) * ((2 : ℝ) ^ h) ^ (d + 1) := by
  have hterm : ∀ t ∈ Finset.range (h + 1),
      (2 : ℝ) ^ t * recordBound C d h t ≤
        (2 : ℝ) ^ t * (1 + 2 * C * ((2 : ℝ) ^ h) ^ d) := by
    intro t _
    exact mul_le_mul_of_nonneg_left (recordBound_le C d h t hC hd) (by positivity)
  calc (∑ t ∈ Finset.range (h + 1), (2 : ℝ) ^ t * recordBound C d h t)
      ≤ ∑ t ∈ Finset.range (h + 1), (2 : ℝ) ^ t * (1 + 2 * C * ((2 : ℝ) ^ h) ^ d) :=
        Finset.sum_le_sum hterm
    _ = (∑ t ∈ Finset.range (h + 1), (2 : ℝ) ^ t) *
          (1 + 2 * C * ((2 : ℝ) ^ h) ^ d) := by
        rw [Finset.sum_mul]
    _ ≤ (2 : ℝ) ^ (h + 1) * (1 + 2 * C * ((2 : ℝ) ^ h) ^ d) := by
        apply mul_le_mul_of_nonneg_right (sum_pow_two_range_le h)
        positivity
    _ ≤ 2 * (1 + 2 * C) * ((2 : ℝ) ^ h) ^ (d + 1) := by
        rw [pow_succ ((2 : ℝ) ^ h) d, pow_succ (2 : ℝ) h]
        have hpos : (0:ℝ) < (2 : ℝ) ^ h := pow_pos (by norm_num) h
        have hge1 : (1:ℝ) ≤ ((2 : ℝ) ^ h) ^ d :=
          one_le_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
        have hle : (2 : ℝ) ^ h ≤ ((2 : ℝ) ^ h) ^ d * (2 : ℝ) ^ h := by
          calc (2 : ℝ) ^ h = 1 * (2 : ℝ) ^ h := by ring
            _ ≤ ((2 : ℝ) ^ h) ^ d * (2 : ℝ) ^ h := by
                exact mul_le_mul_of_nonneg_right hge1 (le_of_lt hpos)
        nlinarith [hle, hpos, hC]

/-- Theorem 1, depth bound (Eq. (S17)): the layers of disjoint blocks run in
parallel, so the total depth is at most `2 C n^{d+1}`. -/
theorem depth_le (C : ℝ) (d h : ℕ) (hC : 0 ≤ C) :
    C * (∑ t ∈ Finset.range h, levelSize h t ^ (d + 1)) ≤
      2 * C * ((2 : ℝ) ^ h) ^ (d + 1) := by
  have hsum := level_pow_sum_le h (d + 1) h (Nat.succ_le_succ (Nat.zero_le d))
  nlinarith [mul_le_mul_of_nonneg_left hsum hC]

/-- Theorem 1, gate-count bound, `d > 0` (Eq. (S18)): a layer's blocks are
disjoint and contain `n` variables in total, so the layer costs
`C n m_t^d` gates and the geometric sum is at most `2 C n^{d+1}`. -/
theorem gate_le (C : ℝ) (d h : ℕ) (hC : 0 ≤ C) (hd : 1 ≤ d) :
    C * (∑ t ∈ Finset.range h, (2 : ℝ) ^ t * levelSize h t ^ (d + 1)) ≤
      2 * C * ((2 : ℝ) ^ h) ^ (d + 1) := by
  have hterm : ∀ t,
      (2 : ℝ) ^ t * levelSize h t ^ (d + 1) =
        levelSize h t ^ d * (2 : ℝ) ^ h := by
    intro t
    have hsplit : levelSize h t ^ (d + 1) = levelSize h t ^ d * levelSize h t :=
      pow_succ _ _
    rw [hsplit, ← mul_assoc, mul_comm ((2 : ℝ) ^ t) (levelSize h t ^ d),
      mul_assoc, level_block_count_mul_size]
  rw [Finset.sum_congr rfl (fun t _ => hterm t), ← Finset.sum_mul]
  have hsum := level_pow_sum_le h d h hd
  have hnh : 0 ≤ C := hC
  have h2h : (0:ℝ) ≤ (2 : ℝ) ^ h := by positivity
  calc C * ((∑ t ∈ Finset.range h, levelSize h t ^ d) * (2 : ℝ) ^ h)
      ≤ C * (2 * ((2 : ℝ) ^ h) ^ d * (2 : ℝ) ^ h) := by
        have := mul_le_mul_of_nonneg_right hsum h2h
        nlinarith [mul_le_mul_of_nonneg_left this hC]
    _ = 2 * C * ((2 : ℝ) ^ h) ^ (d + 1) := by
        rw [pow_succ]
        ring

/-- Lemma S1, `d = 0`: a block at depth `t` inherits at most `1 + C t`
records, because each level adds the constant `C`. -/
theorem recordBound_zero (C : ℝ) (h t : ℕ) : recordBound C 0 h t = 1 + C * t := by
  induction t with
  | zero => simp [recordBound]
  | succ t ih =>
      rw [recordBound, ih]
      simp only [levelSize, pow_zero]
      push_cast
      ring

/-- Lemma S1, `d = 0`: every one of the `n` blocks inherits `O(h)` records, so
the tree carries at most `2 (1 + C) n (h + 1)` records, i.e. `O(n log n)`. -/
theorem total_records_zero_le (C : ℝ) (h : ℕ) (hC : 0 ≤ C) :
    (∑ t ∈ Finset.range (h + 1), (2 : ℝ) ^ t * recordBound C 0 h t) ≤
      2 * (1 + C) * (2 : ℝ) ^ h * (h + 1) := by
  have hterm : ∀ t ∈ Finset.range (h + 1),
      (2 : ℝ) ^ t * recordBound C 0 h t ≤
        (2 : ℝ) ^ t * (1 + C * ((h + 1 : ℕ) : ℝ)) := by
    intro t ht
    rw [recordBound_zero]
    have ht' : (t : ℝ) ≤ ((h + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show t ≤ h + 1 by
        have := Finset.mem_range.mp ht
        omega)
    have hct : C * (t : ℝ) ≤ C * ((h + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left ht' hC
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc (∑ t ∈ Finset.range (h + 1), (2 : ℝ) ^ t * recordBound C 0 h t)
      ≤ ∑ t ∈ Finset.range (h + 1), (2 : ℝ) ^ t * (1 + C * ((h + 1 : ℕ) : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (∑ t ∈ Finset.range (h + 1), (2 : ℝ) ^ t) * (1 + C * ((h + 1 : ℕ) : ℝ)) := by
        rw [Finset.sum_mul]
    _ ≤ (2 : ℝ) ^ (h + 1) * (1 + C * ((h + 1 : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_right (sum_pow_two_range_le h)
        positivity
    _ ≤ 2 * (1 + C) * (2 : ℝ) ^ h * (h + 1) := by
        rw [pow_succ]
        have hK : (1:ℝ) ≤ ((h + 1 : ℕ) : ℝ) := by
          have : (1:ℕ) ≤ h + 1 := Nat.succ_le_succ (Nat.zero_le h)
          exact_mod_cast this
        have hkey : 1 + C * ((h + 1 : ℕ) : ℝ) ≤ (1 + C) * ((h + 1 : ℕ) : ℝ) := by
          nlinarith [hK]
        have hcast : ((h + 1 : ℕ) : ℝ) = (h : ℝ) + 1 := by push_cast; ring
        rw [hcast] at hkey
        have hmul := mul_le_mul_of_nonneg_left hkey
          (by positivity : (0:ℝ) ≤ 2 * (2 : ℝ) ^ h)
        push_cast
        nlinarith [hmul]

/-- Theorem 1, gate-count bound for `d = 0`: every one of the `h` layers costs
`C n` gates, giving the `n log n` term of Eq. (S18). -/
theorem gate_zero_le (C : ℝ) (h : ℕ) (hC : 0 ≤ C) :
    C * (∑ t ∈ Finset.range h, (2 : ℝ) ^ t * levelSize h t) ≤
      C * (2 : ℝ) ^ h * (h + 1) := by
  have hterm : ∀ t, (2 : ℝ) ^ t * levelSize h t = (2 : ℝ) ^ h :=
    fun t => level_block_count_mul_size h t
  rw [Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have hpos : (0:ℝ) < (2 : ℝ) ^ h := pow_pos (by norm_num) h
  have hh : ((h : ℕ) : ℝ) ≤ ((h + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ h
  nlinarith [hpos, hC, mul_nonneg (mul_nonneg hC (le_of_lt hpos)) (by positivity : (0:ℝ) ≤ ((h:ℕ):ℝ))]


/-- Lemma 1, balanced-recursion height: after `log2 n + 1` halvings a block of
`n` variables is empty, so a constructible balanced decomposition has height
`O(log n)`. -/
theorem levelSize_nat_eq_zero (n : ℕ) :
    n / 2 ^ (Nat.log2 n + 1) = 0 := by
  apply Nat.div_eq_of_lt
  exact Nat.lt_log2_self

/-- Lemma 1, the two-sided height bound: `2^{log2 n} ≤ n < 2^{log2 n + 1}`, so
the number of balanced bisection levels is `Θ(log n)`. -/
theorem levelSize_nat_bounds (n : ℕ) (hn : 1 ≤ n) :
    2 ^ Nat.log2 n ≤ n ∧ n < 2 ^ (Nat.log2 n + 1) :=
  ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

end Qatlib.Papers.ProbStructure26.StatePrep
