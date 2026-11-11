/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QInspired25.MainResults.Model.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Simulation — Theorem 10 of the coordinator model

Fixed source: arXiv:2402.15686v3, Theorem 10 (p. 6) and its proof (p. 6--7).

The theorem says: in the multi-player coordinator model, if player `P_i` holds the row
block `A^{(i)} ∈ ℝ^{ℓ_i×n}` and the vector block `b^{(i)} ∈ ℝ^{m_i}` with
`m = Σ_i ℓ_i = Σ_i m_i`, and all entries are specified by `O(log q)` bits, then

* the coordinator can use `SQ(b)` `O(T)` times with `O((T+k) log(qm))` bits;
* the coordinator can use `SQ(A)` `O(T)` times with `O((T+k) log(qmn))` bits.

The mathematical content is the *hierarchical sampler* of the proof: player `P_i` sends
`‖b^{(i)}‖` once (`O(k log(qm))` bits), the coordinator samples a block with probability
`‖b^{(i)}‖²/‖b‖²` and then asks `P_i` for a sample from `b^{(i)}`, which yields the direct
law `|b_j|²/‖b‖²` (`hierarchical_sample_prob` below).  Queries of entries cost
`O(log m)` (index) plus `O(log q)` (value) bits each.

This file records the *cost arithmetic* with explicit constants (`6` for vectors,
`12` for matrices) and the probability identity.  We do not model the players' internal
unbounded computation, exactly as the source does not count it.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QInspired25.MainResults.Simulation

open Qatlib.Papers.QInspired25.MainResults.Model

/-! ## §1. The hierarchical sampling identity -/

/-- Squared norm of a block vector, summed over the blocks. -/
def blockNormSq {k m : ℕ} (b : Fin k → Fin m → ℝ) : ℝ := ∑ i, frobSqVec (b i)

/-- Block squared norm equals the Frobenius norm of the block matrix. -/
theorem blockNormSq_eq_frobSqBlock {k m : ℕ} (b : Fin k → Fin m → ℝ) :
    blockNormSq b = frobSqBlock b := by
  unfold blockNormSq frobSqBlock frobSqVec
  rw [Finset.sum_comm]

/-- **Theorem 10, probability identity (p. 6).**  Sampling a block `i` with probability
`‖b^{(i)}‖²/‖b‖²` and then sampling `j` inside the block with probability
`|b^{(i)}_j|²/‖b^{(i)}‖²` gives exactly the direct law `|b^{(i)}_j|²/‖b‖²`, i.e. the
distribution of `SQ(b)` of Definition 2. -/
theorem hierarchical_sample_prob {k m : ℕ} (b : Fin k → Fin m → ℝ)
    (hnorm : blockNormSq b ≠ 0) (hrow : ∀ i, frobSqVec (b i) ≠ 0) (i : Fin k) (j : Fin m) :
    (frobSqVec (b i) / blockNormSq b) * (b i j ^ 2 / frobSqVec (b i)) =
      b i j ^ 2 / blockNormSq b := by
  have hi := hrow i
  field_simp

/-- The block law sums to one. -/
theorem hierarchical_sample_sum {k m : ℕ} (b : Fin k → Fin m → ℝ)
    (hnorm : blockNormSq b ≠ 0) (hrow : ∀ i, frobSqVec (b i) ≠ 0) :
    ∑ i, ∑ j, (frobSqVec (b i) / blockNormSq b) * (b i j ^ 2 / frobSqVec (b i)) = 1 := by
  have hterm : ∀ i, (∑ j, (frobSqVec (b i) / blockNormSq b) * (b i j ^ 2 / frobSqVec (b i)))
      = frobSqVec (b i) / blockNormSq b := by
    intro i
    rw [← Finset.mul_sum, ← Finset.sum_div]
    have : ∑ j : Fin m, b i j ^ 2 = frobSqVec (b i) := rfl
    rw [this]
    field_simp
  simp only [hterm]
  unfold blockNormSq
  rw [← Finset.sum_div]
  exact div_self hnorm

/-! ## §2. Bit-cost of the simulated accesses -/

/-- Bits for one simulated `SQ(b)` access: exchange an index (`log m`), an entry or a sample
(`log q` plus `log m`) in both directions, plus a constant slack. -/
def perVecAccessBits (q m : ℕ) : ℕ := 2 * logBits m + 2 * logBits q + 2

/-- Total bits for `T` simulated `SQ(b)` accesses and the `k` one-off norm messages. -/
def vecSimCost (T k q m : ℕ) : ℕ :=
  T * perVecAccessBits q m + k * (logBits (q * m) + logBits m)

/-- Bits for one simulated `SQ(A)` access (`log(qmn)` for a value, `log(mn)` for a position). -/
def perMatAccessBits (q m n : ℕ) : ℕ := 2 * logBits (q * m * n) + 2 * logBits (m * n) + 2

/-- Total bits for `T` simulated `SQ(A)` accesses and the `k` one-off norm messages. -/
def matSimCost (T k q m n : ℕ) : ℕ :=
  T * perMatAccessBits q m n + k * (2 * logBits (q * m * n) + logBits (m * n))

/-- A product of positive naturals has bit count at least one. -/
theorem one_le_logBits_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : 1 ≤ logBits (a * b) :=
  logBits_pos (Nat.mul_pos ha hb)

/-- **Theorem 10, `SQ(b)` clause (p. 6).**  `O(T)` uses of `SQ(b)` cost at most
`6 (T+k) log(qm)` bits. -/
theorem vecSimCost_le (T k q m : ℕ) (hm : 0 < m) (hq : 0 < q) :
    vecSimCost T k q m ≤ 6 * (T + k) * logBits (q * m) := by
  have hL : 1 ≤ logBits (q * m) := one_le_logBits_mul hq hm
  have hqL : logBits q ≤ logBits (q * m) :=
    logBits_mono (Nat.le_mul_of_pos_right q hm)
  have hmL : logBits m ≤ logBits (q * m) :=
    logBits_mono (by
      calc m = 1 * m := (one_mul m).symm
        _ ≤ q * m := Nat.mul_le_mul_right m hq)
  have hper : perVecAccessBits q m ≤ 6 * logBits (q * m) := by
    unfold perVecAccessBits
    omega
  have hone : logBits (q * m) + logBits m ≤ 2 * logBits (q * m) := by omega
  unfold vecSimCost
  calc T * perVecAccessBits q m + k * (logBits (q * m) + logBits m)
      ≤ T * (6 * logBits (q * m)) + k * (2 * logBits (q * m)) := by
        exact Nat.add_le_add (Nat.mul_le_mul_left T hper) (Nat.mul_le_mul_left k hone)
    _ ≤ 6 * (T + k) * logBits (q * m) := by
        nlinarith [Nat.zero_le T, Nat.zero_le k, Nat.zero_le (logBits (q * m))]

/-- **Theorem 10, `SQ(A)` clause (p. 6--7).**  `O(T)` uses of `SQ(A)` cost at most
`12 (T+k) log(qmn)` bits. -/
theorem matSimCost_le (T k q m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hq : 0 < q) :
    matSimCost T k q m n ≤ 12 * (T + k) * logBits (q * m * n) := by
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  have hL : 1 ≤ logBits (q * m * n) := by
    have h := one_le_logBits_mul (a := q) (b := m * n) hq hmn
    simpa [Nat.mul_assoc] using h
  have hmnL : logBits (m * n) ≤ logBits (q * m * n) := by
    apply logBits_mono
    calc m * n = 1 * (m * n) := (one_mul _).symm
      _ ≤ q * (m * n) := Nat.mul_le_mul_right _ hq
      _ = q * m * n := by ring
  have hper : perMatAccessBits q m n ≤ 12 * logBits (q * m * n) := by
    unfold perMatAccessBits
    omega
  have hone : 2 * logBits (q * m * n) + logBits (m * n) ≤ 3 * logBits (q * m * n) := by omega
  unfold matSimCost
  calc T * perMatAccessBits q m n + k * (2 * logBits (q * m * n) + logBits (m * n))
      ≤ T * (12 * logBits (q * m * n)) + k * (3 * logBits (q * m * n)) := by
        exact Nat.add_le_add (Nat.mul_le_mul_left T hper) (Nat.mul_le_mul_left k hone)
    _ ≤ 12 * (T + k) * logBits (q * m * n) := by
        nlinarith [Nat.zero_le T, Nat.zero_le k, Nat.zero_le (logBits (q * m * n))]

end Qatlib.Papers.QInspired25.MainResults.Simulation
