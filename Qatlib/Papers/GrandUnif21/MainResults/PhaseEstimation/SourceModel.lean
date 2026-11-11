/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# GrandUnif21 Sec. V / Appendix B: binary phase estimation model

Source: arXiv:2105.02859v3, Sec. V A 2 (Algorithm 3, "phase estimation by
QSVT") and Appendix B, Eqs. (B1)--(B9), (B13)--(B18).

The inner loop of the paper's phase-estimation algorithm maintains a phase
`θ` and processes the binary digits `φ₁ φ₂ … φₙ` of the target phase
`Φ = 0.φ₁…φₙ`, one iteration `j = 0, …, n-1` at a time, each step doubling the
current value and setting the next binary digit (`θ ← φ_{j+1}/2 + θ/2`).  At
the end of iteration `j` the register holds `θ = 0.φ_{j+1}…φₙ` (Lemma 11);
when the phase is not representable with `n` bits the value is the nearest
`n`-bit number, i.e. a rounding step to `n-j` binary places (Lemma 12).

This file fixes the numerical vocabulary shared by the paper-layer theorems
for claims `c005`--`c011`:

* `bitVal` / `binFrac` / `tailFrac` — the binary fraction `0.φ₁…φ_L` and the
  contiguous tail `0.φ[j+1:]`;
* `thetaIter` — the actual halving recursion of the algorithm;
* `roundDyadic` — rounding to the nearest multiple of `2^{-K}` (the paper's
  `r̃_j.φ̃[j+1:]`, nearest-dyadic rounding, ties upward).

Boundary: this is the arithmetic skeleton only.  The QSVT sign function, the
`Δ`-region (Theorem 8 / Lemma 13) and the measurement model are layered on top
in `SourceTheorem08.lean` and `SourceLemma13.lean`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation

/-- The `i`-th binary digit, as a real number (`0` or `1`). -/
def bitVal (φ : ℕ → Bool) (i : ℕ) : ℝ := if φ i then 1 else 0

/-- The binary fraction `0.φ₁φ₂…φ_L = ∑_{i<L} φ_{i+1} 2^{-(i+1)}`
(paper notation `0.φ[1:]`, Appendix B). -/
def binFrac (φ : ℕ → Bool) (L : ℕ) : ℝ :=
  ∑ i ∈ Finset.range L, bitVal φ (i + 1) / (2 : ℝ) ^ (i + 1)

/-- The tail `0.φ_{j+1}…φ_n` of a phase whose first `j` digits have already
been processed (paper notation `0.φ[j+1:]`, Appendix B). -/
def tailFrac (φ : ℕ → Bool) (j n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n - j), bitVal φ (j + i + 1) / (2 : ℝ) ^ (i + 1)

/-- The algorithm's inner loop: `k` halving/bit-setting steps starting from the
deep end of the digit string.  With `k = n - j` this is the value held at the
end of iteration `j` (Appendix B, Eqs. (B2)--(B6)). -/
def thetaIter (φ : ℕ → Bool) (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => bitVal φ (n - k) / 2 + thetaIter φ n k / 2

/-- Round `x` to the nearest multiple of `2^{-K}`; ties round upward.  This is
the paper's `r̃_j.φ̃[j+1:]` (nearest-dyadic rounding to `n-j` binary places,
Appendix B, Lemma 12). -/
def roundDyadic (K : ℕ) (x : ℝ) : ℝ :=
  (⌊x * (2 : ℝ) ^ K + 1 / 2⌋ : ℝ) / (2 : ℝ) ^ K

/-! ### Binary digits -/

/-- A binary digit is nonnegative. -/
lemma bitVal_nonneg (φ : ℕ → Bool) (i : ℕ) : 0 ≤ bitVal φ i := by
  unfold bitVal
  split <;> norm_num

/-- A binary digit is at most one. -/
lemma bitVal_le_one (φ : ℕ → Bool) (i : ℕ) : bitVal φ i ≤ 1 := by
  unfold bitVal
  split <;> norm_num

/-- Splitting the first `j` digits off a binary fraction: the remaining digits
are the scaled tail `2^{-j}·0.φ[j+1:]`. -/
lemma binFrac_split (φ : ℕ → Bool) {j n : ℕ} (hj : j ≤ n) :
    binFrac φ n = binFrac φ j +
      ∑ i ∈ Finset.range (n - j), bitVal φ (j + i + 1) / (2 : ℝ) ^ (j + i + 1) := by
  have h := Finset.sum_range_add
    (fun i => bitVal φ (i + 1) / (2 : ℝ) ^ (i + 1)) j (n - j)
  rw [Nat.add_sub_cancel' hj] at h
  unfold binFrac
  rw [h]

/-- Lemma 11 closed form: the tail `0.φ[j+1:]` is `2^j` times the remainder of
the phase after its first `j` digits. -/
theorem tailFrac_eq (φ : ℕ → Bool) {j n : ℕ} (hj : j ≤ n) :
    tailFrac φ j n = (2 : ℝ) ^ j * (binFrac φ n - binFrac φ j) := by
  have hsplit := binFrac_split φ hj
  unfold tailFrac
  rw [hsplit, add_sub_cancel_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h2 : (2 : ℝ) ^ (j + i + 1) = (2 : ℝ) ^ j * (2 : ℝ) ^ (i + 1) := by
    rw [show j + i + 1 = j + (i + 1) by omega, pow_add]
  rw [h2]
  field_simp

/-- One halving/bit-setting step: the tail beginning at `j` is the `j+1`-st
digit over `2` plus half of the tail beginning at `j+1`.  This is the update
rule actually executed by the algorithm (Appendix B, Eqs. (B2)--(B6)). -/
theorem tailFrac_recurrence (φ : ℕ → Bool) {j n : ℕ} (hj : j < n) :
    tailFrac φ j n = bitVal φ (j + 1) / 2 + tailFrac φ (j + 1) n / 2 := by
  rw [tailFrac_eq φ (j := j) (n := n) (le_of_lt hj),
    tailFrac_eq φ (j := j + 1) (n := n) (by omega)]
  have hbf : binFrac φ (j + 1) = binFrac φ j + bitVal φ (j + 1) / (2 : ℝ) ^ (j + 1) := by
    unfold binFrac
    rw [Finset.sum_range_succ]
  rw [hbf]
  have h2 : (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ j * 2 := pow_succ 2 j
  have hpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  rw [h2]
  field_simp
  ring

/-- Lemma 11 (paper, Appendix B, Eq. (B9) special case): the value produced by
the algorithm's halving recursion after `n-j` steps is exactly the binary
fraction of the remaining digits, `θ_j = 0.φ[j+1:]`. -/
theorem thetaIter_eq_tailFrac (φ : ℕ → Bool) (n : ℕ) :
    ∀ k ≤ n, thetaIter φ n k = tailFrac φ (n - k) n := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [thetaIter, tailFrac]
  | succ k ih =>
    intro hk
    have hk' : k ≤ n := by omega
    rw [thetaIter, ih hk']
    have hidx : n - (k + 1) = n - k - 1 := by omega
    rw [hidx, tailFrac_recurrence φ (j := n - k - 1) (n := n) (by omega)]
    have hbit : n - k - 1 + 1 = n - k := by omega
    rw [hbit]

/-- Lemma 11, closed form at the end of iteration `j`: the algorithm's value is
`2^j (φ - 0.φ[1:j])`, i.e. `θ_j = 0.φ[j+1:]` (paper Appendix B, Eq. (B9)). -/
theorem thetaIter_eq (φ : ℕ → Bool) {j n : ℕ} (hj : j ≤ n) :
    thetaIter φ n (n - j) = (2 : ℝ) ^ j * (binFrac φ n - binFrac φ j) := by
  have hjj : n - (n - j) = j := by omega
  rw [thetaIter_eq_tailFrac φ n (n - j) (by omega), hjj, tailFrac_eq φ hj]

/-- If all digits beyond `m` vanish, the `n`-digit fraction agrees with the
`m`-digit fraction (`n ≥ m`).  This is the exactness behind Theorem 6: the
algorithm adds no error when the phase is representable. -/
theorem binFrac_eq_of_bits_zero {φ : ℕ → Bool} {m n : ℕ} (hmn : m ≤ n)
    (hbits : ∀ i, m < i → φ i = false) : binFrac φ n = binFrac φ m := by
  have hsplit := binFrac_split φ hmn
  rw [hsplit]
  have hzero :
      ∑ i ∈ Finset.range (n - m), bitVal φ (m + i + 1) / (2 : ℝ) ^ (m + i + 1) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hgt : m < m + i + 1 := by omega
    unfold bitVal
    rw [hbits (m + i + 1) hgt]
    norm_num
  rw [hzero, add_zero]

/-! ### Nearest-dyadic rounding -/

/-- Rounding to the nearest `K`-bit number is exact on `K`-bit numbers. -/
theorem roundDyadic_eq_of_int {K : ℕ} {x : ℝ} {N : ℤ}
    (hN : x * (2 : ℝ) ^ K = (N : ℝ)) : roundDyadic K x = x := by
  unfold roundDyadic
  have hpos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have hfl : ⌊x * (2 : ℝ) ^ K + 1 / 2⌋ = N := by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · linarith
    · linarith
  rw [hfl, div_eq_iff (ne_of_gt hpos)]
  linarith

/-- Nearest-dyadic rounding error: at most half a unit in the last place,
`|θ - x| ≤ 2^{-(K+1)}` (paper Lemma 12 / Theorem 7, Appendix B). -/
theorem abs_roundDyadic_sub_le (K : ℕ) (x : ℝ) :
    |roundDyadic K x - x| ≤ 1 / (2 : ℝ) ^ (K + 1) := by
  unfold roundDyadic
  set N : ℤ := ⌊x * (2 : ℝ) ^ K + 1 / 2⌋ with hN
  have hpos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have h1 : (N : ℝ) ≤ x * (2 : ℝ) ^ K + 1 / 2 := hN ▸ Int.floor_le _
  have h2 : x * (2 : ℝ) ^ K + 1 / 2 < (N : ℝ) + 1 := hN ▸ Int.lt_floor_add_one _
  have habs : |(N : ℝ) - x * (2 : ℝ) ^ K| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have heq : (N : ℝ) / (2 : ℝ) ^ K - x = ((N : ℝ) - x * (2 : ℝ) ^ K) / (2 : ℝ) ^ K := by
    field_simp
  rw [heq, abs_div, abs_of_pos hpos]
  calc |(N : ℝ) - x * (2 : ℝ) ^ K| / (2 : ℝ) ^ K
      ≤ (1 / 2) / (2 : ℝ) ^ K := by gcongr
    _ = 1 / (2 : ℝ) ^ (K + 1) := by
        rw [pow_succ]
        field_simp

end Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation
