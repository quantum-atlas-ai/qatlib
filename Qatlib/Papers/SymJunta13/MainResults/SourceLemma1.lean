/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option backward.isDefEq.respectTransparency false

/-!
# SymJunta13.MainResults — the binomial estimate of Lemma 1

Belovs, *Quantum Algorithms for Learning Symmetric Juntas via the Adversary Bound*,
fixed arXiv:1311.6777v3, Section 2, Lemma 1 (printed p. 4).

The paper states: if `n` and `k` are positive integers with `k = O(√n)`, then
`C(n, ⌊n/2⌋ ± k) = Θ(2^n/√n)`.  Later estimates in the paper instantiate this lemma, so it is
recorded here as the paper-layer bridge for that claim.

The proof is elementary and does not use Stirling's formula.  Two ingredients are combined:

* the central binomial coefficient satisfies `4^m/(2√m) ≤ C(2m,m) ≤ 4^m/√(2m+1)` for `m ≥ 1`,
  proved by induction from `(m+1) C(2m+2,m+1) = 2(2m+1) C(2m,m)`
  (`Nat.succ_mul_centralBinom_succ`) after squaring;
* moving the weight `k` steps away from the middle multiplies the coefficient by at most
  `exp(8k²/n)`, because `C(n,j)/C(n,j+1) = (j+1)/(n-j) ≤ 1 + (8k+4)/n` while `k ≤ n/4`, and
  `1 + x ≤ exp x`.

Together these give the paper's `Θ(2^n/√n)` with explicit constants depending only on the
`O(√n)` constant of `k`.  The final lemma in the file records the `κ₀` weight `Θ(k^{-1/2})` that
Sections 5 and 6 obtain from Lemma 1.
-/

set_option autoImplicit false
noncomputable section

open Real

namespace Qatlib.Papers.SymJunta13.MainResults

/-- The defining recurrence of the central binomial coefficient, cast to `ℝ`. -/
theorem centralBinom_succ_cast (m : ℕ) :
    ((m : ℝ) + 1) * (Nat.centralBinom (m + 1) : ℝ) =
      2 * (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) := by
  have h := Nat.succ_mul_centralBinom_succ m
  have h' : (((m + 1) * Nat.centralBinom (m + 1) : ℕ) : ℝ) =
      ((2 * (2 * m + 1) * Nat.centralBinom m : ℕ) : ℝ) := by rw [h]
  push_cast at h' ⊢
  linarith

/-- Key squared recurrence: `(m+1)² C(2m+2,m+1)² = 4 (2m+1)² C(2m,m)²`. -/
theorem centralBinom_succ_sq (m : ℕ) :
    ((m : ℝ) + 1) ^ 2 * (Nat.centralBinom (m + 1) : ℝ) ^ 2 =
      4 * (2 * (m : ℝ) + 1) ^ 2 * (Nat.centralBinom m : ℝ) ^ 2 := by
  have h := centralBinom_succ_cast m
  have h' := congrArg (fun x : ℝ => x ^ 2) h
  nlinarith [h']

/-- Upper half of the central binomial two-sided bound, in squared form:
`C(2m,m)² (2m+1) ≤ 16^m`. -/
theorem centralBinom_sq_mul_le (m : ℕ) :
    (Nat.centralBinom m : ℝ) ^ 2 * (2 * (m : ℝ) + 1) ≤ 16 ^ m := by
  induction m with
  | zero => norm_num [Nat.centralBinom]
  | succ n ih =>
    have hstep := centralBinom_succ_sq n
    have hkey : ((n : ℝ) + 1) ^ 2 *
        ((Nat.centralBinom (n + 1) : ℝ) ^ 2 * (2 * (n : ℝ) + 3)) =
        ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) *
          (4 * ((Nat.centralBinom n : ℝ) ^ 2 * (2 * (n : ℝ) + 1))) := by
      nlinarith [hstep]
    have hcoef : (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) ≤ 4 * ((n : ℝ) + 1) ^ 2 := by
      nlinarith
    have hnonneg : (0 : ℝ) ≤ (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) := by positivity
    have h16 : (0 : ℝ) ≤ (16 : ℝ) ^ n := (pow_pos (by norm_num) n).le
    have hmain : ((n : ℝ) + 1) ^ 2 *
        ((Nat.centralBinom (n + 1) : ℝ) ^ 2 * (2 * (n : ℝ) + 3)) ≤
        ((n : ℝ) + 1) ^ 2 * (16 : ℝ) ^ (n + 1) := by
      calc ((n : ℝ) + 1) ^ 2 * ((Nat.centralBinom (n + 1) : ℝ) ^ 2 * (2 * (n : ℝ) + 3))
          = ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) *
              (4 * ((Nat.centralBinom n : ℝ) ^ 2 * (2 * (n : ℝ) + 1))) := hkey
        _ ≤ ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) * (4 * (16 : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left (by linarith [ih]) hnonneg
        _ = ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) * 4) * (16 : ℝ) ^ n := by ring
        _ ≤ (16 * ((n : ℝ) + 1) ^ 2) * (16 : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right (by nlinarith) h16
        _ = ((n : ℝ) + 1) ^ 2 * (16 : ℝ) ^ (n + 1) := by
            rw [pow_succ]; ring
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    have hgoal : ((n : ℝ) + 1) ^ 2 *
        ((Nat.centralBinom (n + 1) : ℝ) ^ 2 * (2 * ((n : ℝ) + 1) + 1)) ≤
        ((n : ℝ) + 1) ^ 2 * (16 : ℝ) ^ (n + 1) := by
      have : 2 * ((n : ℝ) + 1) + 1 = 2 * (n : ℝ) + 3 := by ring
      rw [this]; exact hmain
    exact (mul_le_mul_iff_of_pos_left hpos).mp (by push_cast; exact hgoal)

/-- Lower half of the central binomial two-sided bound, in squared form:
`16^m ≤ C(2m,m)² (4m)`. -/
theorem centralBinom_sq_ge (m : ℕ) (hm : 1 ≤ m) :
    (16 : ℝ) ^ m ≤ (Nat.centralBinom m : ℝ) ^ 2 * (4 * (m : ℝ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  clear hm
  induction k with
  | zero => norm_num [Nat.centralBinom]
  | succ j ih =>
    push_cast at ih ⊢
    have hstep := centralBinom_succ_sq (j + 1)
    push_cast at hstep
    have hsq : ((j : ℝ) + 1 + 1) ^ 2 *
        ((Nat.centralBinom (j + 1 + 1) : ℝ) ^ 2 * (4 * ((j : ℝ) + 1 + 1))) =
        16 * ((j : ℝ) + 1 + 1) * (2 * ((j : ℝ) + 1) + 1) ^ 2 *
          (Nat.centralBinom (j + 1) : ℝ) ^ 2 := by
      rw [show ((j : ℝ) + 1 + 1) ^ 2 *
          ((Nat.centralBinom (j + 1 + 1) : ℝ) ^ 2 * (4 * ((j : ℝ) + 1 + 1))) =
          4 * ((j : ℝ) + 1 + 1) *
            (((j : ℝ) + 1 + 1) ^ 2 * (Nat.centralBinom (j + 1 + 1) : ℝ) ^ 2) from by ring]
      rw [hstep]
      ring
    have h16 : (16 : ℝ) ^ (j + 1 + 1) = 16 * (16 : ℝ) ^ (j + 1) := by rw [pow_succ]; ring
    have hcoef : 4 * ((j : ℝ) + 1) * ((j : ℝ) + 1 + 1) ≤ (2 * ((j : ℝ) + 1) + 1) ^ 2 := by
      nlinarith
    have hpos : (0 : ℝ) < ((j : ℝ) + 1 + 1) ^ 2 := by positivity
    have h1 : (0 : ℝ) ≤ ((j : ℝ) + 1 + 1) := by positivity
    have h2 := mul_le_mul_of_nonneg_right ih h1
    have hC : (0 : ℝ) ≤ (Nat.centralBinom (j + 1) : ℝ) ^ 2 := by positivity
    refine (mul_le_mul_iff_of_pos_left hpos).mp ?_
    rw [hsq]
    nlinarith [h2, hcoef, h16, hC]

/-- Upper bound `C(2m,m) ≤ 4^m/√(2m+1)`. -/
theorem centralBinom_le_four_pow_div_sqrt (m : ℕ) (hm : 1 ≤ m) :
    (Nat.centralBinom m : ℝ) ≤ (4 : ℝ) ^ m / Real.sqrt (2 * (m : ℝ) + 1) := by
  have hC : (0 : ℝ) ≤ (Nat.centralBinom m : ℝ) := by positivity
  have hb : (0 : ℝ) ≤ (4 : ℝ) ^ m / Real.sqrt (2 * (m : ℝ) + 1) := by positivity
  have hsq : (Nat.centralBinom m : ℝ) ^ 2 ≤
      ((4 : ℝ) ^ m / Real.sqrt (2 * (m : ℝ) + 1)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * (m : ℝ) + 1)]
    have h16 : ((4 : ℝ) ^ m) ^ 2 = (16 : ℝ) ^ m := by
      rw [← pow_mul (4 : ℝ) m 2, show (16 : ℝ) = (4 : ℝ) ^ 2 by norm_num, ← pow_mul (4 : ℝ) 2 m,
        Nat.mul_comm]
    rw [h16]
    exact (le_div_iff₀ (by positivity : (0:ℝ) < 2 * (m : ℝ) + 1)).mpr (centralBinom_sq_mul_le m)
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg hC, abs_of_nonneg hb] at h

/-- Lower bound `4^m/(2√m) ≤ C(2m,m)`. -/
theorem four_pow_div_two_sqrt_le_centralBinom (m : ℕ) (hm : 1 ≤ m) :
    (4 : ℝ) ^ m / (2 * Real.sqrt (m : ℝ)) ≤ (Nat.centralBinom m : ℝ) := by
  have hC : (0 : ℝ) ≤ (Nat.centralBinom m : ℝ) := by positivity
  have hb : (0 : ℝ) ≤ (4 : ℝ) ^ m / (2 * Real.sqrt (m : ℝ)) := by positivity
  have hsq : ((4 : ℝ) ^ m / (2 * Real.sqrt (m : ℝ))) ^ 2 ≤
      (Nat.centralBinom m : ℝ) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (m : ℝ)),
      show (2:ℝ) ^ 2 = 4 by norm_num]
    have h16 : ((4 : ℝ) ^ m) ^ 2 = (16 : ℝ) ^ m := by
      rw [← pow_mul (4 : ℝ) m 2, show (16 : ℝ) = (4 : ℝ) ^ 2 by norm_num, ← pow_mul (4 : ℝ) 2 m,
        Nat.mul_comm]
    rw [h16]
    exact (div_le_iff₀ (by positivity : (0:ℝ) < 4 * (m:ℝ))).mpr (centralBinom_sq_ge m hm)
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg hC, abs_of_nonneg hb] at h

/-- Middle-weight two-sided bound: `(1/4) 2^n/√n ≤ C(n,⌊n/2⌋) ≤ 2^n/√n`. -/
theorem choose_middle_bounds (n : ℕ) (hn : 1 ≤ n) :
    (1 / 4) * (2 : ℝ) ^ n / Real.sqrt (n : ℝ) ≤ (n.choose (n / 2) : ℝ) ∧
      (n.choose (n / 2) : ℝ) ≤ (2 : ℝ) ^ n / Real.sqrt (n : ℝ) := by
  rcases Nat.even_or_odd n with hev | hod
  · obtain ⟨m, rfl⟩ := hev
    push_cast
    have hm1 : 1 ≤ m := by omega
    have hmn : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hhalf : (m + m) / 2 = m := by omega
    have hC : ((m + m).choose ((m + m) / 2) : ℝ) = (Nat.centralBinom m : ℝ) := by
      rw [hhalf, Nat.centralBinom, Nat.two_mul]
    have h4 : (4 : ℝ) ^ m = (2 : ℝ) ^ (m + m) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, ← Nat.two_mul]
    have hsqrt1 : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) + m) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsqrt2 : Real.sqrt ((m : ℝ) + m) ≤ Real.sqrt (2 * (m : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have hpos : (0 : ℝ) < Real.sqrt ((m : ℝ) + m) := Real.sqrt_pos.mpr (by positivity)
    have hposm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by positivity)
    constructor
    · rw [hC, ← h4]
      have hlow := four_pow_div_two_sqrt_le_centralBinom m hm1
      have hstep : (1 / 4) * (4 : ℝ) ^ m / Real.sqrt ((m : ℝ) + m) ≤
          (4 : ℝ) ^ m / (2 * Real.sqrt (m : ℝ)) := by
        rw [show (1 / 4) * (4 : ℝ) ^ m / Real.sqrt ((m : ℝ) + m)
            = (4 : ℝ) ^ m / (4 * Real.sqrt ((m : ℝ) + m)) by ring]
        gcongr
        nlinarith [hsqrt1]
      linarith
    · rw [hC, ← h4]
      have hup := centralBinom_le_four_pow_div_sqrt m hm1
      have hstep : (4 : ℝ) ^ m / Real.sqrt (2 * (m : ℝ) + 1) ≤
          (4 : ℝ) ^ m / Real.sqrt ((m : ℝ) + m) := by
        gcongr
      linarith
  · obtain ⟨m, rfl⟩ := hod
    push_cast
    have hmn : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hhalf : (2 * m + 1) / 2 = m := by omega
    rw [hhalf]
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      norm_num
    · have hrec : (2 * m + 1).choose m = (2 * m).choose (m - 1) + (2 * m).choose m := by
        have h := Nat.choose_succ_succ (2 * m) (m - 1)
        rw [show (2 * m).succ = 2 * m + 1 from rfl,
          show (m - 1).succ = m by omega] at h
        exact h
      have hle : (2 * m).choose (m - 1) ≤ (Nat.centralBinom m) := by
        have h := Nat.choose_le_middle (m - 1) (2 * m)
        rw [show (2 * m) / 2 = m by omega] at h
        simpa [Nat.centralBinom, Nat.two_mul] using h
      have hnn : (((2 * m).choose (m - 1) : ℕ) : ℝ) ≤ (Nat.centralBinom m : ℝ) := by
        exact_mod_cast hle
      have hmc : (Nat.centralBinom m : ℝ) = ((2 * m).choose m : ℝ) := by
        simp [Nat.centralBinom, Nat.two_mul]
      have hC : (((2 * m + 1).choose m : ℕ) : ℝ) ≤ 2 * (Nat.centralBinom m : ℝ) := by
        rw [hrec]
        push_cast
        linarith
      have hCge : (Nat.centralBinom m : ℝ) ≤ (((2 * m + 1).choose m : ℕ) : ℝ) := by
        rw [hrec]
        push_cast
        have h0 : (0 : ℝ) ≤ (((2 * m).choose (m - 1) : ℕ) : ℝ) := by positivity
        linarith
      have h4 : 2 * (4 : ℝ) ^ m = (2 : ℝ) ^ (2 * m + 1) := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul,
          show (2 : ℝ) ^ (2 * m + 1) = 2 * (2 : ℝ) ^ (2 * m) by rw [pow_succ]; ring]
      have hsqrt : Real.sqrt (m : ℝ) ≤ Real.sqrt (2 * (m : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      constructor
      · have hlow := four_pow_div_two_sqrt_le_centralBinom m hmpos
        have hstep : (1 / 4) * (2 : ℝ) ^ (2 * m + 1) / Real.sqrt (2 * (m : ℝ) + 1) ≤
            (4 : ℝ) ^ m / (2 * Real.sqrt (m : ℝ)) := by
          rw [show (1 / 4) * (2 : ℝ) ^ (2 * m + 1) = (1 / 2) * (4 : ℝ) ^ m by
              rw [← h4]; ring,
            show (1 / 2) * (4 : ℝ) ^ m / Real.sqrt (2 * (m : ℝ) + 1)
              = (4 : ℝ) ^ m / (2 * Real.sqrt (2 * (m : ℝ) + 1)) by ring]
          gcongr
        linarith
      · have hup := centralBinom_le_four_pow_div_sqrt m hmpos
        have hstep : 2 * ((4 : ℝ) ^ m / Real.sqrt (2 * (m : ℝ) + 1)) =
            (2 : ℝ) ^ (2 * m + 1) / Real.sqrt (2 * (m : ℝ) + 1) := by
          rw [show 2 * ((4 : ℝ) ^ m / Real.sqrt (2 * (m : ℝ) + 1))
              = (2 * (4 : ℝ) ^ m) / Real.sqrt (2 * (m : ℝ) + 1) by ring, ← h4]
        linarith

/-- One step of the ratio recurrence, cast to `ℝ`: `C(n,j) (n-j) = C(n,j+1) (j+1)`. -/
theorem choose_mul_sub_cast {n j : ℕ} (hj : j ≤ n) :
    (n.choose j : ℝ) * ((n : ℝ) - (j : ℝ)) = (n.choose (j + 1) : ℝ) * ((j : ℝ) + 1) := by
  have h := Nat.choose_succ_right_eq n j
  have h' : (((n.choose (j + 1)) * (j + 1) : ℕ) : ℝ) = (((n.choose j) * (n - j) : ℕ) : ℝ) := by
    rw [h]
  push_cast at h'
  rw [Nat.cast_sub hj] at h'
  linarith

/-- Moving `k` steps up from the middle multiplies the binomial coefficient by at most
`exp (8 k²/n)`, as long as `4 k ≤ n`. -/
theorem choose_up_shift (n : ℕ) :
    ∀ k : ℕ, 4 * k ≤ n →
      (n.choose (n / 2) : ℝ) ≤
        Real.exp (8 * (k : ℝ) ^ 2 / (n : ℝ)) * (n.choose (n / 2 + k) : ℝ) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : 4 * k ≤ n := by omega
    have ihb := ih hk'
    have hn : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    set j : ℕ := n / 2 + k with hjdef
    have hjle : j ≤ n := by omega
    have hjpos : j + 1 ≤ n := by omega
    have hden : (n : ℝ) / 4 ≤ (n : ℝ) - (j : ℝ) := by
      have hnat : n ≤ 4 * (n - j) := by omega
      have hcast : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub hjle
      have : (n : ℝ) ≤ 4 * ((n - j : ℕ) : ℝ) := by exact_mod_cast hnat
      rw [hcast] at this
      linarith
    have hdenpos : (0 : ℝ) < (n : ℝ) - (j : ℝ) := by linarith
    have hnum : 2 * (j : ℝ) + 1 - (n : ℝ) ≤ 2 * (k : ℝ) + 1 := by
      have h2 : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
        have := Nat.div_mul_le_self n 2
        have : (((n / 2) * 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
        push_cast at this
        linarith
      have hjcast : (j : ℝ) = ((n / 2 : ℕ) : ℝ) + (k : ℝ) := by rw [hjdef]; push_cast; ring
      rw [hjcast]
      linarith
    have hratio : ((j : ℝ) + 1) / ((n : ℝ) - (j : ℝ)) ≤ 1 + (8 * (k : ℝ) + 4) / (n : ℝ) := by
      rw [div_le_iff₀ hdenpos]
      have h1 : (1 + (8 * (k : ℝ) + 4) / (n : ℝ)) * ((n : ℝ) - (j : ℝ)) =
          ((n : ℝ) - (j : ℝ)) + ((n : ℝ) - (j : ℝ)) * (8 * (k : ℝ) + 4) / (n : ℝ) := by ring
      have h2 : 2 * (k : ℝ) + 1 ≤ ((n : ℝ) - (j : ℝ)) * (8 * (k : ℝ) + 4) / (n : ℝ) := by
        have hstep : ((n : ℝ) / 4) * (8 * (k : ℝ) + 4) / (n : ℝ) = 2 * (k : ℝ) + 1 := by
          field_simp
          ring
        rw [← hstep]
        gcongr
      linarith
    have hratioC : (n.choose j : ℝ) =
        (n.choose (j + 1) : ℝ) * (((j : ℝ) + 1) / ((n : ℝ) - (j : ℝ))) := by
      have hcast := choose_mul_sub_cast (n := n) (j := j) hjle
      rw [show (n.choose (j + 1) : ℝ) * (((j : ℝ) + 1) / ((n : ℝ) - (j : ℝ))) =
          ((n.choose (j + 1) : ℝ) * ((j : ℝ) + 1)) / ((n : ℝ) - (j : ℝ)) by ring]
      rw [eq_div_iff hdenpos.ne']
      linarith [hcast]
    have hb1 : (n.choose j : ℝ) ≤ (n.choose (j + 1) : ℝ) * Real.exp ((8 * (k : ℝ) + 4) / (n : ℝ)) := by
      rw [hratioC]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ((j : ℝ) + 1) / ((n : ℝ) - (j : ℝ)) ≤ 1 + (8 * (k : ℝ) + 4) / (n : ℝ) := hratio
        _ ≤ Real.exp ((8 * (k : ℝ) + 4) / (n : ℝ)) := by
            linarith [Real.add_one_le_exp ((8 * (k : ℝ) + 4) / (n : ℝ))]
    have hexp : Real.exp (8 * (k : ℝ) ^ 2 / (n : ℝ)) * Real.exp ((8 * (k : ℝ) + 4) / (n : ℝ)) ≤
        Real.exp (8 * ((k : ℝ) + 1) ^ 2 / (n : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : (0 : ℝ) < (n : ℝ) := hn
      have hk8 : 8 * ((k : ℝ) + 1) ^ 2 = 8 * (k : ℝ) ^ 2 + (8 * (k : ℝ) + 4) + (8 * (k : ℝ) + 4) := by ring
      rw [hk8]
      field_simp
      nlinarith
    calc (n.choose (n / 2) : ℝ)
        ≤ Real.exp (8 * (k : ℝ) ^ 2 / (n : ℝ)) * (n.choose j : ℝ) := ihb
      _ ≤ Real.exp (8 * (k : ℝ) ^ 2 / (n : ℝ)) *
            ((n.choose (j + 1) : ℝ) * Real.exp ((8 * (k : ℝ) + 4) / (n : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hb1 (by positivity)
      _ = (Real.exp (8 * (k : ℝ) ^ 2 / (n : ℝ)) * Real.exp ((8 * (k : ℝ) + 4) / (n : ℝ))) *
            (n.choose (j + 1) : ℝ) := by ring
      _ ≤ Real.exp (8 * ((k : ℝ) + 1) ^ 2 / (n : ℝ)) * (n.choose (j + 1) : ℝ) := by
          exact mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = Real.exp (8 * ((k + 1 : ℕ) : ℝ) ^ 2 / (n : ℝ)) * (n.choose (n / 2 + (k + 1)) : ℝ) := by
          rw [hjdef, Nat.add_assoc]
          push_cast
          ring_nf

/-- Moving `k` steps down from the middle multiplies the binomial coefficient by at most
`exp (8 k²/n)`, as long as `4 k ≤ n`. -/
theorem choose_down_shift (n : ℕ) :
    ∀ k : ℕ, 4 * k ≤ n →
      (n.choose (n / 2) : ℝ) ≤
        Real.exp (8 * (k : ℝ) ^ 2 / (n : ℝ)) * (n.choose (n / 2 - k) : ℝ) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : 4 * k ≤ n := by omega
    have ihb := ih hk'
    have hn : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    set j : ℕ := n / 2 - k with hjdef
    have hjle : j ≤ n := by omega
    have hj1 : 1 ≤ j := by omega
    have hjsub : n / 2 - (k + 1) = j - 1 := by omega
    have hden : (n : ℝ) / 4 ≤ (j : ℝ) := by
      have hnat : n ≤ 4 * j := by omega
      have : (n : ℝ) ≤ 4 * (j : ℝ) := by exact_mod_cast hnat
      linarith
    have hjpos : (0 : ℝ) < (j : ℝ) := by
      have : (0 : ℝ) ≤ (j : ℝ) := by positivity
      have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      linarith
    have hnum : (n : ℝ) - 2 * (j : ℝ) + 1 ≤ 2 * (k : ℝ) + 2 := by
      have h2 : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
        have := Nat.div_mul_le_self n 2
        have : (((n / 2) * 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
        push_cast at this
        linarith
      have hjcast : (j : ℝ) = ((n / 2 : ℕ) : ℝ) - (k : ℝ) := by
        rw [hjdef]
        have hk2 : k ≤ n / 2 := by omega
        rw [Nat.cast_sub hk2]
      have h3 : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
        have hnat : n ≤ 2 * (n / 2) + 1 := by
          have := Nat.div_add_mod n 2
          omega
        exact_mod_cast hnat
      rw [hjcast]
      linarith
    have hratio : ((n : ℝ) - (j : ℝ) + 1) / (j : ℝ) ≤ 1 + (8 * (k : ℝ) + 8) / (n : ℝ) := by
      rw [div_le_iff₀ hjpos]
      have h1 : (1 + (8 * (k : ℝ) + 8) / (n : ℝ)) * (j : ℝ) =
          (j : ℝ) + (j : ℝ) * (8 * (k : ℝ) + 8) / (n : ℝ) := by ring
      have h2 : 2 * (k : ℝ) + 2 ≤ (j : ℝ) * (8 * (k : ℝ) + 8) / (n : ℝ) := by
        have hstep : ((n : ℝ) / 4) * (8 * (k : ℝ) + 8) / (n : ℝ) = 2 * (k : ℝ) + 2 := by
          field_simp
          ring
        rw [← hstep]
        gcongr
      linarith
    have hcast := choose_mul_sub_cast (n := n) (j := j - 1) (by omega)
    have hjm1 : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      rw [Nat.cast_sub hj1]; norm_num
    have hkey : (n.choose (j - 1) : ℝ) * ((n : ℝ) - (j : ℝ) + 1) = (n.choose j : ℝ) * (j : ℝ) := by
      have hthis := hcast
      rw [hjm1, show (j - 1 + 1) = j by omega] at hthis
      have hsimp : (n : ℝ) - ((j : ℝ) - 1) = (n : ℝ) - (j : ℝ) + 1 := by ring
      rw [hsimp] at hthis
      have hsimp2 : ((j : ℝ) - 1 + 1) = (j : ℝ) := by ring
      rw [hsimp2] at hthis
      linarith [hthis]
    have hratioC : (n.choose j : ℝ) =
        (n.choose (j - 1) : ℝ) * (((n : ℝ) - (j : ℝ) + 1) / (j : ℝ)) := by
      rw [show (n.choose (j - 1) : ℝ) * (((n : ℝ) - (j : ℝ) + 1) / (j : ℝ)) =
          ((n.choose (j - 1) : ℝ) * ((n : ℝ) - (j : ℝ) + 1)) / (j : ℝ) by
            rw [mul_div_assoc'],
        eq_div_iff hjpos.ne']
      linarith [hkey]
    have hb1 : (n.choose j : ℝ) ≤ (n.choose (j - 1) : ℝ) * Real.exp ((8 * (k : ℝ) + 8) / (n : ℝ)) := by
      rw [hratioC]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ((n : ℝ) - (j : ℝ) + 1) / (j : ℝ) ≤ 1 + (8 * (k : ℝ) + 8) / (n : ℝ) := hratio
        _ ≤ Real.exp ((8 * (k : ℝ) + 8) / (n : ℝ)) := by
            linarith [Real.add_one_le_exp ((8 * (k : ℝ) + 8) / (n : ℝ))]
    have hexp : Real.exp (8 * (k : ℝ) ^ 2 / (n : ℝ)) * Real.exp ((8 * (k : ℝ) + 8) / (n : ℝ)) ≤
        Real.exp (8 * ((k + 1 : ℕ) : ℝ) ^ 2 / (n : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      push_cast
      have hnum : 8 * (k : ℝ) ^ 2 + (8 * (k : ℝ) + 8) ≤ 8 * ((k : ℝ) + 1) ^ 2 := by nlinarith
      have hsplit : 8 * (k : ℝ) ^ 2 / (n : ℝ) + (8 * (k : ℝ) + 8) / (n : ℝ) =
          (8 * (k : ℝ) ^ 2 + (8 * (k : ℝ) + 8)) / (n : ℝ) := by ring
      rw [hsplit]
      gcongr
    calc (n.choose (n / 2) : ℝ)
        ≤ Real.exp (8 * (k : ℝ) ^ 2 / (n : ℝ)) * (n.choose j : ℝ) := ihb
      _ ≤ Real.exp (8 * (k : ℝ) ^ 2 / (n : ℝ)) *
            ((n.choose (j - 1) : ℝ) * Real.exp ((8 * (k : ℝ) + 8) / (n : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hb1 (by positivity)
      _ = (Real.exp (8 * (k : ℝ) ^ 2 / (n : ℝ)) * Real.exp ((8 * (k : ℝ) + 8) / (n : ℝ))) *
            (n.choose (j - 1) : ℝ) := by ring
      _ ≤ Real.exp (8 * ((k + 1 : ℕ) : ℝ) ^ 2 / (n : ℝ)) * (n.choose (j - 1) : ℝ) := by
          exact mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = Real.exp (8 * ((k + 1 : ℕ) : ℝ) ^ 2 / (n : ℝ)) * (n.choose (n / 2 - (k + 1)) : ℝ) := by
          rw [hjsub]

/-- **Lemma 1 of the paper** (printed p. 4), in the form used downstream: for every constant
`C` there are positive constants `c₁ c₂` such that, whenever `k ≤ C √n` (the paper's `k = O(√n)`)
and `n` is large enough for `k ≤ n/4` to follow, both `C(n,⌊n/2⌋+k)` and `C(n,⌊n/2⌋-k)` lie
between `c₁ 2^n/√n` and `c₂ 2^n/√n`. -/
theorem source_lemma1 (C : ℝ) (hC : 0 < C) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ n k : ℕ, 1 ≤ k → (k : ℝ) ≤ C * Real.sqrt (n : ℝ) → 16 * C ^ 2 + 1 ≤ (n : ℝ) →
        c₁ * (2 : ℝ) ^ n / Real.sqrt (n : ℝ) ≤ (n.choose (n / 2 + k) : ℝ) ∧
          (n.choose (n / 2 + k) : ℝ) ≤ c₂ * (2 : ℝ) ^ n / Real.sqrt (n : ℝ) ∧
            c₁ * (2 : ℝ) ^ n / Real.sqrt (n : ℝ) ≤ (n.choose (n / 2 - k) : ℝ) ∧
              (n.choose (n / 2 - k) : ℝ) ≤ c₂ * (2 : ℝ) ^ n / Real.sqrt (n : ℝ) := by
  refine ⟨(1 / 4) * Real.exp (-(8 * C ^ 2)), 1, by positivity, by norm_num, ?_⟩
  intro n k hk1 hkC hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by nlinarith
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hnpos
      norm_num at hnpos
    · exact h
  have h4C : 4 * C ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by linarith) (by linarith)]
    nlinarith
  have hk4real : 4 * (k : ℝ) ≤ (n : ℝ) := by
    have h1 : 4 * (k : ℝ) ≤ 4 * C * Real.sqrt (n : ℝ) := by nlinarith
    have h2 : 4 * C * Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by nlinarith
    have h3 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
      rw [← pow_two, Real.sq_sqrt (by linarith)]
    linarith [h1, h2, h3.le, h3.ge]
  have hk4 : 4 * k ≤ n := by exact_mod_cast hk4real
  have hmiddle := choose_middle_bounds n hn1
  have hup := choose_up_shift n k hk4
  have hdown := choose_down_shift n k hk4
  have hk2 : (k : ℝ) ^ 2 ≤ C ^ 2 * (n : ℝ) := by
    have hsq := mul_le_mul hkC hkC (by positivity : (0:ℝ) ≤ (k:ℝ))
      (by positivity : (0:ℝ) ≤ C * Real.sqrt (n : ℝ))
    have h3 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
      rw [← pow_two, Real.sq_sqrt (by linarith)]
    nlinarith [hsq, h3]
  have hexpbound : 8 * (k : ℝ) ^ 2 / (n : ℝ) ≤ 8 * C ^ 2 := by
    rw [div_le_iff₀ hnpos]
    nlinarith
  have hExp : Real.exp (-(8 * C ^ 2)) ≤ Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hexpPos : (0 : ℝ) < Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))) := by positivity
  have hupper : ((n.choose (n / 2 + k) : ℝ)) ≤ (n.choose (n / 2) : ℝ) := by
    exact_mod_cast Nat.choose_le_middle (n / 2 + k) n
  have hupper' : ((n.choose (n / 2 - k) : ℝ)) ≤ (n.choose (n / 2) : ℝ) := by
    exact_mod_cast Nat.choose_le_middle (n / 2 - k) n
  have hlowCommon : (1 / 4) * (2 : ℝ) ^ n / Real.sqrt (n : ℝ) *
      Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))) ≤ (n.choose (n / 2) : ℝ) *
        Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))) := by
    exact mul_le_mul_of_nonneg_right hmiddle.1 (by positivity)
  have hlowUp : (n.choose (n / 2) : ℝ) * Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))) ≤
      (n.choose (n / 2 + k) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hup (by positivity : (0:ℝ) ≤ Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))))
    calc (n.choose (n / 2) : ℝ) * Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ)))
        = Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))) * (n.choose (n / 2) : ℝ) := by ring
      _ ≤ Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))) *
            (Real.exp (8 * (k : ℝ) ^ 2 / (n : ℝ)) * (n.choose (n / 2 + k) : ℝ)) :=
          mul_le_mul_of_nonneg_left hup (by positivity)
      _ = (Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))) *
            Real.exp (8 * (k : ℝ) ^ 2 / (n : ℝ))) * (n.choose (n / 2 + k) : ℝ) := by ring
      _ = (n.choose (n / 2 + k) : ℝ) := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hlowDown : (n.choose (n / 2) : ℝ) * Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))) ≤
      (n.choose (n / 2 - k) : ℝ) := by
    calc (n.choose (n / 2) : ℝ) * Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ)))
        = Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))) * (n.choose (n / 2) : ℝ) := by ring
      _ ≤ Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))) *
            (Real.exp (8 * (k : ℝ) ^ 2 / (n : ℝ)) * (n.choose (n / 2 - k) : ℝ)) :=
          mul_le_mul_of_nonneg_left hdown (by positivity)
      _ = (Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))) *
            Real.exp (8 * (k : ℝ) ^ 2 / (n : ℝ))) * (n.choose (n / 2 - k) : ℝ) := by ring
      _ = (n.choose (n / 2 - k) : ℝ) := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hmain : ((1 / 4) * Real.exp (-(8 * C ^ 2))) * (2 : ℝ) ^ n / Real.sqrt (n : ℝ) ≤
      (1 / 4) * (2 : ℝ) ^ n / Real.sqrt (n : ℝ) * Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ n / Real.sqrt (n : ℝ) := by positivity
    calc ((1 / 4) * Real.exp (-(8 * C ^ 2))) * (2 : ℝ) ^ n / Real.sqrt (n : ℝ)
        = (1 / 4) * ((2 : ℝ) ^ n / Real.sqrt (n : ℝ)) * Real.exp (-(8 * C ^ 2)) := by ring
      _ ≤ (1 / 4) * ((2 : ℝ) ^ n / Real.sqrt (n : ℝ)) *
            Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))) := by
          have h4 : (0 : ℝ) ≤ (1 / 4) * ((2 : ℝ) ^ n / Real.sqrt (n : ℝ)) := by positivity
          exact mul_le_mul_of_nonneg_left hExp h4
      _ = (1 / 4) * (2 : ℝ) ^ n / Real.sqrt (n : ℝ) * Real.exp (-(8 * (k : ℝ) ^ 2 / (n : ℝ))) := by
          ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hmain.trans (hlowCommon.trans hlowUp)
  · rw [one_mul]
    exact hupper.trans hmiddle.2
  · exact hmain.trans (hlowCommon.trans hlowDown)
  · rw [one_mul]
    exact hupper'.trans hmiddle.2

/-- Sections 5 and 6 of the paper use `κ₀[[s]] = √(C(k,s))/2^{k/2}` with `s = ⌊k/2⌋`, and record
`κ₀[[s]] = Θ(k^{-1/4})` as the first consequence of Lemma 1. This is that consequence, stated for
the weight `κ₀[[s]]² = C(k,⌊k/2⌋)/2^k`. -/
theorem krawtchouk_zero_middle_weight (k : ℕ) (hk : 1 ≤ k) :
    (1 / 4) / Real.sqrt (k : ℝ) ≤ (k.choose (k / 2) : ℝ) / (2 : ℝ) ^ k ∧
      (k.choose (k / 2) : ℝ) / (2 : ℝ) ^ k ≤ 1 / Real.sqrt (k : ℝ) := by
  have hkb := choose_middle_bounds k hk
  have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hsqrt : (0 : ℝ) < Real.sqrt (k : ℝ) := by positivity
  constructor
  · rw [le_div_iff₀ hpow]
    calc (1 / 4) / Real.sqrt (k : ℝ) * (2 : ℝ) ^ k
        = ((1 / 4) * (2 : ℝ) ^ k / Real.sqrt (k : ℝ)) := by ring
      _ ≤ (k.choose (k / 2) : ℝ) := hkb.1
  · have h := hkb.2
    calc (k.choose (k / 2) : ℝ) / (2 : ℝ) ^ k
        ≤ ((2 : ℝ) ^ k / Real.sqrt (k : ℝ)) / (2 : ℝ) ^ k := by
          gcongr
      _ = 1 / Real.sqrt (k : ℝ) := by
          field_simp

end Qatlib.Papers.SymJunta13.MainResults
