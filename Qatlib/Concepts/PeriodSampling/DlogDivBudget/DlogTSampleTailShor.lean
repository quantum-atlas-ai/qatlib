/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogDivBudget.DlogTSampleTailStat
import Qatlib.Concepts.PeriodSampling.DlogDivBudget.DlogUniformGoodDivisibilityShor

/-!
# Tail bounds for common prime-power divisors

This module bounds the probability that uniformly sampled good discrete-logarithm outputs share
a prime-power divisor greater than 18. It combines a union bound with arithmetic estimates for
the divisor sum to prove `dlogTSampleTail`, including a probability below one half for at least
twelve samples in the parameter range of [Shor1997].

## Main statements

* `dlog_tsample_union_bound`: Bounds the common-divisor event by a sum of powers of
  single-sample bounds.
* `dlog_tsample_sum_bound`: Controls this divisor sum by an explicit constant.
* `dlogTSampleTail`: Establishes the common-divisor tail contract.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.PeriodSampling.DlogDivBudget
open Qatlib
open scoped Classical BigOperators

/-- The probability that all `t` independent samples satisfy `E` is the `t`th power of the
single-sample mass of `E`. -/
theorem dlog_probEvent_all {X : Type} [Fintype X] [DecidableEq X]
    (law : FinDist X) (E : X → Prop) [DecidablePred E] (t : ℕ) :
    law.probEvent (L := t) (fun ω => ∀ i, E (ω i)) =
      (∑ x ∈ Finset.univ.filter E, law.prob x) ^ t := by
  have h := law.expect_prod (L := t) (fun _ x => if E x then (1 : ℝ) else 0)
  simpa only [Fintype.prod_ite_zero, Finset.prod_const_one, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, mul_ite, mul_one, mul_zero,
    FinDist.probEvent, Finset.sum_filter] using h

/-- The probability of a union indexed by a finite set is at most the sum of the probabilities
of its events. -/
theorem dlog_probEvent_union {X : Type} [Fintype X] [DecidableEq X]
    (law : FinDist X) (t : ℕ) (S : Finset ℕ)
    (E : ℕ → (Fin t → X) → Prop) :
    law.probEvent (fun ω => ∃ w ∈ S, E w ω) ≤
      ∑ w ∈ S, law.probEvent (E w) := by
  simp only [FinDist.probEvent, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  have hn : 0 ≤ law.probOf ω := Finset.prod_nonneg fun i _ => law.nonneg (ω i)
  by_cases he : ∃ w ∈ S, E w ω
  · rw [if_pos he]
    obtain ⟨w, hw, hew⟩ := he
    calc
      _ = (if E w ω then law.probOf ω else 0) := (if_pos hew).symm
      _ ≤ _ := Finset.single_le_sum (s := S) (a := w)
        (f := fun j => if E j ω then law.probOf ω else 0)
        (fun j _ => by exact ite_nonneg hn (le_refl 0)) hw
  · rw [if_neg he]
    exact Finset.sum_nonneg fun j _ => by split_ifs <;> positivity

/-- For the stated prime and Fourier-modulus range, the common prime-power divisibility
probability is bounded by the sum of the corresponding single-sample bounds raised to `t`. -/
theorem dlog_tsample_union_bound (p q t : ℕ) [NeZero p] [NeZero q]
    (hprime : Nat.Prime p) (hp : 3 ≤ p) (hpq : p < q) (hq : q < 2 * p) :
    (dlogUniformGoodLaw p q).probEvent (L := t) (dlogCommonPpDivides p q) ≤
      ∑ w ∈ (Nat.divisors (p - 1)).filter (fun w => dlogIsPrimePower w ∧ 18 < w),
        ((((p - 1) / w + 1 : ℕ) : ℝ) / ((q / 12 : ℕ) : ℝ)) ^ t := by
  have hub := dlog_probEvent_union (dlogUniformGoodLaw p q) t
    ((Nat.divisors (p - 1)).filter (fun w => dlogIsPrimePower w ∧ 18 < w))
    (fun w ω => ∀ i, (w : ℤ) ∣ dlogCprime p q (ω i).val)
  have hub' : (dlogUniformGoodLaw p q).probEvent (L := t) (dlogCommonPpDivides p q) ≤
      ∑ w ∈ (Nat.divisors (p - 1)).filter (fun w => dlogIsPrimePower w ∧ 18 < w),
        (dlogUniformGoodLaw p q).probEvent (L := t)
          (fun ω => ∀ i, (w : ℤ) ∣ dlogCprime p q (ω i).val) := by
    convert hub using 1
    · unfold FinDist.probEvent
      congr 1
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, dlogCommonPpDivides]
    · apply Finset.sum_congr rfl
      intro w _
      unfold FinDist.probEvent
      congr 1
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  apply le_trans hub'
  apply Finset.sum_le_sum
  intro w hw
  obtain ⟨hwd, _, hwlarge⟩ := Finset.mem_filter.mp hw
  have hdiv : w ∣ p - 1 := (Nat.mem_divisors.mp hwd).1
  have hwle : w ≤ p - 1 := Nat.le_of_dvd (by omega) hdiv
  have hden : (0 : ℝ) < ((q / 12 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < q / 12 by omega)
  have hb := dlogUniformGoodDivisibility p q hprime hp hpq hq w (by omega) hdiv
  rw [dlog_probEvent_one (dlogUniformGoodLaw p q)
    (fun c : dlogGoodCType p q => (w : ℤ) ∣ dlogCprime p q c.val)] at hb
  rw [dlog_probEvent_all (dlogUniformGoodLaw p q)
    (fun c : dlogGoodCType p q => (w : ℤ) ∣ dlogCprime p q c.val) t]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun c _ => (dlogUniformGoodLaw p q).nonneg c)
    ((le_div_iff₀ hden).2 hb) t

/-- The common prime-power divisibility event has probability zero when there are no prime-power
divisors of `p - 1` greater than 18. -/
theorem dlog_tsample_empty_divisors (p q t : ℕ) [NeZero q]
    (he : (Nat.divisors (p-1)).filter (fun w => dlogIsPrimePower w ∧ 18 < w) = ∅) :
    (dlogUniformGoodLaw p q).probEvent (L := t) (dlogCommonPpDivides p q) = 0 := by
  simp [FinDist.probEvent,dlogCommonPpDivides,he]

/-- For `2 ≤ p ≤ 19`, the common prime-power divisibility event has probability zero. -/
theorem dlog_tsample_small_modulus (p q t : ℕ) [NeZero q] (hp : 2 ≤ p) (hp19 : p ≤ 19) :
    (dlogUniformGoodLaw p q).probEvent (L := t) (dlogCommonPpDivides p q) = 0 := by
  apply dlog_tsample_empty_divisors
  apply Finset.filter_eq_empty_iff.mpr
  intro w hw
  have hle : w ≤ p-1 := Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hw).1
  omega

/-- Natural-number scalar multiplication on the reals equals multiplication by the corresponding
real cast. -/
theorem dlog_nat_smul_real (k : ℕ) (x : ℝ) : k • x = (k : ℝ) * x := by
  rw [← smul_one_mul, Nat.smul_one_eq_cast]

/-- For a prime `p ≥ 3`, the identity `p - 1 = 2 * (p / 2)` holds with natural-number division. -/
theorem dlog_prime_sub_two_mul {p : ℕ} (hprime : Nat.Prime p) (hp3 : 3 ≤ p) :
    p - 1 = 2 * (p / 2) := by
  rcases hprime.eq_two_or_odd with h | h
  · omega
  · omega

/-- An even prime power greater than 18 is a power of two with exponent at least five. -/
theorem dlog_even_prime_power {w : ℕ} (hpp : dlogIsPrimePower w) (hw18 : 18 < w)
    (hw2 : 2 ∣ w) : ∃ e, 5 ≤ e ∧ 2 ^ e = w := by
  obtain ⟨ℓ, e, hℓ, _, hwe⟩ := hpp
  rcases hℓ.eq_two_or_odd with h2 | hodd
  · rw [h2] at hwe
    refine ⟨e, ?_, hwe⟩
    by_contra hcon
    have h4 : e ≤ 4 := by omega
    have h16 : (2:ℕ) ^ e ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h4
    norm_num at h16
    have hwle : w ≤ 16 := by rw [← hwe]; exact h16
    omega
  · exfalso
    rw [← hwe] at hw2
    obtain ⟨j, hj⟩ := (Nat.even_pow.mp (even_iff_two_dvd.mpr hw2)).1
    omega

/-- A prime power between 19 and 28 inclusive is one of 19, 23, 25, or 27. -/
theorem dlog_prime_power_19_28 {w : ℕ} (hpp : dlogIsPrimePower w)
    (hw19 : 19 ≤ w) (hw28 : w ≤ 28) :
    w = 19 ∨ w = 23 ∨ w = 25 ∨ w = 27 := by
  obtain ⟨ℓ, e, hℓ, he, hwe⟩ := hpp
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  have he4 : e ≤ 4 := by
    by_contra hcon
    have h5 : 5 ≤ e := by omega
    have h32 : (2:ℕ) ^ 5 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h5
    have h32' : (2:ℕ) ^ 5 ≤ ℓ ^ e := h32.trans (Nat.pow_le_pow_left hℓ2 e)
    norm_num at h32'
    have hwge : 32 ≤ w := by rw [← hwe]; exact h32'
    omega
  interval_cases e
  · have hℓw : ℓ = w := by rw [← hwe, pow_one]
    have hmem : w ∈ (Finset.Icc 19 28).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hw19, hw28⟩, hℓw ▸ hℓ⟩
    rw [show (Finset.Icc 19 28).filter Nat.Prime = {19, 23} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hℓle : ℓ ≤ 5 := by
      by_contra hcon
      have h6 : 6 ≤ ℓ := by omega
      have h36 : (6:ℕ) ^ 2 ≤ ℓ ^ 2 := Nat.pow_le_pow_left h6 2
      norm_num at h36
      have hwge : 36 ≤ w := by rw [← hwe]; exact h36
      omega
    have hℓge : 5 ≤ ℓ := by
      by_contra hcon
      have hℓ4 : ℓ ≤ 4 := by omega
      interval_cases ℓ
      · norm_num at hwe; omega
      · norm_num at hwe; omega
      · exact absurd hℓ (by decide)
    interval_cases ℓ
    norm_num at hwe
    exact Or.inr (Or.inr (Or.inl (by omega)))
  · have hℓle : ℓ ≤ 3 := by
      by_contra hcon
      have h4 : 4 ≤ ℓ := by omega
      have h64 : (4:ℕ) ^ 3 ≤ ℓ ^ 3 := Nat.pow_le_pow_left h4 3
      norm_num at h64
      have hwge : 64 ≤ w := by rw [← hwe]; exact h64
      omega
    interval_cases ℓ
    · norm_num at hwe; omega
    · norm_num at hwe
      exact Or.inr (Or.inr (Or.inr (by omega)))
  · have hℓle : ℓ ≤ 2 := by
      by_contra hcon
      have h3 : 3 ≤ ℓ := by omega
      have h81 : (3:ℕ) ^ 4 ≤ ℓ ^ 4 := Nat.pow_le_pow_left h3 4
      norm_num at h81
      have hwge : 81 ≤ w := by rw [← hwe]; exact h81
      omega
    interval_cases ℓ
    norm_num at hwe
    exact absurd hw19 (by omega)

/-- A prime predecessor cannot equal `w * m` when `w` is a prime power in `[19, 23)` and `m` is
one of 2, 4, 6, or 8. -/
theorem dlog_mid_even_false {p w m : ℕ} (hprime : Nat.Prime p) (hwm : w * m = p - 1)
    (hw19 : 19 ≤ w) (hpp : dlogIsPrimePower w) (hw22 : w < 23)
    (hm : m = 2 ∨ m = 4 ∨ m = 6 ∨ m = 8) : False := by
  rcases dlog_prime_power_19_28 hpp hw19 (by omega) with h1 | h1 | h1 | h1
  · rw [h1] at hwm
    rcases hm with hm | hm | hm | hm
    · rw [hm] at hwm
      have hp : p = 39 := by omega
      rw [hp] at hprime
      exact absurd hprime (by decide)
    · rw [hm] at hwm
      have hp : p = 77 := by omega
      rw [hp] at hprime
      exact absurd hprime (by decide)
    · rw [hm] at hwm
      have hp : p = 115 := by omega
      rw [hp] at hprime
      exact absurd hprime (by decide)
    · rw [hm] at hwm
      have hp : p = 153 := by omega
      rw [hp] at hprime
      exact absurd hprime (by decide)
  · omega
  · omega
  · omega

/-- If `p - 1 = m * w` for an odd prime `p`, a prime power `w ≥ 19`, and `m` in `{3, 5, 7, 9}`,
then `w ≥ 32`. -/
theorem dlog_mid_odd_ge {p w m : ℕ} (hprime : Nat.Prime p) (hp3 : 3 ≤ p) (hwm : m * w = p - 1)
    (hw19 : 19 ≤ w) (hpp : dlogIsPrimePower w)
    (hm : m = 3 ∨ m = 5 ∨ m = 7 ∨ m = 9) : 32 ≤ w := by
  have hpeven : p - 1 = 2 * (p / 2) := dlog_prime_sub_two_mul hprime hp3
  rcases Nat.even_or_odd w with he | ho
  · obtain ⟨e, he5, hwe⟩ := dlog_even_prime_power hpp (by omega) (even_iff_two_dvd.mp he)
    have h2e : (2:ℕ) ^ 5 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he5
    norm_num at h2e
    rw [← hwe]
    exact h2e
  · exfalso
    obtain ⟨a, ha⟩ := ho
    rcases hm with hm | hm | hm | hm <;> rw [hm] at hwm <;> rw [ha] at hwm
    all_goals omega

/-- From `w * m = p - 1`, `1 ≤ p`, and `p < q`, derives the two stated bounds involving `q` and
`q / 12`. -/
theorem dlog_floor_bounds (p q w m : ℕ) (hp1 : 1 ≤ p) (hpq : p < q) (hwm : w * m = p - 1) :
    w * m + 2 ≤ q ∧ w * m ≤ 12 * (q / 12) + 9 := by
  have hqd : q = 12 * (q / 12) + q % 12 := (Nat.div_add_mod q 12).symm
  have hqmod : q % 12 < 12 := Nat.mod_lt _ (by norm_num)
  constructor <;> omega

/-- The natural-number inequality `4 * (m + 1) ≤ 3 * (q / 12)` gives the real ratio bound `(m +
1) / (q / 12) ≤ 3 / 4` when the denominator is positive. -/
theorem dlog_rho_of_floor {m q : ℕ} (hD1 : 1 ≤ q / 12)
    (h4 : 4 * (m + 1) ≤ 3 * (q / 12)) :
    (((m + 1 : ℕ) : ℝ) / ((q / 12 : ℕ) : ℝ)) ≤ 3 / 4 := by
  have hDpos : (0:ℝ) < ((q / 12 : ℕ) : ℝ) := by exact_mod_cast hD1
  rw [div_le_iff₀ hDpos]
  have hcast : (4:ℝ) * (((m + 1 : ℕ) : ℝ)) ≤ 3 * ((q / 12 : ℕ) : ℝ) := by exact_mod_cast h4
  linarith

/-- When `w ≥ 19` divides `p - 1` and its complementary divisor is at least ten, the ratio `((p
- 1) / w + 1) / (q / 12)` is at most `14 / w`. -/
theorem dlog_rho_le_div14 (p q w : ℕ) (hp1 : 1 ≤ p) (hpq : p < q)
    (hw : w ∣ p - 1) (hw19 : 19 ≤ w) (hm10 : 10 ≤ (p - 1) / w) :
    ((((p - 1) / w + 1 : ℕ) : ℝ) / ((q / 12 : ℕ) : ℝ)) ≤ 14 / ((w : ℕ) : ℝ) := by
  have hwm : ((p - 1) / w) * w = p - 1 := Nat.div_mul_cancel hw
  have hwm2 : w * ((p - 1) / w) = p - 1 := by rw [mul_comm]; exact hwm
  obtain ⟨_, hD⟩ := dlog_floor_bounds p q w _ hp1 hpq hwm2
  have h190 : (19:ℕ) * 10 ≤ w * ((p - 1) / w) :=
    mul_le_mul hw19 hm10 (by omega) (by omega)
  have hD1 : 1 ≤ q / 12 := by omega
  have hDpos : (0:ℝ) < ((q / 12 : ℕ) : ℝ) := by exact_mod_cast hD1
  have hWpos : (0:ℝ) < ((w : ℕ) : ℝ) := by exact_mod_cast (show 0 < w by omega)
  have hW19 : (19:ℝ) ≤ ((w : ℕ) : ℝ) := by exact_mod_cast hw19
  have hM10 : (10:ℝ) ≤ (((p - 1) / w : ℕ) : ℝ) := by exact_mod_cast hm10
  have hDcast : ((w : ℕ) : ℝ) * (((p - 1) / w : ℕ) : ℝ) ≤ 12 * ((q / 12 : ℕ) : ℝ) + 9 := by
    exact_mod_cast hD
  have h4 : (4:ℝ) ≤ (((p - 1) / w : ℕ) : ℝ) - 6 := by linarith
  have hprod : (19:ℝ) * 4 ≤ ((w : ℕ) : ℝ) * ((((p - 1) / w : ℕ) : ℝ) - 6) :=
    mul_le_mul hW19 h4 (by linarith) (by linarith)
  rw [div_le_iff₀ hDpos, div_mul_eq_mul_div, le_div_iff₀ hWpos]
  push_cast
  nlinarith [hDcast, hprod]

/-- For the stated prime-power divisor and a complementary divisor between two and nine, the
ratio `((p - 1) / w + 1) / (q / 12)` is at most `3 / 4`. -/
theorem dlog_rho_le_three_fourths (p q w : ℕ) (hprime : Nat.Prime p) (hp3 : 3 ≤ p)
    (hpq : p < q) (hw : w ∣ p - 1) (hw19 : 19 ≤ w) (hpp : dlogIsPrimePower w)
    (hm2 : 2 ≤ (p - 1) / w) (hm9 : (p - 1) / w ≤ 9) :
    ((((p - 1) / w + 1 : ℕ) : ℝ) / ((q / 12 : ℕ) : ℝ)) ≤ 3 / 4 := by
  have hp1 : 1 ≤ p := by omega
  have hwm : ((p - 1) / w) * w = p - 1 := Nat.div_mul_cancel hw
  have hwm2 : w * ((p - 1) / w) = p - 1 := by rw [mul_comm]; exact hwm
  obtain ⟨hqe, hD⟩ := dlog_floor_bounds p q w _ hp1 hpq hwm2
  have hpeven : p - 1 = 2 * (p / 2) := dlog_prime_sub_two_mul hprime hp3
  set m := (p - 1) / w with hmdef
  interval_cases m
  · rcases Nat.lt_or_ge w 23 with hlt | hge
    · exact (dlog_mid_even_false hprime hwm2 hw19 hpp hlt (Or.inl rfl)).elim
    · exact dlog_rho_of_floor (by omega) (by omega)
  · have hw32 := dlog_mid_odd_ge hprime hp3 hwm hw19 hpp (Or.inl rfl)
    exact dlog_rho_of_floor (by omega) (by omega)
  · rcases Nat.lt_or_ge w 23 with hlt | hge
    · exact (dlog_mid_even_false hprime hwm2 hw19 hpp hlt (Or.inr (Or.inl rfl))).elim
    · exact dlog_rho_of_floor (by omega) (by omega)
  · have hw32 := dlog_mid_odd_ge hprime hp3 hwm hw19 hpp (Or.inr (Or.inl rfl))
    exact dlog_rho_of_floor (by omega) (by omega)
  · rcases Nat.lt_or_ge w 23 with hlt | hge
    · exact (dlog_mid_even_false hprime hwm2 hw19 hpp hlt
        (Or.inr (Or.inr (Or.inl rfl)))).elim
    · exact dlog_rho_of_floor (by omega) (by omega)
  · have hw32 := dlog_mid_odd_ge hprime hp3 hwm hw19 hpp (Or.inr (Or.inr (Or.inl rfl)))
    exact dlog_rho_of_floor (by omega) (by omega)
  · rcases Nat.lt_or_ge w 23 with hlt | hge
    · exact (dlog_mid_even_false hprime hwm2 hw19 hpp hlt
        (Or.inr (Or.inr (Or.inr rfl)))).elim
    · exact dlog_rho_of_floor (by omega) (by omega)
  · have hw32 := dlog_mid_odd_ge hprime hp3 hwm hw19 hpp (Or.inr (Or.inr (Or.inr rfl)))
    exact dlog_rho_of_floor (by omega) (by omega)

/-- For the stated prime-power divisor with complementary divisor one, the ratio `((p - 1) / w +
1) / (q / 12)` is at most `1 / 10`. -/
theorem dlog_rho_le_one_tenth (p q w : ℕ) (hprime : Nat.Prime p) (hp3 : 3 ≤ p)
    (hpq : p < q) (hw : w ∣ p - 1) (hw19 : 19 ≤ w) (hpp : dlogIsPrimePower w)
    (hm1 : (p - 1) / w = 1) :
    ((((p - 1) / w + 1 : ℕ) : ℝ) / ((q / 12 : ℕ) : ℝ)) ≤ 1 / 10 := by
  have hp1 : 1 ≤ p := by omega
  have hpeven : p - 1 = 2 * (p / 2) := dlog_prime_sub_two_mul hprime hp3
  have hwm : ((p - 1) / w) * w = p - 1 := Nat.div_mul_cancel hw
  rw [hm1] at hwm
  have hweq : w = p - 1 := by omega
  have hw2d : 2 ∣ w := by
    rw [hweq, hpeven]
    exact ⟨p / 2, rfl⟩
  obtain ⟨e, he5, hwe⟩ := dlog_even_prime_power hpp (by omega) hw2d
  rcases Nat.lt_or_ge w 256 with hlt | hge
  · exfalso
    have he7 : e ≤ 7 := by
      by_contra hcon
      have h8 : 8 ≤ e := by omega
      have h2e : (2:ℕ) ^ 8 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h8
      norm_num at h2e
      have hwge : 256 ≤ w := by rw [← hwe]; exact h2e
      omega
    interval_cases e
    · norm_num at hwe
      have hp : p = 33 := by omega
      rw [hp] at hprime
      exact absurd hprime (by decide)
    · norm_num at hwe
      have hp : p = 65 := by omega
      rw [hp] at hprime
      exact absurd hprime (by decide)
    · norm_num at hwe
      have hp : p = 129 := by omega
      rw [hp] at hprime
      exact absurd hprime (by decide)
  · have hD1 : 1 ≤ q / 12 := by omega
    have hD21 : 21 ≤ q / 12 := by omega
    have hDpos : (0:ℝ) < ((q / 12 : ℕ) : ℝ) := by exact_mod_cast hD1
    have hDcast : (21:ℝ) ≤ ((q / 12 : ℕ) : ℝ) := by exact_mod_cast hD21
    rw [hm1]
    norm_num
    rw [div_le_iff₀ hDpos]
    linarith

/-- If `0 ≤ a ≤ c ≤ 1` and `t ≥ 12`, then `a ^ t ≤ c ^ 12`. -/
theorem dlog_pow_t_le {a c : ℝ} {t : ℕ} (ha : 0 ≤ a) (hac : a ≤ c) (hc1 : c ≤ 1)
    (ht : 12 ≤ t) : a ^ t ≤ c ^ 12 := by
  have hsplit : a ^ t = a ^ 12 * a ^ (t - 12) := by
    conv_lhs => rw [show t = 12 + (t - 12) by omega]
    rw [pow_add]
  have ha12 : a ^ 12 ≤ c ^ 12 := pow_le_pow_left₀ ha hac 12
  have hare : a ^ (t - 12) ≤ 1 := pow_le_one₀ ha (le_trans hac hc1)
  rw [hsplit]
  calc a ^ 12 * a ^ (t - 12) ≤ a ^ 12 * 1 :=
        mul_le_mul_of_nonneg_left hare (pow_nonneg ha 12)
    _ = a ^ 12 := by ring
    _ ≤ c ^ 12 := ha12

/-- For `x ≥ 19`, bounds `1 / x ^ 12` by one eleventh of the difference between consecutive
reciprocal eleventh powers. -/
theorem dlog_inv_pow_step (x : ℝ) (hx : 19 ≤ x) :
    1 / x ^ 12 ≤ 1 / 11 * (1 / (x - 1) ^ 11 - 1 / x ^ 11) := by
  have hx0 : (0:ℝ) < x := by linarith
  have hxm : (0:ℝ) < x - 1 := by linarith
  have hbern := one_add_mul_le_pow (a := 1 / (x - 1))
    (le_trans (by norm_num : (-2:ℝ) ≤ 0) (div_nonneg (by norm_num) hxm.le)) 11
  have hmul := mul_le_mul_of_nonneg_right hbern (pow_nonneg hxm.le 11)
  have hL : (1 + ((11:ℕ):ℝ) * (1 / (x - 1))) * (x - 1) ^ 11
      = (x - 1) ^ 11 + 11 * (x - 1) ^ 10 := by
    field_simp
    ring
  have hR : (1 + 1 / (x - 1)) ^ 11 * (x - 1) ^ 11 = x ^ 11 := by
    have h1 : 1 + 1 / (x - 1) = x / (x - 1) := by
      field_simp
      ring
    rw [h1]
    field_simp
  rw [hL, hR] at hmul
  have hkey : (x + 11) * (x - 1) ^ 11 ≤ x ^ 12 := by
    have h2 : (x - 1) ^ 11 ≤ x * (x - 1) ^ 10 := by
      have hp : (x - 1) ^ 11 = (x - 1) ^ 10 * (x - 1) := (pow_succ (x - 1) 10).symm
      rw [hp, mul_comm x ((x - 1) ^ 10)]
      exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hxm.le 10)
    have h3 : ((x - 1) ^ 11 + 11 * (x - 1) ^ 10) * x ≤ x ^ 11 * x :=
      mul_le_mul_of_nonneg_right hmul hx0.le
    have h4 : x ^ 11 * x = x ^ 12 := (pow_succ x 11).symm
    rw [h4] at h3
    nlinarith [h2, h3]
  rw [show ((1:ℝ)/11) * (1 / (x - 1) ^ 11 - 1 / x ^ 11)
      = (1 / (x - 1) ^ 11 - 1 / x ^ 11) / 11 by ring]
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 11)]
  rw [le_sub_iff_add_le]
  rw [le_div_iff₀ (pow_pos hxm 11)]
  have hpos : (0:ℝ) < x ^ 12 * x ^ 11 := by positivity
  have hbr : (1 / x ^ 12 * 11 + 1 / x ^ 11) * (x - 1) ^ 11
      = (11 * (x - 1) ^ 11 * x ^ 11 + (x - 1) ^ 11 * x ^ 12) / (x ^ 12 * x ^ 11) := by
    field_simp
  rw [hbr, div_le_iff₀ hpos]
  have hx11 : (0:ℝ) ≤ x ^ 11 := pow_nonneg hx0.le 11
  have hd : (0:ℝ) ≤ x ^ 12 - (x + 11) * (x - 1) ^ 11 := by nlinarith [hkey]
  nlinarith [mul_nonneg hx11 hd]

/-- The finite sum of consecutive differences of `F` telescopes to `F 0 - F m`. -/
theorem dlog_sum_range_telescope (F : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range m, (F k - F (k + 1)) = F 0 - F m := by
  have hconv : ∑ k ∈ Finset.range m, (F k - F (k + 1))
      = ∑ k ∈ Finset.range m, ((fun k => -F k) (k + 1) - (fun k => -F k) k) :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [hconv]
  show ∑ k ∈ Finset.range m, (-F (k + 1) - -F k) = F 0 - F m
  have h2 : ∑ k ∈ Finset.range m, (-F (k + 1) - -F k)
      = ∑ i ∈ Finset.range m, ((fun k => -F k) (i + 1) - (fun k => -F k) i) :=
    Finset.sum_congr rfl fun _ _ => rfl
  rw [h2, Finset.sum_range_sub (fun k => -F k) m]
  ring

/-- The sum of reciprocal twelfth powers from 19 to `n` is at most `1 / (11 * 18 ^ 11)`. -/
theorem dlog_sum_inv_pow_le (n : ℕ) :
    ∑ w ∈ Finset.Icc 19 n, (1:ℝ) / ((w:ℕ) ^ 12) ≤ 1 / (11 * ((18:ℝ) ^ 11)) := by
  rcases Nat.lt_or_ge n 19 with hlt | h19
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    norm_num
  · have hsum2 : ∑ w ∈ Finset.Icc 19 n, (1:ℝ) / ((w:ℕ) ^ 12) ≤
        ∑ w ∈ Finset.Icc 19 n, 1 / 11 * (1 / (((w:ℕ):ℝ) - 1) ^ 11 - 1 / ((w:ℕ):ℝ) ^ 11) := by
      refine Finset.sum_le_sum fun w hw => ?_
      have hw19 : 19 ≤ w := (Finset.mem_Icc.mp hw).1
      have hwR : 19 ≤ ((w:ℕ):ℝ) := by exact_mod_cast hw19
      exact dlog_inv_pow_step _ hwR
    refine le_trans hsum2 ?_
    have heq : (Finset.Icc 19 n : Finset ℕ) = Finset.Ico 19 (n + 1) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [heq, Finset.sum_Ico_eq_sum_range]
    have hconv : ∑ k ∈ Finset.range (n + 1 - 19),
        (fun w => 1 / 11 * (1 / (((w:ℕ):ℝ) - 1) ^ 11 - 1 / ((w:ℕ):ℝ) ^ 11)) ((19:ℕ) + k)
        = 1 / 11 * ∑ k ∈ Finset.range (n + 1 - 19),
            ((1:ℝ) / ((((18:ℕ) + k : ℕ):ℝ) ^ 11)
              - (1:ℝ) / ((((18:ℕ) + (k + 1) : ℕ):ℝ) ^ 11)) := by
      rw [← Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      have hA : (((19:ℕ) + k : ℕ):ℝ) - 1 = (((18:ℕ) + k : ℕ):ℝ) := by push_cast; ring
      have hB : (((18:ℕ) + (k + 1) : ℕ):ℝ) = (((19:ℕ) + k : ℕ):ℝ) := by push_cast; ring
      rw [hA, hB]
    rw [hconv]
    rw [dlog_sum_range_telescope
      (fun j => (1:ℝ) / ((((18:ℕ) + j : ℕ):ℝ) ^ 11)) (n + 1 - 19)]
    have h0 : (18:ℕ) + 0 = 18 := by omega
    have hn : (18:ℕ) + (n + 1 - 19) = n := by omega
    rw [h0, hn]
    have hnn : (0:ℝ) ≤ 1 / (((n:ℕ):ℝ) ^ 11) := by positivity
    have hident : 1 / (11 * ((18:ℝ) ^ 11)) = 1 / 11 * (1 / (((18:ℕ):ℝ) ^ 11)) := by
      push_cast
      field_simp
    rw [hident]
    linarith

/-- The explicit constant bounding the twelve-sample divisor sum is strictly less than one half. -/
theorem dlog_tsample_constant :
    (1 / 10 : ℝ) ^ 12 + 8 * (3 / 4) ^ 12 + 14 ^ 12 / (11 * ((18:ℝ) ^ 11)) < 1 / 2 := by
  norm_num

/-- For `t ≥ 12` and the stated prime-modulus assumptions, the prime-power divisor sum is
bounded by the explicit twelve-sample constant. -/
theorem dlog_tsample_sum_bound (p q t : ℕ) (hprime : Nat.Prime p) (hp3 : 3 ≤ p)
    (hpq : p < q) (ht : 12 ≤ t) :
    ∑ w ∈ (Nat.divisors (p - 1)).filter (fun w => dlogIsPrimePower w ∧ 18 < w),
        ((((p - 1) / w + 1 : ℕ) : ℝ) / ((q / 12 : ℕ) : ℝ)) ^ t
      ≤ (1 / 10 : ℝ) ^ 12 + 8 * (3 / 4) ^ 12 + 14 ^ 12 / (11 * ((18:ℝ) ^ 11)) := by
  have hp1 : 1 ≤ p := by omega
  rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1)))
      (fun w => (p - 1) / w ≤ 9)
      (fun w => ((((p - 1) / w + 1 : ℕ) : ℝ) / ((q / 12 : ℕ) : ℝ)) ^ t)]
  rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.filter (fun w => (p - 1) / w ≤ 9)
        (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1))))
      (fun w => (p - 1) / w = 1)
      (fun w => ((((p - 1) / w + 1 : ℕ) : ℝ) / ((q / 12 : ℕ) : ℝ)) ^ t)]
  refine add_le_add_three ?_ ?_ ?_
  · have hT1sub : ∀ x ∈ Finset.filter (fun w => (p - 1) / w = 1)
          (Finset.filter (fun w => (p - 1) / w ≤ 9)
            (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1)))),
        x = p - 1 := by
      intro x hx
      obtain ⟨h1, hm1⟩ := Finset.mem_filter.mp hx
      obtain ⟨h2, _⟩ := Finset.mem_filter.mp h1
      obtain ⟨hdx, _, _⟩ := Finset.mem_filter.mp h2
      obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hdx
      have hwm : (p - 1) / x * x = p - 1 := Nat.div_mul_cancel hdvd
      rw [hm1] at hwm
      omega
    by_cases hn : p - 1 ∈ Finset.filter (fun w => (p - 1) / w = 1)
        (Finset.filter (fun w => (p - 1) / w ≤ 9)
          (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1))))
    · rw [Finset.eq_singleton_iff_nonempty_unique_mem.mpr
        ⟨⟨p - 1, hn⟩, fun x hx => hT1sub x hx⟩, Finset.sum_singleton]
      obtain ⟨h1, _⟩ := Finset.mem_filter.mp hn
      obtain ⟨h2, _⟩ := Finset.mem_filter.mp h1
      obtain ⟨hdx, hpp, hw18⟩ := Finset.mem_filter.mp h2
      obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hdx
      have hw19 : 19 ≤ p - 1 := by omega
      have hρ := dlog_rho_le_one_tenth p q (p - 1) hprime hp3 hpq hdvd hw19 hpp
        (Nat.div_self (by omega))
      exact dlog_pow_t_le (by positivity) hρ (by norm_num) ht
    · have hempty : Finset.filter (fun w => (p - 1) / w = 1)
          (Finset.filter (fun w => (p - 1) / w ≤ 9)
            (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1)))) = ∅ := by
        rw [← Finset.subset_empty]
        intro x hx
        exact absurd (hT1sub x hx) (fun hc => hn (hc ▸ hx))
      rw [hempty, Finset.sum_empty]
      norm_num
  · have hmono : ∀ w ∈ Finset.filter (fun w => ¬((p - 1) / w = 1))
          (Finset.filter (fun w => (p - 1) / w ≤ 9)
            (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1)))),
        ((((p - 1) / w + 1 : ℕ) : ℝ) / ((q / 12 : ℕ) : ℝ)) ^ t ≤ (3 / 4 : ℝ) ^ 12 := by
      intro w hw
      obtain ⟨h1, hmne⟩ := Finset.mem_filter.mp hw
      obtain ⟨h2, hm9⟩ := Finset.mem_filter.mp h1
      obtain ⟨hdx, hpp, hw18⟩ := Finset.mem_filter.mp h2
      obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp hdx
      have hw19 : 19 ≤ w := by omega
      have hwle : w ≤ p - 1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
      have hd1 : 1 ≤ (p - 1) / w := Nat.div_pos hwle (by omega)
      have hm2 : 2 ≤ (p - 1) / w := by omega
      have hρ := dlog_rho_le_three_fourths p q w hprime hp3 hpq hdvd hw19 hpp hm2 hm9
      exact dlog_pow_t_le (by positivity) hρ (by norm_num) ht
    have hinj : ∀ a ∈ Finset.filter (fun w => ¬((p - 1) / w = 1))
          (Finset.filter (fun w => (p - 1) / w ≤ 9)
            (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1)))),
        ∀ b ∈ Finset.filter (fun w => ¬((p - 1) / w = 1))
          (Finset.filter (fun w => (p - 1) / w ≤ 9)
            (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1)))),
        (p - 1) / a = (p - 1) / b → a = b := by
      intro a ha b hb hab
      obtain ⟨h1a, _⟩ := Finset.mem_filter.mp ha
      obtain ⟨h2a, _⟩ := Finset.mem_filter.mp h1a
      obtain ⟨hda, _, _⟩ := Finset.mem_filter.mp h2a
      obtain ⟨h1b, _⟩ := Finset.mem_filter.mp hb
      obtain ⟨h2b, _⟩ := Finset.mem_filter.mp h1b
      obtain ⟨hdb, _, _⟩ := Finset.mem_filter.mp h2b
      obtain ⟨hdvda, _⟩ := Nat.mem_divisors.mp hda
      obtain ⟨hdvdb, hneb⟩ := Nat.mem_divisors.mp hdb
      have ha1 : (p - 1) / a * a = p - 1 := Nat.div_mul_cancel hdvda
      have hb1 : (p - 1) / b * b = p - 1 := Nat.div_mul_cancel hdvdb
      rw [hab] at ha1
      have hble : b ≤ p - 1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hneb) hdvdb
      exact Nat.eq_of_mul_eq_mul_left (Nat.div_pos hble (by omega)) (by rw [ha1, hb1])
    have himg : Finset.image (fun w => (p - 1) / w)
          (Finset.filter (fun w => ¬((p - 1) / w = 1))
            (Finset.filter (fun w => (p - 1) / w ≤ 9)
              (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1)))))
        ⊆ Finset.Icc 2 9 := by
      rw [Finset.image_subset_iff]
      intro x hx
      obtain ⟨h1, hmne⟩ := Finset.mem_filter.mp hx
      obtain ⟨h2, hm9⟩ := Finset.mem_filter.mp h1
      obtain ⟨hdx, _, _⟩ := Finset.mem_filter.mp h2
      obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp hdx
      have hle : x ≤ p - 1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
      have hd1 : 1 ≤ (p - 1) / x := Nat.div_pos hle (by omega)
      exact Finset.mem_Icc.mpr ⟨by omega, hm9⟩
    calc ∑ w ∈ Finset.filter (fun w => ¬((p - 1) / w = 1))
          (Finset.filter (fun w => (p - 1) / w ≤ 9)
            (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1)))),
          ((((p - 1) / w + 1 : ℕ) : ℝ) / ((q / 12 : ℕ) : ℝ)) ^ t
          ≤ ∑ w ∈ Finset.filter (fun w => ¬((p - 1) / w = 1))
            (Finset.filter (fun w => (p - 1) / w ≤ 9)
              (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1)))),
            (3 / 4 : ℝ) ^ 12 := Finset.sum_le_sum hmono
      _ = ∑ m' ∈ Finset.image (fun w => (p - 1) / w)
            (Finset.filter (fun w => ¬((p - 1) / w = 1))
              (Finset.filter (fun w => (p - 1) / w ≤ 9)
                (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1))))),
            (3 / 4 : ℝ) ^ 12 := by
          exact (Finset.sum_image (f := fun _ => (3 / 4 : ℝ) ^ 12)
            (g := fun w => (p - 1) / w)
            (fun a ha b hb hab =>
              hinj a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab)).symm
      _ ≤ ∑ m' ∈ Finset.Icc 2 9, (3 / 4 : ℝ) ^ 12 :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
      _ = 8 * (3 / 4 : ℝ) ^ 12 := by
          rw [Finset.sum_const, dlog_nat_smul_real]
          have hcard : (Finset.Icc 2 9).card = 8 := by decide
          rw [hcard]
          norm_num
  · have hmono : ∀ w ∈ Finset.filter (fun w => ¬((p - 1) / w ≤ 9))
          (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1))),
        ((((p - 1) / w + 1 : ℕ) : ℝ) / ((q / 12 : ℕ) : ℝ)) ^ t
          ≤ (14 / ((w:ℕ):ℝ)) ^ 12 := by
      intro w hw
      obtain ⟨h1, hmge⟩ := Finset.mem_filter.mp hw
      obtain ⟨hdx, _, _⟩ := Finset.mem_filter.mp h1
      obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp hdx
      have hw19 : 19 ≤ w := by omega
      have hm10 : 10 ≤ (p - 1) / w := by omega
      have hρ := dlog_rho_le_div14 p q w hp1 hpq hdvd hw19 hm10
      have hc1 : 14 / ((w:ℕ):ℝ) ≤ 1 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < ((w:ℕ):ℝ))]
        have hwR : (14:ℝ) ≤ ((w:ℕ):ℝ) := by exact_mod_cast (show 14 ≤ w by omega)
        linarith
      exact dlog_pow_t_le (by positivity) hρ hc1 ht
    have hsub : Finset.filter (fun w => ¬((p - 1) / w ≤ 9))
          (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1)))
        ⊆ Finset.Icc 19 (p - 1) := by
      intro x hx
      obtain ⟨h1, _⟩ := Finset.mem_filter.mp hx
      obtain ⟨hdx, _, hw18⟩ := Finset.mem_filter.mp h1
      obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp hdx
      exact Finset.mem_Icc.mpr ⟨by omega, Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd⟩
    calc ∑ w ∈ Finset.filter (fun w => ¬((p - 1) / w ≤ 9))
          (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1))),
          ((((p - 1) / w + 1 : ℕ) : ℝ) / ((q / 12 : ℕ) : ℝ)) ^ t
          ≤ ∑ w ∈ Finset.filter (fun w => ¬((p - 1) / w ≤ 9))
            (Finset.filter (fun w => dlogIsPrimePower w ∧ 18 < w) (Nat.divisors (p - 1))),
            (14 / ((w:ℕ):ℝ)) ^ 12 := Finset.sum_le_sum hmono
      _ ≤ ∑ w ∈ Finset.Icc 19 (p - 1), (14 / ((w:ℕ):ℝ)) ^ 12 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∑ w ∈ Finset.Icc 19 (p - 1), 14 ^ 12 * (1 / ((w:ℕ):ℝ) ^ 12) :=
          Finset.sum_congr rfl fun _ _ => by ring
      _ = 14 ^ 12 * ∑ w ∈ Finset.Icc 19 (p - 1), 1 / ((w:ℕ):ℝ) ^ 12 :=
          (Finset.mul_sum (s := Finset.Icc 19 (p - 1)) (f := fun w => 1 / ((w:ℕ):ℝ) ^ 12)
            (a := (14:ℝ) ^ 12)).symm
      _ ≤ 14 ^ 12 * (1 / (11 * ((18:ℝ) ^ 11))) :=
          mul_le_mul_of_nonneg_left (dlog_sum_inv_pow_le (p - 1)) (by positivity)
      _ = 14 ^ 12 / (11 * ((18:ℝ) ^ 11)) := by ring

/-- Establishes the divisor-sum bound and the strict one-half tail estimate for at least twelve
uniform good samples in the discrete-logarithm analysis of [Shor1997]. -/
theorem dlogTSampleTail : DlogTSampleTail := by
  intro p q t _ _ hprime hp hpq hq
  refine ⟨dlog_tsample_union_bound p q t hprime hp hpq hq, ?_⟩
  intro ht
  exact lt_of_le_of_lt
    (le_trans (dlog_tsample_union_bound p q t hprime hp hpq hq)
      (dlog_tsample_sum_bound p q t hprime hp hpq ht)) dlog_tsample_constant

end Qatlib.Concepts.PeriodSampling.DlogDivBudget
