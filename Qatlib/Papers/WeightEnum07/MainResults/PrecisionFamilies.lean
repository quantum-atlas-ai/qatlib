/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.Basic

/-!
# Modular orders and fixed-precision families

The multiplicative order `ordMod` of `q` modulo `q ^ k - 1` is exactly `k` for `q ≥ 2` and
positive `k`. The module also establishes arbitrarily large exponents satisfying the stated
fixed-precision inequality.

This development forms part of the formalization of [GeraciVanBussel2007].

## Main statements

* `ordMod_self`: The multiplicative order of `q` modulo `q ^ k - 1` is `k` for `q ≥ 2` and
  positive `k`.
* `exists_precision_exponent`: For `q ≥ 2` and `0 < ε < 1`, arbitrarily large natural exponents
  `k` satisfy `ε ≤ q ^ (k / 2 - 1) / 4`, with the exponent computed in natural numbers.

## References

* [Geraci and Van Bussel, 2007][GeraciVanBussel2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeightEnum07.MainResults

open Filter

/-- For `q ≥ 2` and positive `k`, the numbers `q` and `q ^ k - 1` are coprime. -/
lemma coprime_pow_sub_one {q k : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) : Nat.Coprime q (q ^ k - 1) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hqk_ge : 1 ≤ q ^ k := le_trans (by omega : 1 ≤ q) (le_self_pow (by omega) (by omega))
  set g := Nat.gcd q (q ^ k - 1) with hg
  have h1 : g ∣ q := Nat.gcd_dvd_left _ _
  have h2 : g ∣ q ^ k - 1 := Nat.gcd_dvd_right _ _
  have h3 : g ∣ q ^ k :=
    dvd_trans h1 (by
      have hk' : k = (k - 1) + 1 := by omega
      rw [hk', pow_succ]
      exact dvd_mul_left q (q ^ (k - 1)))
  have h4 : g ∣ q ^ k - (q ^ k - 1) := Nat.dvd_sub h3 h2
  have h5 : q ^ k - (q ^ k - 1) = 1 := by omega
  rw [h5] at h4
  exact Nat.dvd_one.mp h4

/-- The multiplicative order of the unit represented by `q` modulo `n`. -/
def ordMod (q n : ℕ) (h : Nat.Coprime q n) : ℕ := orderOf (ZMod.unitOfCoprime q h)

/-- The multiplicative order of `q` modulo `q ^ k - 1` is `k` for `q ≥ 2` and positive `k`. See
[GeraciVanBussel2007]. -/
theorem ordMod_self {q k : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) :
    ordMod q (q ^ k - 1) (coprime_pow_sub_one hq hk) = k := by
  classical
  have hqk_ge : 1 ≤ q ^ k := le_trans (by omega : 1 ≤ q) (le_self_pow (by omega) (by omega))
  have hcop := coprime_pow_sub_one hq hk
  set n := q ^ k - 1 with hn
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime q hcop
  have hcoe : (u : ZMod n) = (q : ZMod n) := ZMod.coe_unitOfCoprime q hcop
  have hqk_eq : q ^ k = n + 1 := by rw [hn]; omega
  have hqk : (q : ZMod n) ^ k = 1 := by
    rw [← Nat.cast_pow, hqk_eq, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]
  have huk : u ^ k = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hcoe]
    exact hqk
  refine (orderOf_eq_iff (n := k) (by omega)).2 ⟨huk, ?_⟩
  intro m hmk hmpos hm1
  have hqm : (q : ZMod n) ^ m = 1 := by
    have := congrArg (fun w : (ZMod n)ˣ => (w : ZMod n)) hm1
    simpa [Units.val_pow_eq_pow_val, hcoe] using this
  have hqm' : ((q ^ m : ℕ) : ZMod n) = 1 := by simpa [Nat.cast_pow] using hqm
  have hqm_ge : 1 ≤ q ^ m := le_trans (by omega : 1 ≤ q) (le_self_pow (by omega) (by omega))
  have hzero : ((q ^ m - 1 : ℕ) : ZMod n) = 0 := by
    rw [Nat.cast_sub hqm_ge, hqm']
    ring
  have hdvd : n ∣ q ^ m - 1 := (ZMod.natCast_eq_zero_iff (q ^ m - 1) n).mp hzero
  have hlt : q ^ m - 1 < n := by
    have h1 : q ^ m ≤ q ^ (k - 1) := by
      apply Nat.pow_le_pow_right (by omega)
      omega
    have h2 : q ^ (k - 1) < q ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
    rw [hn]; omega
  have hpos : 0 < q ^ m - 1 := by
    have : 2 ≤ q ^ m := le_trans hq (le_self_pow (by omega) (by omega))
    omega
  exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)

/-- For `q ≥ 2` and `0 < ε < 1`, arbitrarily large natural exponents `k` satisfy `ε ≤ q ^ (k / 2
- 1) / 4`, with the exponent computed in natural numbers. See [GeraciVanBussel2007]. -/
theorem exists_precision_exponent {q : ℕ} (hq : 2 ≤ q) {ε : ℝ} (_hε0 : 0 < ε) (_hε1 : ε < 1) :
    ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ ε ≤ (q : ℝ) ^ (k / 2 - 1) / 4 := by
  intro K
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have htend : Tendsto (fun m : ℕ => (q : ℝ) ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hq1
  have hev : ∀ᶠ m : ℕ in atTop, ε ≤ (q : ℝ) ^ m / 4 := by
    have : Tendsto (fun m : ℕ => (q : ℝ) ^ m / 4) atTop atTop :=
      htend.atTop_div_const (by norm_num)
    exact this.eventually (eventually_ge_atTop ε)
  obtain ⟨a, ha⟩ := eventually_atTop.mp hev
  set M := max a (max K 2) with hM
  have hMge : a ≤ M := le_max_left _ _
  refine ⟨2 * (M + 1), by omega, ?_⟩
  have hdiv : 2 * (M + 1) / 2 - 1 = M := by omega
  rw [hdiv]
  exact ha M hMge

end Qatlib.Papers.WeightEnum07.MainResults
