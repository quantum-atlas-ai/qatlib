/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurve04.MainResults.Defs

/-!
# A lower bound for prime-divisor counts

Bounds on proper divisors control the sums of ordinary and half powers appearing in the
orbit-count identity. Combining these estimates with `PointCountWeil` gives
`primeDivisorCount_lower_bound` for every positive extension degree.

This development forms part of the formalization of [Kedlaya2006].

## Main statements

* `sum_pow_properDivisors_le`: For `q ≥ 2` and positive `e`, the sum of `q ^ i` over proper
  divisors of `e` is at most `q ^ (e - 1)`.
* `primeDivisorCount_lower_bound`: The point-count bounds and orbit-count identity imply the
  prime-divisor lower bound `(q ^ e * (1 - q⁻¹) - 4 * g * halfPower q e) / e` for positive `e`
  and `q ≥ 2`.

## References

* [Kedlaya, 2006][Kedlaya2006]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

open Qatlib.Papers.ZetaCurve04.MainResults.Defs

namespace Qatlib.Papers.ZetaCurve04.MainResults.Lemma6

/-- Removing `e` from its divisor finset gives its proper-divisor finset. -/
theorem divisors_erase_self (e : ℕ) : e.divisors.erase e = e.properDivisors := by
  ext i
  rw [Finset.mem_erase, Nat.mem_divisors, Nat.mem_properDivisors]
  constructor
  · rintro ⟨hne, hdvd, he0⟩
    exact ⟨hdvd, lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero he0) hdvd) hne⟩
  · rintro ⟨hdvd, hlt⟩
    exact ⟨ne_of_lt hlt, hdvd, by omega⟩

/-- Every proper divisor of `e` is at most `e - 1`. -/
theorem properDivisors_le_pred (e : ℕ) : ∀ i ∈ e.properDivisors, i ≤ e - 1 := by
  intro i hi
  have h := (Nat.mem_properDivisors.mp hi).2
  omega

/-- Every proper divisor `i` of positive `e` satisfies `2 * i ≤ e`. -/
theorem properDivisors_le_half {e : ℕ} (he : 1 ≤ e) :
    ∀ i ∈ e.properDivisors, 2 * i ≤ e := by
  intro i hi
  obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hi
  have hi0 : 0 < i := Nat.pos_of_dvd_of_pos hdvd (by omega)
  obtain ⟨j, rfl⟩ := hdvd
  have hj : 1 < j := (Nat.lt_mul_iff_one_lt_right hi0).mp hlt
  calc 2 * i = i * 2 := by ring
    _ ≤ i * j := Nat.mul_le_mul_left i hj

/-- For `q ≥ 2` and positive `e`, the sum of `q ^ i` over proper divisors of `e` is at most `q ^
(e - 1)`. See [Kedlaya2006]. -/
theorem sum_pow_properDivisors_le (q e : ℕ) (hq : 2 ≤ q) (he : 1 ≤ e) :
    (∑ i ∈ e.properDivisors, (q : ℝ) ^ i) ≤ (q : ℝ) ^ (e - 1) := by
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rcases eq_or_lt_of_le he with rfl | he2
  · simp
  rcases (show e = 2 ∨ 3 ≤ e by omega) with rfl | he3
  · have : (2 : ℕ).properDivisors = {1} := by decide
    rw [this]
    simp
  · have hsub : e.properDivisors ⊆ Finset.range (e - 1) := by
      intro i hi
      rw [Finset.mem_range]
      have h2 := properDivisors_le_half (by omega : 1 ≤ e) i hi
      omega
    have hs : (∑ i ∈ e.properDivisors, (q : ℝ) ^ i)
        ≤ ∑ i ∈ Finset.range (e - 1), (q : ℝ) ^ i := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro i _ _
      positivity
    have hgeom : (∑ i ∈ Finset.range (e - 1), (q : ℝ) ^ i) * ((q : ℝ) - 1)
        = (q : ℝ) ^ (e - 1) - 1 := by
      have := geom_sum_mul (q : ℝ) (e - 1)
      simpa using this
    have hS_nonneg : 0 ≤ ∑ i ∈ Finset.range (e - 1), (q : ℝ) ^ i := by positivity
    have hqm1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      linarith
    have hbound : (∑ i ∈ Finset.range (e - 1), (q : ℝ) ^ i) ≤ (q : ℝ) ^ (e - 1) := by
      have hSle : (∑ i ∈ Finset.range (e - 1), (q : ℝ) ^ i)
          ≤ (∑ i ∈ Finset.range (e - 1), (q : ℝ) ^ i) * ((q : ℝ) - 1) := by
        nlinarith
      have hqpow_le : (q : ℝ) ^ (e - 1) - 1 ≤ (q : ℝ) ^ (e - 1) := by
        have : (0 : ℝ) ≤ (q : ℝ) ^ (e - 1) := by positivity
        linarith
      calc (∑ i ∈ Finset.range (e - 1), (q : ℝ) ^ i)
          ≤ (∑ i ∈ Finset.range (e - 1), (q : ℝ) ^ i) * ((q : ℝ) - 1) := hSle
        _ = (q : ℝ) ^ (e - 1) - 1 := hgeom
        _ ≤ (q : ℝ) ^ (e - 1) := hqpow_le
    exact le_trans hs hbound

/-- For `q ≥ 2` and positive `e`, the sum of `halfPower q i` over proper divisors of `e` is at
most `halfPower q e`. See [Kedlaya2006]. -/
theorem sum_halfPower_properDivisors_le (q e : ℕ) (hq : 2 ≤ q) (he : 1 ≤ e) :
    (∑ i ∈ e.properDivisors, halfPower q i) ≤ halfPower q e := by
  have hpow : ∀ i, halfPower q i = (Real.sqrt (q : ℝ)) ^ i := halfPower_eq_sqrt_pow q
  simp only [hpow]
  set r : ℝ := Real.sqrt (q : ℝ) with hrdef
  have hr2 : r ^ 2 = (q : ℝ) := by
    rw [hrdef]; exact Real.sq_sqrt (by positivity)
  have hq2' : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hr2ge : (2 : ℝ) ≤ r ^ 2 := by rw [hr2]; exact hq2'
  have hr1 : 1 ≤ r := by
    have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt h1
      _ = r := by rw [hrdef]
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  rcases (show e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7 ∨ 8 ≤ e by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | he8
  · have hset : (1 : ℕ).properDivisors = ∅ := by decide
    rw [hset]
    simp
    positivity
  · have hsum : (∑ i ∈ (2 : ℕ).properDivisors, r ^ i) = r := by
      rw [show (2 : ℕ).properDivisors = {1} from by decide]
      simp
    rw [hsum]
    simpa using pow_le_pow_right₀ hr1 (show 1 ≤ 2 by norm_num)
  · have hsum : (∑ i ∈ (3 : ℕ).properDivisors, r ^ i) = r := by
      rw [show (3 : ℕ).properDivisors = {1} from by decide]
      simp
    rw [hsum]
    simpa using pow_le_pow_right₀ hr1 (show 1 ≤ 3 by norm_num)
  · have hsum : (∑ i ∈ (4 : ℕ).properDivisors, r ^ i) = r + r ^ 2 := by
      rw [show (4 : ℕ).properDivisors = {1, 2} from by decide]
      simp
    rw [hsum]
    nlinarith [hr2ge, hr1, hrpos, sq_nonneg r]
  · have hsum : (∑ i ∈ (5 : ℕ).properDivisors, r ^ i) = r := by
      rw [show (5 : ℕ).properDivisors = {1} from by decide]
      simp
    rw [hsum]
    simpa using pow_le_pow_right₀ hr1 (show 1 ≤ 5 by norm_num)
  · have hsum : (∑ i ∈ (6 : ℕ).properDivisors, r ^ i) = r + r ^ 2 + r ^ 3 := by
      rw [show (6 : ℕ).properDivisors = {1, 2, 3} from by decide]
      simp
      ring
    rw [hsum]
    have hr3 : 2 * r ≤ r ^ 3 := by nlinarith [hr2ge, hrpos]
    have hA : 2 * r ^ 3 ≤ r ^ 5 := by
      have hm := mul_le_mul_of_nonneg_left hr3 (show (0 : ℝ) ≤ r ^ 2 by positivity)
      calc 2 * r ^ 3 = r ^ 2 * (2 * r) := by ring
        _ ≤ r ^ 2 * r ^ 3 := hm
        _ = r ^ 5 := by ring
    have h2r1 : (0 : ℝ) ≤ 2 * r - 1 := by linarith
    have hprod : 2 * (2 * r - 1) ≤ r ^ 2 * (2 * r - 1) :=
      mul_le_mul_of_nonneg_right hr2ge h2r1
    have hB : r ^ 2 + r + 1 ≤ 2 * r ^ 3 := by nlinarith [hprod, hr1, hrpos]
    have h5 : r ^ 2 + r + 1 ≤ r ^ 5 := le_trans hB hA
    have hmul := mul_le_mul_of_nonneg_left h5 (le_of_lt hrpos)
    calc r + r ^ 2 + r ^ 3 = r * (r ^ 2 + r + 1) := by ring
      _ ≤ r * r ^ 5 := hmul
      _ = r ^ 6 := by ring
  · have hsum : (∑ i ∈ (7 : ℕ).properDivisors, r ^ i) = r := by
      rw [show (7 : ℕ).properDivisors = {1} from by decide]
      simp
    rw [hsum]
    simpa using pow_le_pow_right₀ hr1 (show 1 ≤ 7 by norm_num)
  · have hsub : e.properDivisors ⊆ Finset.Icc 1 (e / 2) := by
      intro i hi
      rw [Finset.mem_Icc]
      obtain ⟨hdvd, -⟩ := Nat.mem_properDivisors.mp hi
      have hpos : 0 < i := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hhalf := properDivisors_le_half (by omega : 1 ≤ e) i hi
      omega
    have hle : (∑ i ∈ e.properDivisors, r ^ i)
        ≤ ∑ i ∈ Finset.Icc 1 (e / 2), r ^ i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => pow_nonneg (le_of_lt hrpos) i)
    have hsub2 : Finset.Icc 1 (e / 2) ⊆ Finset.range (e / 2 + 1) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      rw [Finset.mem_range]
      omega
    have hle2 : (∑ i ∈ Finset.Icc 1 (e / 2), r ^ i)
        ≤ ∑ i ∈ Finset.range (e / 2 + 1), r ^ i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub2
        (fun i _ _ => pow_nonneg (le_of_lt hrpos) i)
    have hgeom : (∑ i ∈ Finset.range (e / 2 + 1), r ^ i) * (r - 1)
        = r ^ (e / 2 + 1) - 1 := by
      simpa using geom_sum_mul r (e / 2 + 1)
    have hrgt1 : 1 < r := by nlinarith [hr2ge, hrpos]
    have hrm1pos : 0 < r - 1 := by linarith
    have hsum_le : (∑ i ∈ Finset.range (e / 2 + 1), r ^ i)
        ≤ r ^ (e / 2 + 1) / (r - 1) := by
      rw [le_div_iff₀ hrm1pos, hgeom]
      have : (0 : ℝ) ≤ r ^ (e / 2 + 1) := by positivity
      linarith
    have hratio : r / (r - 1) ≤ 4 := by
      rw [div_le_iff₀ hrm1pos]
      nlinarith [hr2ge, hr1]
    have hm4 : 4 ≤ e / 2 := by omega
    have hr4 : (4 : ℝ) ≤ r ^ (e / 2) := by
      have h4 : (4 : ℝ) ≤ r ^ 4 := by
        have hsq : (2 : ℝ) * 2 ≤ r ^ 2 * r ^ 2 :=
          mul_le_mul hr2ge hr2ge (by norm_num) (by positivity)
        calc (4 : ℝ) = 2 * 2 := by norm_num
          _ ≤ r ^ 2 * r ^ 2 := hsq
          _ = r ^ 4 := by ring
      exact le_trans h4 (pow_le_pow_right₀ hr1 hm4)
    have hfin : r ^ (e / 2 + 1) / (r - 1) ≤ r ^ (e / 2) * 4 := by
      rw [pow_succ, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    have step2 : r ^ (e / 2) * 4 ≤ r ^ (e / 2) * r ^ (e / 2) :=
      mul_le_mul_of_nonneg_left hr4 (by positivity)
    have step3 : r ^ (e / 2) * r ^ (e / 2) = r ^ (2 * (e / 2)) := by
      rw [← pow_add]
      congr 1
      ring
    have step4 : r ^ (2 * (e / 2)) ≤ r ^ e :=
      pow_le_pow_right₀ hr1 (by omega)
    calc (∑ i ∈ e.properDivisors, r ^ i)
        ≤ ∑ i ∈ Finset.Icc 1 (e / 2), r ^ i := hle
      _ ≤ ∑ i ∈ Finset.range (e / 2 + 1), r ^ i := hle2
      _ ≤ r ^ (e / 2 + 1) / (r - 1) := hsum_le
      _ ≤ r ^ (e / 2) * 4 := hfin
      _ ≤ r ^ (e / 2) * r ^ (e / 2) := step2
      _ = r ^ (2 * (e / 2)) := step3
      _ ≤ r ^ e := step4

/-- The point-count bounds and orbit-count identity imply the prime-divisor lower bound `(q ^ e
* (1 - q⁻¹) - 4 * g * halfPower q e) / e` for positive `e` and `q ≥ 2`. See [Kedlaya2006]. -/
theorem primeDivisorCount_lower_bound (C : CurveData)
    (hWeil : PointCountWeil C) (hOrbit : OrbitCountIdentity C)
    (hq2 : 2 ≤ C.q) (e : ℕ) (he : 1 ≤ e) :
    (C.primeDivisorCount e : ℝ) ≥
      (1 / (e : ℝ)) *
        ((C.q : ℝ) ^ e * (1 - ((C.q : ℝ))⁻¹) - 4 * (C.g : ℝ) * halfPower C.q e) := by
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hene : (e : ℝ) ≠ 0 := ne_of_gt hepos

  set q : ℝ := (C.q : ℝ) with hqdef
  set g : ℝ := (C.g : ℝ) with hgdef
  set P : ℕ → ℕ := C.primeDivisorCount with hPdef
  set pc : ℕ → ℕ := C.pointCount with hpcdef
  set h : ℕ → ℝ := halfPower C.q with hhdef
  have hqpos : 0 < q := by positivity

  have horb := hOrbit e he
  have herase : e.divisors.erase e = e.properDivisors := divisors_erase_self e
  have hmem : e ∈ e.divisors := Nat.mem_divisors_self e (by omega)

  have hsplit : (pc e : ℝ) = (e : ℝ) * (P e : ℝ) + ∑ i ∈ e.properDivisors, (i : ℝ) * (P i : ℝ) := by
    have hsum := (Finset.add_sum_erase e.divisors (fun i => (i : ℝ) * (P i : ℝ)) hmem)
    rw [herase, ← horb] at hsum
    linarith [hsum]

  have hterm : ∀ i ∈ e.properDivisors, (i : ℝ) * (P i : ℝ) ≤ (pc i : ℝ) := by
    intro i hi
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hi
    have hi0 : 0 < i := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hi1 : 1 ≤ i := hi0
    have hoi := hOrbit i hi1
    have himem : i ∈ i.divisors := Nat.mem_divisors_self i (by omega)
    have hle : (i : ℝ) * (P i : ℝ) ≤ ∑ j ∈ i.divisors, (j : ℝ) * (P j : ℝ) := by
      have := Finset.single_le_sum (f := fun j : ℕ => (j : ℝ) * (P j : ℝ))
        (fun j _ => by positivity) himem
      simpa using this
    linarith [hoi, hle]
  have hSle : (∑ i ∈ e.properDivisors, (i : ℝ) * (P i : ℝ))
      ≤ ∑ i ∈ e.properDivisors, (pc i : ℝ) :=
    Finset.sum_le_sum hterm

  have hWe := (hWeil e he).1
  have hWi : ∀ i ∈ e.properDivisors, (pc i : ℝ) ≤ q ^ i + 2 * g * h i := by
    intro i hi
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hi
    have hi0 : 0 < i := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hi1 : 1 ≤ i := hi0
    exact (hWeil i hi1).2
  have hTle : (∑ i ∈ e.properDivisors, (pc i : ℝ))
      ≤ ∑ i ∈ e.properDivisors, (q ^ i + 2 * g * h i) :=
    Finset.sum_le_sum hWi

  have hsplit2 : (∑ i ∈ e.properDivisors, (q ^ i + 2 * g * h i))
      = (∑ i ∈ e.properDivisors, q ^ i) + 2 * g * (∑ i ∈ e.properDivisors, h i) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hpow := sum_pow_properDivisors_le C.q e hq2 he
  have hhalf := sum_halfPower_properDivisors_le C.q e hq2 he
  have hsumPowR : (∑ i ∈ e.properDivisors, q ^ i) ≤ q ^ (e - 1) := hpow
  have hsumHalfR : (∑ i ∈ e.properDivisors, h i) ≤ h e := hhalf
  have hg_nonneg : 0 ≤ g := by positivity

  have hkey : (e : ℝ) * (P e : ℝ) ≥ q ^ e - 2 * g * h e - (q ^ (e - 1) + 2 * g * h e) := by
    have hA : (pc e : ℝ) ≥ q ^ e - 2 * g * h e := hWe
    have hB : (∑ i ∈ e.properDivisors, (pc i : ℝ)) ≤ q ^ (e - 1) + 2 * g * h e := by
      calc (∑ i ∈ e.properDivisors, (pc i : ℝ))
          ≤ (∑ i ∈ e.properDivisors, (q ^ i + 2 * g * h i)) := hTle
        _ = (∑ i ∈ e.properDivisors, q ^ i) + 2 * g * (∑ i ∈ e.properDivisors, h i) := hsplit2
        _ ≤ q ^ (e - 1) + 2 * g * h e := by nlinarith [hsumPowR, hsumHalfR, hg_nonneg]
    have hdecomp : (pc e : ℝ) - (∑ i ∈ e.properDivisors, (pc i : ℝ))
        ≤ (e : ℝ) * (P e : ℝ) := by
      have := hsplit; linarith [hSle]
    linarith [hA, hB, hdecomp]

  have hq_ne : q ≠ 0 := ne_of_gt hqpos
  have hqpow : q ^ e = q ^ (e - 1) * q := by
    exact (pow_sub_one_mul (by omega : e ≠ 0) q).symm
  have hqe : q ^ e * q⁻¹ = q ^ (e - 1) := by
    have h1 : q ^ (e - 1) * q = q ^ e := pow_sub_one_mul (by omega : e ≠ 0) q
    rw [← h1, mul_assoc, mul_inv_cancel₀ hq_ne, mul_one]
  have hrewrite : q ^ e - 2 * g * h e - (q ^ (e - 1) + 2 * g * h e)
      = q ^ e * (1 - q⁻¹) - 4 * g * h e := by
    rw [mul_sub, mul_one, hqe]
    ring
  rw [hrewrite] at hkey

  have hmul : (1 / (e : ℝ)) *
      (q ^ e * (1 - q⁻¹) - 4 * g * h e)
      = (q ^ e * (1 - q⁻¹) - 4 * g * h e) / (e : ℝ) := by ring
  rw [ge_iff_le, hmul, div_le_iff₀ hepos]
  linarith [hkey]

end Qatlib.Papers.ZetaCurve04.MainResults.Lemma6
