/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreFullBoundaryStat

/-!
# Corrected numerator and Legendre boundary for period recovery

`legendreFullBoundary_answer` recovers a continued-fraction convergent from the rounded modular
quotient, while `legendreFullBoundary_false` refutes the original residue-distance numerator.
The module also isolates the denominator-one obstruction to a closed Legendre inequality in the
period-recovery setting of [Cornwell2014].

## Main statements

* `legendreFullBoundary_false`: The original modular recovery contract using residue distance as
  the numerator is false.
* `legendre_correct_numerator`: If P² ≤ N and |Py−Na| ≤ P/2, then a/P is a convergent of y/N and
  its reduced denominator divides P.
* `legendreFullBoundary_answer`: Proves the corrected rounded-numerator recovery contract
  `LegendreFullBoundary`; see [Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.AmpTransform.LegendreWindow

/-- The rational 1/5 is not a continued-fraction convergent of 25/63. -/
private theorem convergent_25_63_ne (n : ℕ) :
    (25 / 63 : ℝ).convergent n ≠ (1 / 5 : ℚ) := by
  have h1 (m : ℕ) : (25 / 63 : ℝ).convergent (m + 1) =
      ((63 / 25 : ℝ).convergent m)⁻¹ := by
    rw [Real.convergent_succ]
    norm_num [Int.fract]
  have h2 (m : ℕ) : (63 / 25 : ℝ).convergent (m + 1) =
      2 + ((25 / 13 : ℝ).convergent m)⁻¹ := by
    rw [Real.convergent_succ]
    norm_num [Int.fract]
  have h3 (m : ℕ) : (25 / 13 : ℝ).convergent (m + 1) =
      1 + ((13 / 12 : ℝ).convergent m)⁻¹ := by
    rw [Real.convergent_succ]
    norm_num [Int.fract]
  have h4 (m : ℕ) : (13 / 12 : ℝ).convergent (m + 1) =
      1 + ((12 : ℝ).convergent m)⁻¹ := by
    rw [Real.convergent_succ]
    norm_num [Int.fract]
  cases n with
  | zero => norm_num
  | succ n =>
    rw [h1]
    cases n with
    | zero => norm_num
    | succ n =>
      rw [h2]
      cases n with
      | zero => norm_num
      | succ n =>
        rw [h3]
        cases n with
        | zero => norm_num
        | succ n =>
          rw [h4]
          have hi : (12 : ℝ).convergent n = 12 :=
            Real.convergent_of_int (ξ := 12) n
          rw [hi]
          norm_num

/-- The original proposed modular recovery condition, identifying the recovered rational with
residue distance divided by P and requiring a continued-fraction denominator dividing P. -/
def LegendreFullBoundaryOriginal : Prop :=
  ∀ (N P y : ℕ), 0 < N → 0 < P → P ^ 2 ≤ N → 0 < y → y < N →
    let r := (P * y) % N
    let d := min r (N - r)
    d ≤ P / 2 →
    ∃ a b : ℕ, 0 < b ∧ Nat.Coprime a b ∧ b ∣ P ∧
      ((a : ℚ) / (b : ℚ) = (d : ℚ) / (P : ℚ)) ∧
      ∃ n : ℕ, ((a : ℚ) / (b : ℚ)) = (((y : ℝ) / (N : ℝ)).convergent n)

/-- The original modular recovery contract using residue distance as the numerator is false. -/
theorem legendreFullBoundary_false : ¬ LegendreFullBoundaryOriginal := by
  intro h
  obtain ⟨a, b, _hb, _hcop, _hdiv, hab, n, hn⟩ :=
    h 63 5 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  norm_num at hab hn
  exact convergent_25_63_ne n (hn.symm.trans hab)

/-- If P² ≤ N and |Py−Na| ≤ P/2, then a/P is a convergent of y/N and its reduced denominator
divides P. -/
theorem legendre_correct_numerator (N P y a : ℕ) (hN : 0 < N) (hP : 0 < P)
    (hsize : P ^ 2 ≤ N)
    (hwindow : |(P : ℝ) * y - (N : ℝ) * a| ≤ (P : ℝ) / 2) :
    ((a : ℚ) / P).den ∣ P ∧
      ∃ n : ℕ, (a : ℚ) / P = ((y : ℝ) / N).convergent n := by
  let q : ℚ := (a : ℚ) / P
  have hdiv : q.den ∣ P := by
    have hd := Rat.den_dvd (a : ℤ) (P : ℤ)
    simpa only [Rat.divInt_eq_div, Int.cast_natCast, Int.natCast_dvd_natCast] using hd
  have hden : q.den ≤ P := Nat.le_of_dvd hP hdiv
  have hp : (0 : ℝ) < P := by exact_mod_cast hP
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hdp : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hleg : |(y : ℝ) / N - (q : ℝ)| < 1 / (2 * (q.den : ℝ) ^ 2) := by
    have hq : (q : ℝ) = (a : ℝ) / P := by simp [q]
    rw [hq]
    have herr : |(y : ℝ) / N - (a : ℝ) / P| =
        |(P : ℝ) * y - (N : ℝ) * a| / ((N : ℝ) * P) := by
      rw [← abs_of_pos (mul_pos hn hp), ← abs_div]
      congr 1
      field_simp
    rw [herr]
    by_cases he : N = P ^ 2
    · have hw : |((y : ℤ) - (P : ℤ) * a : ℤ)| < 1 := by
        have heR : (N : ℝ) = (P : ℝ) ^ 2 := by exact_mod_cast he
        have hw' : |(P : ℝ) * ((y : ℝ) - (P : ℝ) * a)| ≤ (P : ℝ) / 2 := by
          have hid : (P : ℝ) * ((y : ℝ) - (P : ℝ) * a) =
              (P : ℝ) * y - (P : ℝ) ^ 2 * a := by ring
          rw [hid, ← heR]
          exact hwindow
        rw [abs_mul, abs_of_pos hp] at hw'
        have hsmall : |(y : ℝ) - (P : ℝ) * a| < 1 := by nlinarith
        exact_mod_cast hsmall
      have hz : (y : ℤ) - (P : ℤ) * a = 0 := by
        have hab := abs_lt.mp hw
        omega
      have hy : y = P * a := by exact_mod_cast (sub_eq_zero.mp hz)
      have hzR : (P : ℝ) * y - (N : ℝ) * a = 0 := by
        rw [hy, he]
        push_cast
        ring
      rw [hzR, abs_zero, zero_div]
      positivity
    · have hs : (P : ℝ) ^ 2 < N := by exact_mod_cast (show P ^ 2 < N by omega)
      have hd : (q.den : ℝ) ≤ P := by exact_mod_cast hden
      have hbound : 1 / (2 * (N : ℝ)) < 1 / (2 * (q.den : ℝ) ^ 2) := by
        apply one_div_lt_one_div_of_lt (by positivity)
        nlinarith
      apply lt_of_le_of_lt _ hbound
      apply (div_le_iff₀ (mul_pos hn hp)).mpr
      calc
        |(P : ℝ) * y - (N : ℝ) * a| ≤ (P : ℝ) / 2 := hwindow
        _ = 1 / (2 * (N : ℝ)) * ((N : ℝ) * P) := by field_simp
  exact ⟨hdiv, Real.exists_rat_eq_convergent hleg⟩

/-- Proves the corrected rounded-numerator recovery contract `LegendreFullBoundary`; see
[Cornwell2014]. -/
theorem legendreFullBoundary_answer : LegendreFullBoundary := by
  intro N P y hN hP hsize _hy _hyN
  dsimp only
  intro hd
  let r := (P * y) % N
  let t := (P * y) / N
  let a := t + if r ≤ N - r then 0 else 1
  have hr : r < N := Nat.mod_lt _ hN
  have he : (P : ℝ) * y = (N : ℝ) * t + r := by
    have hn := Nat.div_add_mod (P * y) N
    exact_mod_cast hn.symm
  have hdist : |(P : ℝ) * y - (N : ℝ) * a| = (min r (N - r) : ℕ) := by
    by_cases hh : r ≤ N - r
    · simp only [a, if_pos hh, add_zero, min_eq_left hh]
      have hz : (P : ℝ) * y - (N : ℝ) * t = r := by linarith
      rw [hz, abs_of_nonneg (Nat.cast_nonneg _)]
    · simp only [a, if_neg hh, min_eq_right (by omega : N - r ≤ r)]
      rw [Nat.cast_sub (by omega : r ≤ N)]
      push_cast
      have hz : (P : ℝ) * y - (N : ℝ) * ((t : ℝ) + 1) = (r : ℝ) - N := by
        nlinarith
      have hrR : (r : ℝ) ≤ N := by exact_mod_cast hr.le
      rw [hz, abs_of_nonpos (by linarith)]
      ring
  have hwin : |(P : ℝ) * y - (N : ℝ) * a| ≤ (P : ℝ) / 2 := by
    rw [hdist]
    have hh : 2 * min r (N - r) ≤ P := by change min r (N - r) ≤ P / 2 at hd; omega
    have hhR : 2 * ((min r (N - r) : ℕ) : ℝ) ≤ P := by exact_mod_cast hh
    linarith
  obtain ⟨hdiv, n, hn⟩ := legendre_correct_numerator N P y a hN hP hsize hwin
  let q : ℚ := (a : ℚ) / P
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
  have hcast : (q.num.natAbs : ℚ) = q.num := by
    have hh : (q.num.natAbs : ℤ) = q.num := by rw [Int.natCast_natAbs, abs_of_nonneg hnum]
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hh
  have heq : (q.num.natAbs : ℚ) / q.den = q := by rw [hcast, q.num_div_den]
  refine ⟨q.num.natAbs, q.den, q.den_pos, q.reduced, hdiv, heq, n, ?_⟩
  exact heq.trans hn

/-- The non-strict Legendre approximation bound alone does not ensure that a rational is a
continued-fraction convergent. -/
theorem legendre_source_nonstrict_boundary_false :
    ¬ (∀ (ξ : ℝ) (q : ℚ), |ξ - (q : ℝ)| ≤ 1 / (2 * (q.den : ℝ) ^ 2) →
      ∃ n : ℕ, q = ξ.convergent n) := by
  intro h
  obtain ⟨n, hn⟩ := h (1 / 2) 1 (by norm_num)
  cases n with
  | zero => norm_num at hn
  | succ n =>
    rw [Real.convergent_succ] at hn
    norm_num [Int.fract] at hn
    have hi : (2 : ℝ).convergent n = 2 := Real.convergent_of_int (ξ := 2) n
    rw [hi] at hn
    norm_num at hn

/-- A rational of denominator at least two satisfying the non-strict Legendre bound is a
continued-fraction convergent. See [Cornwell2014]. -/
theorem legendre_nonstrict_den_ge_two (ξ : ℝ) (q : ℚ) (hq : 2 ≤ q.den)
    (h : |ξ - (q : ℝ)| ≤ 1 / (2 * (q.den : ℝ) ^ 2)) :
    ∃ n : ℕ, q = ξ.convergent n := by
  refine q.num_div_den ▸ Real.exists_rat_eq_convergent' ⟨?_, ?_, ?_⟩
  · exact Int.isCoprime_iff_nat_coprime.mpr (Int.natAbs_natCast q.den ▸ q.reduced)
  · intro hd
    have hn : q.den = 1 := by exact_mod_cast hd
    omega
  · have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hd2 : (2 : ℝ) ≤ q.den := by exact_mod_cast hq
    have he : |ξ - (q.num : ℝ) / (q.den : ℝ)| = |ξ - (q : ℝ)| := by
      have hn := congrArg (fun r : ℚ => (r : ℝ)) q.num_div_den
      push_cast at hn
      rw [hn]
    push_cast
    rw [he]
    refine h.trans_lt ?_
    rw [← one_div]
    apply one_div_lt_one_div_of_lt (by nlinarith)
    nlinarith

end Qatlib.Concepts.AmpTransform.LegendreWindow
