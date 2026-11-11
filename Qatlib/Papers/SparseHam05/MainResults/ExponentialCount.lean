/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseHam05.MainResults.SuzukiError

/-!
# Exponential counts for recursive Suzuki simulation

This module chooses the repetition count `theorem1R` and proves that it meets the Suzuki error
conditions with target accuracy `ε`. The resulting word-length and error estimates give the
finite-matrix form of Theorem 1 in [BerryEtAl2007Sparse], under the stated Hermiticity, norm,
and scaled-time hypotheses.

## Main statements

* `theorem1R_bounds`: Under the stated positive-parameter and scaled-time hypotheses,
  `theorem1R` is positive, satisfies `PaperLemma1Conditions`, makes `paperSuzukiError` at most
  `ε`, and obeys the explicit exponential-count bound.
* `source_theorem1_exponential_count`: For the stated Hermitian list and norm bounds, the chosen
  positive repetition count yields simulation error at most `ε` and word length at most
  `2*m*5^(2*k)*(m*τ)^(1+1/(2*k))/ε^(1/(2*k))`, where `m = hs.length` and `τ = ‖hs.sum‖*t`.

## References

* [Berry et al., 2007][BerryEtAl2007Sparse]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.SparseHam05.MainResults

/-- The natural-number ceiling of `4 * 5^(k-1/2) * (m*τ)^(1+1/(2*k)) / ε^(1/(2*k))`, used as the
Suzuki repetition count. See [BerryEtAl2007Sparse]. -/
def theorem1R (m k : ℕ) (τ ε : ℝ) : ℕ :=
  Nat.ceil (4 * (5 : ℝ) ^ ((k : ℝ) - 1 / 2) *
    ((m : ℝ) * τ) ^ (1 + 1 / (2 * (k : ℝ))) / ε ^ (1 / (2 * (k : ℝ))))

/-- For positive integer `k`, multiplying `1 + 1/(2*k)` by `2*k` gives `2*k + 1` over the reals. -/
lemma expo_id (k : ℕ) (hk : 1 ≤ k) :
    (1 + 1 / (2 * (k : ℝ))) * ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) + 1 := by
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
  rw [hcast]; field_simp

/-- For `k ≥ 1`, the natural-number exponent identity `2*k² - k = (k-1)*(2*k+1) + 1` holds. -/
lemma nat_expo (k : ℕ) (hk : 1 ≤ k) :
    2*k^2 - k = (k-1)*(2*k+1) + 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hle : (j+1) ≤ 2*(j+1)^2 := by nlinarith
  rw [Nat.sub_eq_iff_eq_add hle]
  simp only [Nat.succ_eq_add_one, Nat.succ_sub_one]
  ring

/-- For positive parameters and `k ≥ 1`, the `2*k` power of the real expression defining
`theorem1R` equals `2^(2*k-1) * 5 * (2 * 5^(k-1) * (m*τ))^(2*k+1) / ε`. -/
lemma suzuki_pow (m k : ℕ) (τ ε : ℝ) (hm : 0 < m) (hk : 1 ≤ k) (hτ0 : 0 < τ)
    (hε0 : 0 < ε) :
    (4 * (5 : ℝ) ^ ((k : ℝ) - 1 / 2) * ((m : ℝ) * τ) ^ (1 + 1 / (2 * (k : ℝ)))
        / ε ^ (1 / (2 * (k : ℝ)))) ^ (2 * k)
      = (2 : ℝ) ^ (2 * k - 1) * 5 *
          (2 * (5 : ℝ) ^ (k - 1) * ((m : ℝ) * τ)) ^ (2 * k + 1) / ε := by
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  set X : ℝ := (m:ℝ)*τ with hX
  have hXpos : 0 < X := by rw [hX]; positivity
  have h5pos : (0:ℝ) < (5:ℝ) := by norm_num
  have hdiv : (4 * (5 : ℝ) ^ ((k : ℝ) - 1 / 2) * X ^ (1 + 1 / (2 * (k : ℝ)))
        / ε ^ (1 / (2 * (k : ℝ))))
      = (4 * (5 : ℝ) ^ ((k : ℝ) - 1 / 2)) * X ^ (1 + 1 / (2 * (k : ℝ)))
          * (ε ^ (1 / (2 * (k : ℝ))))⁻¹ := by field_simp
  rw [hdiv, mul_pow, mul_pow]
  have hεinv : ((ε ^ (1 / (2 * (k : ℝ))))⁻¹) ^ (2 * k) = ε⁻¹ := by
    rw [inv_pow]
    have he : (1 / (2 * (k : ℝ))) = (((2 * k : ℕ) : ℝ))⁻¹ := by
      rw [Nat.cast_mul, Nat.cast_ofNat]; rw [one_div]
    rw [he, Real.rpow_inv_natCast_pow (le_of_lt hε0) (by omega : 2 * k ≠ 0)]
  rw [hεinv]
  have hXpow : (X ^ (1 + 1 / (2 * (k : ℝ)))) ^ (2 * k) = X ^ (2 * k + 1) := by
    rw [← Real.rpow_natCast (X ^ (1 + 1 / (2 * (k : ℝ)))) (2*k)]
    rw [← Real.rpow_mul (le_of_lt hXpos)]
    rw [expo_id k hk]
    have hcast2 : 2*(k:ℝ)+1 = ((2*k+1:ℕ):ℝ) := by push_cast; ring
    rw [hcast2, Real.rpow_natCast]
  rw [hXpow, mul_pow]
  have h4 : (4:ℝ) ^ (2*k) = (2:ℝ)^(4*k) := by
    rw [show (4:ℝ) = 2^2 by norm_num, ← pow_mul]; congr 1; ring
  rw [h4]
  have h5 : ((5:ℝ) ^ ((k:ℝ) - 1 / 2)) ^ (2 * k) = (5:ℝ) ^ (2*k^2 - k) := by
    rw [← Real.rpow_natCast ((5:ℝ) ^ ((k:ℝ) - 1 / 2)) (2*k)]
    rw [← Real.rpow_mul (le_of_lt h5pos)]
    have e1 : ((k:ℝ) - 1 / 2) * (((2 * k : ℕ) : ℝ)) = ((2*k^2 - k : ℕ) : ℝ) := by
      have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
      rw [hcast]
      have hle : k ≤ 2*k^2 := by nlinarith
      rw [Nat.cast_sub hle]; push_cast; ring
    rw [e1, Real.rpow_natCast]
  rw [h5]
  have h2 : (2 * (5 : ℝ) ^ (k - 1) * X) ^ (2 * k + 1)
      = (2:ℝ)^(2*k+1) * ((5:ℝ)^(k-1))^(2*k+1) * X^(2*k+1) := by rw [mul_pow, mul_pow]
  rw [h2]
  have h5b : ((5:ℝ)^(k-1))^(2*k+1) = (5:ℝ)^((k-1)*(2*k+1)) := by rw [← pow_mul]
  rw [h5b]
  have h2b : (2:ℝ)^(4*k) = 2^(2*k-1) * 2^(2*k+1) := by rw [← pow_add]; congr 1; omega
  have h5c : (5:ℝ)^(2*k^2 - k) = 5 * 5^((k-1)*(2*k+1)) := by
    rw [nat_expo k hk, pow_succ]; ring
  rw [h2b, h5c, div_eq_mul_inv]
  ring

/-- For `k ≥ 1`, the product of `5^k` with the reciprocal of `2 * 5^(k-1)` is `5/2`. -/
lemma five_pow_mul (k : ℕ) (hk : 1 ≤ k) :
    (5:ℝ)^k * (1/(2*(5:ℝ)^(k-1))) = 5/2 := by
  have hk1 : (5:ℝ)^k = (5:ℝ)^(k-1) * 5 := by
    conv_lhs => rw [show k = (k-1)+1 from (Nat.sub_add_cancel hk).symm]
    rw [pow_succ]
  rw [hk1]
  have hp : (5:ℝ)^(k-1) ≠ 0 := by positivity
  field_simp

/-- For positive `x`, the product `x^a * x^b` equals `x^c` whenever `a + b = c`. -/
lemma rpow_mul_eq (x : ℝ) (hx : 0 < x) (a b c : ℝ) (h : a + b = c) :
    x ^ a * x ^ b = x ^ c := by
  rw [← h]
  exact (Real.rpow_add hx a b).symm

/-- For positive `x`, the product of a real power `x^a` and a natural power `x^n` equals `x^c`
when `a + n = c`. -/
lemma rpow_mul_natCast (x : ℝ) (hx : 0 < x) (a c : ℝ) (n : ℕ) (h : a + (n:ℝ) = c) :
    x ^ a * x ^ n = x ^ c := by
  rw [← Real.rpow_natCast x n]
  exact rpow_mul_eq x hx a (n:ℝ) c h

/-- For `k ≥ 1`, the real power `2^(2*k)` equals `2 * 2^(2*k-1)`. -/
lemma two_pow_two_k (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ^ (2 * k) = 2 * (2 : ℝ) ^ (2 * k - 1) := by
  have hp := pow_succ (2:ℝ) (2 * k - 1)
  rw [show 2 * k - 1 + 1 = 2 * k by omega] at hp
  rw [hp]; ring

/-- The real number `5^(3/2)` is at least six. -/
lemma six_le_five_three_halves : (6 : ℝ) ≤ (5 : ℝ) ^ ((3:ℝ) / 2) := by
  have h5 : (0:ℝ) < 5 := by norm_num
  have h3 : (5:ℝ)^((3:ℝ)/2) = 5 * Real.sqrt 5 := by
    have h1 : (5:ℝ)^((3:ℝ)/2) = (5:ℝ)^((1:ℝ) + 1/2) := by congr 1; norm_num
    rw [h1, Real.rpow_add h5, Real.rpow_one]
    congr 1
    rw [← Real.sqrt_eq_rpow]
  have h4 : (2:ℝ) ≤ Real.sqrt 5 := by
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by norm_num)
  rw [h3]
  nlinarith

/-- For `k ≥ 1`, multiplying `5^(3/2)`, `5^(k-1/2)`, and `5^(k-1)` gives `5^(2*k)`. -/
lemma five_three_halves_mul (k : ℕ) (hk : 1 ≤ k) :
    (5 : ℝ) ^ ((3:ℝ) / 2) * (5 : ℝ) ^ ((k : ℝ) - 1 / 2) * (5 : ℝ) ^ (k - 1)
      = (5 : ℝ) ^ (2 * k) := by
  have h5 : (0:ℝ) < 5 := by norm_num
  have h1 : (5:ℝ)^((3:ℝ)/2) * (5:ℝ)^((k:ℝ)-1/2) = (5:ℝ)^((k:ℝ)+1) :=
    rpow_mul_eq 5 h5 ((3:ℝ)/2) ((k:ℝ)-1/2) ((k:ℝ)+1) (by ring)
  have h2 : (5:ℝ)^((k:ℝ)+1) * (5:ℝ)^(k-1) = (5:ℝ)^(((k:ℝ)+1) + ((k-1:ℕ):ℝ)) :=
    rpow_mul_natCast 5 h5 ((k:ℝ)+1) (((k:ℝ)+1) + ((k-1:ℕ):ℝ)) (k-1) (by ring)
  have h3 : ((k:ℝ)+1) + ((k-1:ℕ):ℝ) = ((2*k:ℕ):ℝ) := by
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk]; push_cast; ring
    rw [hcast]; push_cast; ring
  calc (5 : ℝ) ^ ((3:ℝ)/2) * (5 : ℝ) ^ ((k : ℝ) - 1 / 2) * (5 : ℝ) ^ (k - 1)
      = (5:ℝ)^((k:ℝ)+1) * (5:ℝ)^(k-1) := by rw [h1]
    _ = (5:ℝ)^(((k:ℝ)+1) + ((k-1:ℕ):ℝ)) := h2
    _ = (5:ℝ)^((2*k:ℕ):ℝ) := by rw [h3]
    _ = (5:ℝ)^(2*k) := Real.rpow_natCast 5 (2*k)

/-- Under the stated positive-parameter and scaled-time hypotheses, `theorem1R` is positive,
satisfies `PaperLemma1Conditions`, makes `paperSuzukiError` at most `ε`, and obeys the
explicit exponential-count bound. See [BerryEtAl2007Sparse]. -/
lemma theorem1R_bounds (m k : ℕ) (τ ε : ℝ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hτ0 : 0 < τ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hτ : 1 ≤ 2 * (m : ℝ) * (5 : ℝ) ^ (k - 1) * τ) :
    let r := theorem1R m k τ ε
    0 < r ∧ PaperLemma1Conditions m k τ r ∧
      paperSuzukiError m k τ r ≤ ε ∧
      (r : ℝ) * (2 * (m : ℝ) * (5 : ℝ) ^ (k - 1)) ≤
        2 * (m : ℝ) * (5 : ℝ) ^ (2 * k) *
          ((m : ℝ) * τ) ^ (1 + 1 / (2 * (k : ℝ))) / ε ^ (1 / (2 * (k : ℝ))) := by
  intro r
  set P : ℝ := 4 * (5 : ℝ) ^ ((k : ℝ) - 1 / 2) *
      ((m : ℝ) * τ) ^ (1 + 1 / (2 * (k : ℝ))) / ε ^ (1 / (2 * (k : ℝ))) with hP
  set B : ℝ := (2 * (5 : ℝ) ^ (k - 1) * (m : ℝ) * τ) ^ (2 * k + 1) with hB
  set C : ℝ := (2 : ℝ) ^ (2 * k - 1) * 5 / ε with hC
  have hr_eq : r = Nat.ceil P := rfl
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hmτ : (0 : ℝ) < (m : ℝ) * τ := mul_pos hmR hτ0
  have hbase : (0 : ℝ) < 2 * (5 : ℝ) ^ (k - 1) * (m : ℝ) * τ := by positivity
  have hBpos : (0 : ℝ) < B := by rw [hB]; exact pow_pos hbase _
  have h2k1pos : (0 : ℝ) < (2 : ℝ) ^ (2 * k - 1) := by positivity
  have hCpos : (0 : ℝ) < C := by rw [hC]; positivity
  have hPpos : 0 < P := by
    rw [hP]
    have h1 : (0 : ℝ) < (5 : ℝ) ^ ((k : ℝ) - 1 / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0 : ℝ) < ((m : ℝ) * τ) ^ (1 + 1 / (2 * (k : ℝ))) :=
      Real.rpow_pos_of_pos hmτ _
    have h3 : (0 : ℝ) < ε ^ (1 / (2 * (k : ℝ))) := Real.rpow_pos_of_pos hε0 _
    positivity
  have hr_pos : 0 < r := by rw [hr_eq]; exact Nat.ceil_pos.mpr hPpos
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr_pos
  have hr_ge : P ≤ (r : ℝ) := by rw [hr_eq]; exact Nat.le_ceil P
  have hr_lt : (r : ℝ) < P + 1 := by
    rw [hr_eq]; exact Nat.ceil_lt_add_one (le_of_lt hPpos)
  have hr2k : (0 : ℝ) < (r : ℝ) ^ (2 * k) := pow_pos hrR _

  have hPpow : P ^ (2 * k) = C * B := by
    rw [hP, hC, hB]
    have hs := suzuki_pow m k τ ε (by omega) hk hτ0 hε0
    rw [hs]
    have hbb : 2 * (5 : ℝ) ^ (k - 1) * ((m : ℝ) * τ)
        = 2 * (5 : ℝ) ^ (k - 1) * (m : ℝ) * τ := by ring
    rw [hbb]
    ring
  have hrpow_ge : P ^ (2 * k) ≤ (r : ℝ) ^ (2 * k) :=
    pow_le_pow_left₀ (le_of_lt hPpos) hr_ge (2 * k)

  have haP : 4 * (m : ℝ) * (5 : ℝ) ^ (k - 1) * τ / P ≤ 1 := by
    have hpow_le : (4 * (m : ℝ) * (5 : ℝ) ^ (k - 1) * τ / P) ^ (2 * k) ≤ 1 := by
      have haeq : 4 * (m : ℝ) * (5 : ℝ) ^ (k - 1) * τ
          = 2 * (2 * (5 : ℝ) ^ (k - 1) * (m : ℝ) * τ) := by ring
      rw [div_pow, hPpow, div_le_one (mul_pos hCpos hBpos), haeq, hB, hC, mul_pow,
        two_pow_two_k k hk, pow_succ]
      have h2eps : 2 * ε ≤ 5 * (2 * (5 : ℝ) ^ (k - 1) * (m : ℝ) * τ) := by
        nlinarith [hτ, hε1]
      have hle : (2 : ℝ) ≤ (5 / ε) * (2 * (5 : ℝ) ^ (k - 1) * (m : ℝ) * τ) := by
        rw [show (5 : ℝ) / ε * (2 * (5 : ℝ) ^ (k - 1) * (m : ℝ) * τ)
            = (5 * (2 * (5 : ℝ) ^ (k - 1) * (m : ℝ) * τ)) / ε by ring,
          le_div_iff₀ hε0]
        exact h2eps
      have hb0pow : (0 : ℝ) < (2 * (5 : ℝ) ^ (k - 1) * (m : ℝ) * τ) ^ (2 * k) :=
        pow_pos hbase _
      have hkey := mul_le_mul_of_nonneg_right hle (le_of_lt (mul_pos h2k1pos hb0pow))
      have he : 5 / ε * (2 * (5 : ℝ) ^ (k - 1) * (m : ℝ) * τ) *
            (2 ^ (2 * k - 1) * (2 * (5 : ℝ) ^ (k - 1) * (m : ℝ) * τ) ^ (2 * k))
          = 2 ^ (2 * k - 1) * 5 / ε *
            ((2 * (5 : ℝ) ^ (k - 1) * (m : ℝ) * τ) ^ (2 * k) *
              (2 * (5 : ℝ) ^ (k - 1) * (m : ℝ) * τ)) := by ring
      linarith [hkey, he]
    by_contra hcon
    push Not at hcon
    have hgt : (1 : ℝ) < (4 * (m : ℝ) * (5 : ℝ) ^ (k - 1) * τ / P) ^ (2 * k) :=
      one_lt_pow₀ hcon (by omega)
    linarith
  have haP' : 4 * (m : ℝ) * (5 : ℝ) ^ (k - 1) * τ / (r : ℝ) ≤ 1 := by
    rw [div_le_one hrR]
    exact ((div_le_one hPpos).mp haP).trans hr_ge

  have hcond2 : (16 / 3) * B / (r : ℝ) ^ (2 * k) ≤ 1 := by
    have hbC : (16 / 3 : ℝ) ≤ C := by
      rw [hC]
      have h2k1 : (2 : ℝ) ≤ (2 : ℝ) ^ (2 * k - 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ (2 : ℝ) ^ (2 * k - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hεinv : (1:ℝ) ≤ ε⁻¹ := by
        rw [← one_div]
        exact (one_le_div hε0).mpr hε1
      have hprod : (2:ℝ) * 1 ≤ (2:ℝ)^(2*k-1) * ε⁻¹ :=
        mul_le_mul h2k1 hεinv (by norm_num) (by positivity)
      have heq : (2:ℝ)^(2*k-1) * 5 / ε = 5 * ((2:ℝ)^(2*k-1) * ε⁻¹) := by
        field_simp
      rw [heq]
      nlinarith [hprod]
    have hp : C * B ≤ (r : ℝ) ^ (2 * k) := hPpow ▸ hrpow_ge
    rw [div_le_one hr2k]
    nlinarith [hbC, hBpos, hp]

  have herr : paperSuzukiError m k τ r ≤ ε := by
    have hεr : (2 : ℝ) ^ (2 * k - 1) * 5 * B ≤ ε * (r : ℝ) ^ (2 * k) := by
      have h1 : ε * P ^ (2 * k) ≤ ε * (r : ℝ) ^ (2 * k) :=
        mul_le_mul_of_nonneg_left hrpow_ge (le_of_lt hε0)
      rw [hPpow] at h1
      have heC : ε * C = (2 : ℝ) ^ (2 * k - 1) * 5 := by
        rw [hC]; field_simp
      calc (2 : ℝ) ^ (2 * k - 1) * 5 * B = (ε * C) * B := by rw [heC]
        _ = ε * (C * B) := by ring
        _ ≤ ε * (r : ℝ) ^ (2 * k) := h1
    have h2pow : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * k - 1) := by
      calc (1 : ℝ) = 2 ^ 0 := by norm_num
        _ ≤ (2 : ℝ) ^ (2 * k - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [paperSuzukiError, ← hB, div_le_iff₀ hr2k]
    nlinarith [hεr, hBpos, h2pow]

  have hcount : (r : ℝ) * (2 * (m : ℝ) * (5 : ℝ) ^ (k - 1)) ≤
      2 * (m : ℝ) * (5 : ℝ) ^ (2 * k) *
        ((m : ℝ) * τ) ^ (1 + 1 / (2 * (k : ℝ))) / ε ^ (1 / (2 * (k : ℝ))) := by
    have ha_le_P : 4 * (m : ℝ) * (5 : ℝ) ^ (k - 1) * τ ≤ P :=
      (div_le_one hPpos).mp haP
    have ha2 : (2 : ℝ) ≤ P := by
      have h2le : (2 : ℝ) ≤ 4 * (m : ℝ) * (5 : ℝ) ^ (k - 1) * τ := by nlinarith [hτ]
      linarith
    have hr_le : (r : ℝ) ≤ (5 : ℝ) ^ ((3:ℝ) / 2) / 4 * P := by
      have h2 : P + 1 ≤ (3 / 2) * P := by nlinarith [ha2]
      have h3 : (3 / 2 : ℝ) ≤ (5 : ℝ) ^ ((3:ℝ) / 2) / 4 := by
        have := six_le_five_three_halves
        linarith
      have h4 : (3 / 2) * P ≤ (5 : ℝ) ^ ((3:ℝ) / 2) / 4 * P :=
        mul_le_mul_of_nonneg_right h3 (le_of_lt hPpos)
      linarith [hr_lt]
    have hmul : (r : ℝ) * (2 * (m : ℝ) * (5 : ℝ) ^ (k - 1))
        ≤ ((5 : ℝ) ^ ((3:ℝ) / 2) / 4 * P) * (2 * (m : ℝ) * (5 : ℝ) ^ (k - 1)) :=
      mul_le_mul_of_nonneg_right hr_le (by positivity)
    refine hmul.trans (le_of_eq ?_)
    rw [hP]
    set X : ℝ := ((m : ℝ) * τ) ^ (1 + 1 / (2 * (k : ℝ))) with hX
    set E : ℝ := ε ^ (1 / (2 * (k : ℝ))) with hE
    have step1 : (5 : ℝ) ^ ((3:ℝ) / 2) / 4 * (4 * (5 : ℝ) ^ ((k : ℝ) - 1 / 2) * X / E) *
          (2 * (m : ℝ) * (5 : ℝ) ^ (k - 1))
        = ((5 : ℝ) ^ ((3:ℝ) / 2) * (5 : ℝ) ^ ((k : ℝ) - 1 / 2) * (5 : ℝ) ^ (k - 1)) *
            (2 * (m : ℝ) * X / E) := by
      field_simp
    rw [step1, five_three_halves_mul k hk]
    ring

  exact ⟨hr_pos, ⟨haP', hcond2⟩, herr, hcount⟩

/-- For the stated Hermitian list and norm bounds, the chosen positive repetition count yields
simulation error at most `ε` and word length at most
`2*m*5^(2*k)*(m*τ)^(1+1/(2*k))/ε^(1/(2*k))`, where `m = hs.length` and `τ = ‖hs.sum‖*t`. See
[BerryEtAl2007Sparse]. -/
theorem source_theorem1_exponential_count {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (t ε : ℝ)
    (hh : ∀ X ∈ hs, Xᴴ = X) (hk : 1 ≤ k) (hm : 0 < hs.length)
    (hbound : ∀ X ∈ hs, ‖X‖ ≤ ‖hs.sum‖)
    (ht : 0 ≤ t) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hτ : 1 ≤ 2 * (hs.length : ℝ) * (5 : ℝ) ^ (k - 1) * ‖hs.sum‖ * t) :
    let r := theorem1R hs.length k (‖hs.sum‖ * t) ε
    0 < r ∧
      ((paperSuzukiWord hs k t r).length : ℝ) ≤
        2 * (hs.length : ℝ) * (5 : ℝ) ^ (2 * k) *
          ((hs.length : ℝ) * (‖hs.sum‖ * t)) ^ (1 + 1 / (2 * (k : ℝ))) /
            ε ^ (1 / (2 * (k : ℝ))) ∧
      ‖(paperSuzukiWord hs k t r).prod -
          NormedSpace.exp (t • (paperAntiHermitian hs).sum)‖ ≤ ε := by
  intro r
  have hm1 : 1 ≤ hs.length := hm
  have hτ0 : 0 < ‖hs.sum‖ * t := by
    by_cases hle : ‖hs.sum‖ * t ≤ 0
    · exfalso
      have hc : (0 : ℝ) < 2 * (hs.length : ℝ) * (5 : ℝ) ^ (k - 1) := by positivity
      nlinarith [hτ, hle, hc]
    · push_neg at hle
      exact hle
  have hτ' : 1 ≤ 2 * (hs.length : ℝ) * (5 : ℝ) ^ (k - 1) * (‖hs.sum‖ * t) := by
    linarith only [hτ]
  obtain ⟨hr0, hcond, herr, hcount⟩ :=
    theorem1R_bounds hs.length k (‖hs.sum‖ * t) ε hm1 hk hτ0 hε0 hε1 hτ'
  refine ⟨hr0, ?_, ?_⟩
  · rw [paperSuzukiWord_length]
    push_cast
    exact hcount
  · exact (source_lemma1_recursive_suzuki_error hs k r t hh hk hr0 ht hm hbound hcond).trans herr

end Qatlib.Papers.SparseHam05.MainResults
