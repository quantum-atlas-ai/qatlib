/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtSignMaterials
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtCoreDefs

/-!
# Gap-dependent sign approximation by truncated series

This module constructs the bounded odd polynomial `gapSignPolynomial` from a truncated
inverse-square-root series. It proves a geometric error bound outside a spectral gap and obtains
an explicit degree bound proportional to δ⁻² log(2/(εδ)). Background and related constructions
are discussed in [GilyenSuLowWiebe2019].

## Main statements

* `gapSign_approximation`: packages the error bound as a sign approximation.
* `frontier1`: chooses a polynomial with prescribed gap error and an explicit degree budget.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.SignalPrimitive.PhaseFrontend

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit

open Polynomial
open scoped Classical BigOperators
open Qatlib.Concepts.QsvtCore.ApproxToolkit
set_option warningAsError false

/-- The odd truncated-series polynomial (X/2) times the sum of `cReal i` (1 − X²/4)ⁱ for i from
zero through `K`. -/
noncomputable def gapSignPolynomial (K : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / 2) * Polynomial.X *
    ∑ i ∈ Finset.range (K + 1),
      Polynomial.C (cReal i) *
        (Polynomial.C (1 : ℝ) - Polynomial.C (1 / 4) * Polynomial.X ^ 2) ^ i

/-- The gap sign polynomial evaluates to `(x / 2) * wsum K (1 - x ^ 2 / 4)`. -/
lemma gapSignPolynomial_eval (K : ℕ) (x : ℝ) :
    (gapSignPolynomial K).eval x = (x / 2) * wsum K (1 - x ^ 2 / 4) := by
  have hsum : (∑ i ∈ Finset.range (K + 1),
      Polynomial.C (cReal i) *
        (Polynomial.C (1 : ℝ) - Polynomial.C (1 / 4) * Polynomial.X ^ 2) ^ i).eval x
      = wsum K (1 - x ^ 2 / 4) := by
    simp only [eval_finsetSum, eval_mul, eval_C, eval_sub, eval_pow, eval_X]
    rw [wsum]
    apply Finset.sum_congr rfl
    intro i hi
    have hb : (1:ℝ) - (1 / 4) * x ^ 2 = 1 - x ^ 2 / 4 := by ring
    rw [hb]
  simp only [gapSignPolynomial, eval_mul, eval_C, eval_X]
  rw [hsum]
  ring

/-- The gap sign polynomial has an odd response. -/
lemma gapSignPolynomial_odd (K : ℕ) (x : ℝ) :
    (gapSignPolynomial K).eval (-x) = -(gapSignPolynomial K).eval x := by
  rw [gapSignPolynomial_eval, gapSignPolynomial_eval]
  have hb : (1:ℝ) - (-x) ^ 2 / 4 = 1 - x ^ 2 / 4 := by ring
  rw [hb]
  ring

/-- A real input of absolute value at most two has square at most four. -/
lemma sq_le_four_of_abs_le_two {x : ℝ} (hx : |x| ≤ 2) : x ^ 2 ≤ 4 := by
  have h1 := mul_self_le_mul_self (abs_nonneg x) hx
  calc x ^ 2 = |x| ^ 2 := by rw [sq_abs]
    _ ≤ (2:ℝ) ^ 2 := by nlinarith [h1]
    _ = 4 := by norm_num

/-- The gap sign polynomial has absolute value at most one on [0, 2]. -/
lemma gapSignPolynomial_abs_le_one_nonneg (K : ℕ) {x : ℝ} (hx : |x| ≤ 2) (h0 : 0 ≤ x) :
    |(gapSignPolynomial K).eval x| ≤ 1 := by
  rw [gapSignPolynomial_eval]
  rcases eq_or_ne x 0 with rfl | hne
  · simp
  · have hpos : 0 < x := lt_of_le_of_ne h0 (Ne.symm hne)
    have hx2 : x ^ 2 ≤ 4 := sq_le_four_of_abs_le_two hx
    have hs0 : (0:ℝ) ≤ 1 - x ^ 2 / 4 := by nlinarith [hx2]
    have hs1 : 1 - x ^ 2 / 4 < 1 := by nlinarith [sq_nonneg x]
    have hw := wsum_le K hs0 hs1
    have hwn := wsum_nonneg K hs0
    rw [abs_of_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ x / 2) hwn)]
    have hsqrt : √(1 - (1 - x ^ 2 / 4)) = x / 2 := by
      rw [show (1:ℝ) - (1 - x ^ 2 / 4) = (x / 2) ^ 2 from by ring, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ x / 2)]
    rw [hsqrt] at hw
    calc (x / 2) * wsum K (1 - x ^ 2 / 4) ≤ (x / 2) * (1 / (x / 2)) :=
          mul_le_mul_of_nonneg_left hw (by linarith : (0:ℝ) ≤ x / 2)
      _ = 1 := by
          have hne : x / 2 ≠ 0 := by linarith
          field_simp [hne]

/-- The gap sign polynomial has absolute value at most one on [−2, 2]. -/
lemma gapSignPolynomial_abs_le_one (K : ℕ) {x : ℝ} (hx : |x| ≤ 2) :
    |(gapSignPolynomial K).eval x| ≤ 1 := by
  rcases le_or_gt 0 x with h0 | h0
  · exact gapSignPolynomial_abs_le_one_nonneg K hx h0
  · have h := gapSignPolynomial_abs_le_one_nonneg K (by rw [abs_neg]; exact hx) (by linarith)
    rw [gapSignPolynomial_odd] at h
    rw [abs_neg] at h
    exact h

/-- On the positive part of [−2, 2] outside a positive gap, the sign error is at most (2/δ)(1 −
δ²/4)^(K + 1) `cReal (K + 1)`. -/
lemma gapSignPolynomial_error_le_pos (K : ℕ) {δ x : ℝ} (hδ : 0 < δ) (hgap : δ ≤ x)
    (hx : |x| ≤ 2) (hpos : 0 < x) :
    |(gapSignPolynomial K).eval x - Real.sign x| ≤
      (2 / δ) * (1 - δ ^ 2 / 4) ^ (K + 1) * cReal (K + 1) := by
  have hposx : (0:ℝ) < 2 / x := div_pos (by norm_num) hpos
  have hposδ : (0:ℝ) < 2 / δ := div_pos (by norm_num) hδ
  have hx2 : x ^ 2 ≤ 4 := sq_le_four_of_abs_le_two hx
  have hs0 : (0:ℝ) ≤ 1 - x ^ 2 / 4 := by nlinarith [hx2]
  have hs1 : 1 - x ^ 2 / 4 < 1 := by nlinarith [sq_nonneg x]
  have hge := wsum_tail K hs0 hs1
  have hsqrt : √(1 - (1 - x ^ 2 / 4)) = x / 2 := by
    rw [show (1:ℝ) - (1 - x ^ 2 / 4) = (x / 2) ^ 2 from by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ x / 2)]
  rw [hsqrt] at hge
  have hone : (gapSignPolynomial K).eval x ≤ 1 := by
    have h := gapSignPolynomial_abs_le_one_nonneg K hx (le_of_lt hpos)
    exact le_trans (le_abs_self ((gapSignPolynomial K).eval x)) h
  have htail : 1 / (x / 2) - wsum K (1 - x ^ 2 / 4) ≤
      (1 - x ^ 2 / 4) ^ (K + 1) * cReal (K + 1) / (x ^ 2 / 4) := by
    have hden : (1:ℝ) - (1 - x ^ 2 / 4) = x ^ 2 / 4 := by ring
    rw [hden] at hge
    linarith
  have hx2' : x ≤ 2 := by
    rw [← abs_of_pos hpos]
    exact hx
  have hδ2 : δ ≤ 2 := le_trans hgap hx2'
  have hδsq : δ ^ 2 ≤ 4 := by
    have h1 := mul_self_le_mul_self hδ.le hδ2
    nlinarith [h1]
  have hsδ : 1 - x ^ 2 / 4 ≤ 1 - δ ^ 2 / 4 := by
    have h1 : δ ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hδ.le hgap 2
    nlinarith [h1]
  have hsδ0 : (0:ℝ) ≤ 1 - δ ^ 2 / 4 := by nlinarith [hδsq]
  have hone2 : (gapSignPolynomial K).eval x = (x / 2) * wsum K (1 - x ^ 2 / 4) :=
    gapSignPolynomial_eval K x
  rw [hone2, Real.sign_of_pos hpos, abs_of_nonpos (by linarith [hone])]
  have hmain : 1 - (x / 2) * wsum K (1 - x ^ 2 / 4) ≤
      (2 / x) * (1 - x ^ 2 / 4) ^ (K + 1) * cReal (K + 1) := by
    have hone3 : (x / 2) * (1 / (x / 2)) = 1 := by
      have hne : x / 2 ≠ 0 := by linarith
      field_simp [hne]
    have hne : x ≠ 0 := by linarith
    have hne4 : x ^ 2 / 4 ≠ 0 := div_ne_zero (pow_ne_zero 2 hne) (by norm_num : (4:ℝ) ≠ 0)
    calc 1 - (x / 2) * wsum K (1 - x ^ 2 / 4)
        = (x / 2) * (1 / (x / 2) - wsum K (1 - x ^ 2 / 4)) := by
          field_simp [hne]
      _ ≤ (x / 2) * ((1 - x ^ 2 / 4) ^ (K + 1) * cReal (K + 1) / (x ^ 2 / 4)) :=
            mul_le_mul_of_nonneg_left htail (by linarith : (0:ℝ) ≤ x / 2)
      _ = (2 / x) * (1 - x ^ 2 / 4) ^ (K + 1) * cReal (K + 1) := by
          field_simp [hne, hne4]
          ring
  have hpow : (1 - x ^ 2 / 4) ^ (K + 1) ≤ (1 - δ ^ 2 / 4) ^ (K + 1) :=
    pow_le_pow_left₀ (by linarith [hs0]) (by linarith [hsδ]) (K + 1)
  have hcoef : (2 / x) ≤ 2 / δ := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < x)]
    have h := mul_le_mul hgap (le_refl (2 / δ)) (le_of_lt hposδ) (le_of_lt hpos)
    calc 2 = δ * (2 / δ) := by field_simp [ne_of_gt hδ]
      _ ≤ x * (2 / δ) := h
      _ = (2 / δ) * x := by ring
  have hstep : (2 / x) * (1 - x ^ 2 / 4) ^ (K + 1) * cReal (K + 1) ≤
      (2 / δ) * (1 - δ ^ 2 / 4) ^ (K + 1) * cReal (K + 1) := by
    calc (2 / x) * (1 - x ^ 2 / 4) ^ (K + 1) * cReal (K + 1)
        ≤ (2 / δ) * (1 - x ^ 2 / 4) ^ (K + 1) * cReal (K + 1) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hcoef (le_refl ((1 - x ^ 2 / 4) ^ (K + 1)))
              (pow_nonneg hs0 (K + 1)) (le_of_lt hposδ))
            (le_of_lt (cReal_pos (K + 1)))
      _ ≤ (2 / δ) * (1 - δ ^ 2 / 4) ^ (K + 1) * cReal (K + 1) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul (le_refl (2 / δ)) hpow (pow_nonneg hs0 (K + 1)) (le_of_lt hposδ))
            (le_of_lt (cReal_pos (K + 1)))
  linarith [hmain, hstep]

/-- On [−2, 2] outside a positive gap, the sign error is at most (2/δ)(1 − δ²/4)^(K + 1) `cReal
(K + 1)`. -/
lemma gapSignPolynomial_error_le (K : ℕ) {δ x : ℝ} (hδ : 0 < δ) (hgap : δ ≤ |x|)
    (hx : |x| ≤ 2) :
    |(gapSignPolynomial K).eval x - Real.sign x| ≤
      (2 / δ) * (1 - δ ^ 2 / 4) ^ (K + 1) * cReal (K + 1) := by
  have hne : x ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hgap
    linarith
  rcases le_or_gt 0 x with h0 | h0
  · have hpos : 0 < x := lt_of_le_of_ne h0 (Ne.symm hne)
    have hgap' : δ ≤ x := by rwa [abs_of_pos hpos] at hgap
    exact gapSignPolynomial_error_le_pos K hδ hgap' hx hpos
  · have hneg : x < 0 := h0
    have hxp : 0 < -x := by linarith
    have hgap' : δ ≤ -x := by
      rw [← abs_of_neg hneg]
      exact hgap
    have h := gapSignPolynomial_error_le_pos K hδ hgap' (by rw [abs_neg]; exact hx) hxp
    rw [gapSignPolynomial_odd, Real.sign_neg] at h
    have hneg' : -((gapSignPolynomial K).eval x) - -(Real.sign x) =
        -((gapSignPolynomial K).eval x - Real.sign x) := by ring
    rw [hneg', abs_neg] at h
    exact h

/-- The gap sign polynomial has natural degree at most 2K + 1. -/
lemma gapSignPolynomial_natDegree_le (K : ℕ) :
    (gapSignPolynomial K).natDegree ≤ 2 * K + 1 := by
  have hfactor :
      (Polynomial.C (1 : ℝ) - Polynomial.C (1 / 4) * Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by
    have hneg : (-(Polynomial.C (1 / 4) * Polynomial.X ^ 2 : Polynomial ℝ)).natDegree
        = (Polynomial.C (1 / 4) * Polynomial.X ^ 2 : Polynomial ℝ).natDegree :=
      natDegree_neg (p := (Polynomial.C (1 / 4) * Polynomial.X ^ 2 : Polynomial ℝ))
    have hmul : (Polynomial.C (1 / 4) * Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by
      refine le_trans natDegree_mul_le ?_
      rw [natDegree_C, _root_.zero_add]
      refine le_trans (natDegree_pow_le (p := (Polynomial.X : Polynomial ℝ)) (n := 2)) ?_
      rw [natDegree_X]
    have h := natDegree_add_le (Polynomial.C (1 : ℝ) : Polynomial ℝ)
      (-(Polynomial.C (1 / 4) * Polynomial.X ^ 2 : Polynomial ℝ))
    rw [sub_eq_add_neg] at ⊢
    refine le_trans h ?_
    rw [natDegree_C, hneg]
    exact max_le (by norm_num) hmul
  have h1 : ∀ i ∈ Finset.range (K + 1),
      (Polynomial.C (cReal i) *
        (Polynomial.C (1 : ℝ) - Polynomial.C (1 / 4) * Polynomial.X ^ 2) ^ i).natDegree ≤ 2 * K := by
    intro i hi
    have hiK : i ≤ K := by
      have hlt : i < K + 1 := Finset.mem_range.mp hi
      omega
    refine le_trans natDegree_mul_le ?_
    rw [natDegree_C, _root_.zero_add]
    refine le_trans (natDegree_pow_le
      (p := (Polynomial.C (1 : ℝ) - Polynomial.C (1 / 4) * Polynomial.X ^ 2 : Polynomial ℝ))
      (n := i)) ?_
    have hmul : i * (Polynomial.C (1 : ℝ) - Polynomial.C (1 / 4) * Polynomial.X ^ 2 : Polynomial ℝ).natDegree
        ≤ i * 2 := Nat.mul_le_mul_left i hfactor
    have hmul2 : i * 2 ≤ 2 * K := by omega
    omega
  unfold gapSignPolynomial
  refine le_trans natDegree_mul_le ?_
  have hmul : (Polynomial.C (1 / 2 : ℝ) * Polynomial.X).natDegree ≤ 1 := by
    have h : (Polynomial.C (1 / 2 : ℝ) * Polynomial.X).natDegree
        = (Polynomial.X : Polynomial ℝ).natDegree := by
      exact Polynomial.natDegree_C_mul (a := (1 / 2 : ℝ)) (p := (Polynomial.X : Polynomial ℝ))
        (by norm_num : (1 / 2 : ℝ) ≠ 0)
    rw [h, Polynomial.natDegree_X]
  have hsum : (∑ i ∈ Finset.range (K + 1),
      Polynomial.C (cReal i) *
        (Polynomial.C (1 : ℝ) - Polynomial.C (1 / 4) * Polynomial.X ^ 2) ^ i).natDegree ≤ 2 * K := by
    exact natDegree_sum_le_of_forall_le (Finset.range (K + 1))
      (fun i => Polynomial.C (cReal i) *
        (Polynomial.C (1 : ℝ) - Polynomial.C (1 / 4) * Polynomial.X ^ 2) ^ i) h1
  exact le_trans (add_le_add hmul hsum) (by omega)

/-- The natural ceiling of 4 log(2/(εδ))/δ² used to choose a gap sign truncation. -/
noncomputable def gapSignCutoff (δ ε : ℝ) : ℕ :=
  Nat.ceil (4 * Real.log (2 / (ε * δ)) / (δ * δ))

/-- For u in [0, 1] and natural `n`, the power (1 − u)ⁿ is at most exp(−un). -/
lemma one_sub_pow_le_exp {u : ℝ} (_hu : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) :
    (1 - u)^n ≤ Real.exp (-(u * (n : ℝ))) := by
  have h1 : 1 - u ≤ Real.exp (-u) := by
    have h := Real.add_one_le_exp (-u)
    linarith
  calc (1 - u)^n ≤ (Real.exp (-u))^n := pow_le_pow_left₀ (by nlinarith [hu1]) h1 n
    _ = Real.exp (-(u * (n : ℝ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-- A cutoff bound K ≤ 4L/D + 1 with D > 0 gives the degree bound 2K + 1 ≤ 8L/D + 3. -/
lemma gapDegreeBudget (K D L : ℝ) (hD : 0 < D) (hK : K ≤ 4 * L / D + 1) :
    2 * K + 1 ≤ 8 * L / D + 3 := by
  have h1 : K * D ≤ 4 * L + D := by
    have h := mul_le_mul_of_nonneg_right hK hD.le
    calc K * D ≤ (4 * L / D + 1) * D := h
      _ = 4 * L + D := by field_simp [ne_of_gt hD]
  have h2 : (K - 1) * D ≤ 4 * L := by nlinarith
  have h3 : (2 * K + 1) * D ≤ 8 * L + 3 * D := by nlinarith
  have h4 : 2 * K + 1 ≤ (8 * L + 3 * D) / D := (le_div_iff₀ hD).2 h3
  have h5 : (8 * L + 3 * D) / D = 8 * L / D + 3 := by
    field_simp [ne_of_gt hD]
  rw [h5] at h4
  exact h4

/-- The geometric error bound (2/δ)(1 − δ²/4)^(K + 1) `cReal (K + 1)` for the truncated sign
polynomial. -/
noncomputable def gapSignError (K : ℕ) (δ : ℝ) : ℝ :=
  (2 / δ) * (1 - δ ^ 2 / 4) ^ (K + 1) * cReal (K + 1)

/-- For positive gap `δ`, the gap sign polynomial satisfies `SignApproximation` with tolerance
`gapSignError K δ`. -/
theorem gapSign_approximation (K : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    Qatlib.Concepts.QsvtCore.ApproxToolkit.SignApproximation
      (gapSignPolynomial K) δ (gapSignError K δ) := by
  refine ⟨?_, ?_, gapSignPolynomial_odd K⟩
  · intro x hx
    exact gapSignPolynomial_abs_le_one K hx
  · intro x hx hgap
    exact gapSignPolynomial_error_le K hδ hgap hx

/-- For 0 < δ ≤ 2 and 0 < ε ≤ 1/2, a gap sign polynomial is odd, bounded by one on [−2, 2], and
approximates sign within `ε` outside the gap. Its degree is at most 8 log(2/(εδ))/δ² + 3. -/
theorem frontier1 (δ ε : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ (P : Polynomial ℝ) (K : ℕ),
      P = gapSignPolynomial K ∧
      P.natDegree ≤ 8 * Real.log (2 / (ε * δ)) / (δ * δ) + 3 ∧
      (∀ x : ℝ, P.eval (-x) = -P.eval x) ∧
      (∀ x : ℝ, |x| ≤ 2 → |P.eval x| ≤ 1) ∧
      (∀ x : ℝ, |x| ≤ 2 → δ ≤ |x| → |P.eval x - Real.sign x| ≤ ε) := by
  set K := gapSignCutoff δ ε with hKdef
  have hδε : 0 < ε * δ := mul_pos hε hδ
  have hlog : 0 ≤ Real.log (2 / (ε * δ)) := by
    have h1 : (1:ℝ) ≤ 2 / (ε * δ) := by
      rw [le_div_iff₀ hδε]
      have hmul : ε * δ ≤ (1 / 2) * 2 :=
        mul_le_mul hε2 hδ2 (by linarith : (0:ℝ) ≤ δ) (by norm_num)
      nlinarith
    exact (Real.log_nonneg (by linarith))
  have harg0 : (0:ℝ) ≤ 4 * Real.log (2 / (ε * δ)) / (δ * δ) := by
    have hD : 0 < δ * δ := mul_pos hδ hδ
    exact div_nonneg (mul_nonneg (by norm_num) hlog) (le_of_lt hD)
  have hKlow : (4 * Real.log (2 / (ε * δ)) / (δ * δ)) ≤ (K : ℝ) := by
    rw [hKdef, gapSignCutoff]
    exact Nat.le_ceil (4 * Real.log (2 / (ε * δ)) / (δ * δ))
  have hKup : (K : ℝ) ≤ 4 * Real.log (2 / (ε * δ)) / (δ * δ) + 1 := by
    rw [hKdef, gapSignCutoff]
    have h := Nat.ceil_lt_add_one harg0
    linarith
  have hu0 : (0:ℝ) ≤ δ ^ 2 / 4 := div_nonneg (sq_nonneg δ) (by norm_num)
  have hu1 : δ ^ 2 / 4 ≤ 1 := by
    have h1 := mul_self_le_mul_self hδ.le hδ2
    nlinarith [h1]
  have hgeom : (1 - δ ^ 2 / 4) ^ (K + 1) ≤ ε * δ / 2 := by
    have hexp : (1 - δ ^ 2 / 4) ^ (K + 1) ≤
        Real.exp (-((δ ^ 2 / 4) * ((K + 1 : ℕ) : ℝ))) :=
      one_sub_pow_le_exp hu0 hu1 (K + 1)
    have hK1 : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by
      push_cast
      rfl
    have hK1' : (4 * Real.log (2 / (ε * δ)) / (δ * δ)) ≤ ((K + 1 : ℕ) : ℝ) := by
      rw [hK1]
      linarith [hKlow]
    have harg : -((δ ^ 2 / 4) * ((K + 1 : ℕ) : ℝ)) ≤ -Real.log (2 / (ε * δ)) := by
      have hmul : Real.log (2 / (ε * δ)) ≤ (δ ^ 2 / 4) * ((K + 1 : ℕ) : ℝ) := by
        have h2 : (δ ^ 2 / 4) * (4 * Real.log (2 / (ε * δ)) / (δ * δ)) =
            Real.log (2 / (ε * δ)) := by
          field_simp [ne_of_gt (sq_pos_of_pos hδ)]
        calc Real.log (2 / (ε * δ))
              = (δ ^ 2 / 4) * (4 * Real.log (2 / (ε * δ)) / (δ * δ)) := h2.symm
          _ ≤ (δ ^ 2 / 4) * ((K + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hK1' (by positivity)
      linarith
    have hexp2 : Real.exp (-((δ ^ 2 / 4) * ((K + 1 : ℕ) : ℝ))) ≤
        Real.exp (-Real.log (2 / (ε * δ))) := Real.exp_le_exp.mpr harg
    have hexp3 : Real.exp (-Real.log (2 / (ε * δ))) = ε * δ / 2 := by
      rw [Real.exp_neg, Real.exp_log (by positivity : (0:ℝ) < 2 / (ε * δ))]
      field_simp [ne_of_gt (mul_pos hε hδ)]
    exact hexp.trans (hexp2.trans (le_of_eq hexp3))
  refine ⟨gapSignPolynomial K, K, rfl, ?_, ?_, ?_, ?_⟩
  · have hdeg : ((gapSignPolynomial K).natDegree : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) := by
      exact_mod_cast gapSignPolynomial_natDegree_le K
    have hD : 0 < δ * δ := mul_pos hδ hδ
    have hb := gapDegreeBudget (K : ℝ) (δ * δ) (Real.log (2 / (ε * δ))) hD hKup
    have hcast : ((2 * K + 1 : ℕ) : ℝ) = 2 * (K : ℝ) + 1 := by
      push_cast
      ring
    linarith
  · intro x
    exact gapSignPolynomial_odd K x
  · intro x hx
    exact gapSignPolynomial_abs_le_one K hx
  · intro x hx hgap
    have herr := gapSignPolynomial_error_le K hδ hgap hx
    have hcl : cReal (K + 1) ≤ 1 := cReal_le_one (K + 1)
    calc |(gapSignPolynomial K).eval x - Real.sign x|
        ≤ (2 / δ) * (1 - δ ^ 2 / 4) ^ (K + 1) * cReal (K + 1) := herr
      _ ≤ (2 / δ) * (1 - δ ^ 2 / 4) ^ (K + 1) := by
            have hbase : (0:ℝ) ≤ (2 / δ) * (1 - δ ^ 2 / 4) ^ (K + 1) := by
              have h1 : (0:ℝ) ≤ 2 / δ := by positivity
              have h2 : (0:ℝ) ≤ 1 - δ ^ 2 / 4 := by
                have h3 := mul_self_le_mul_self hδ.le hδ2
                nlinarith [h3]
              exact mul_nonneg h1 (pow_nonneg h2 (K + 1))
            have hstep := mul_le_mul_of_nonneg_left hcl hbase
            simpa using! hstep
      _ ≤ (2 / δ) * (ε * δ / 2) := by
            have hbase : (0:ℝ) ≤ 2 / δ := by positivity
            exact mul_le_mul_of_nonneg_left hgeom hbase
      _ = ε := by field_simp [ne_of_gt hδ]

end Qatlib.Concepts.QsvtCore.ApproxToolkit
