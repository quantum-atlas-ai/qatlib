/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PolyApprox.Lemma29RectangleApproximationStat
import Qatlib.Concepts.QsvtCore.PolyApprox.Lemma25SignApproximationGily

/-!
# Quantitative polynomial approximation of a rectangle

`lemma29RectangleApproximation_answer` proves the rectangle approximation specification for a
threshold separated from both zero and one by the gap parameter. The resulting real polynomial
is even, bounded on `[-1, 1]`, and approximates the inner and outer plateaus with the stated
degree and iteration bounds. See [GilyenSuLowWiebe2019].

## Main statements

* `lemma29RectangleApproximation_answer`: construct the bounded even rectangle approximant.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.QsvtCore.PolyApprox

open Polynomial Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
set_option maxHeartbeats 1000000 in

/-- For the stated gap, error, and threshold range, an even polynomial satisfies the rectangle
band inequalities and the specified degree and iteration bounds, realizing the formalized
version of [Gilyén et al., Lemma 29][GilyenSuLowWiebe2019]. -/
theorem lemma29RectangleApproximation_answer : Lemma29RectangleApproximation := by
  intro δ' ε' t hδ' hδ'2 hε' hε'2 ht1 ht2
  have hε'0 : 0 < ε' := hε'
  have hLpos : (0:ℝ) < Real.log (2/ε') := by
    have h1 : (1:ℝ) < 2/ε' := by
      rw [lt_div_iff₀ hε'0]
      norm_num
      linarith
    have h2 := (Real.log_lt_log_iff (by norm_num : (0:ℝ) < 1)
      (div_pos (by norm_num : (0:ℝ) < 2) hε'0)).mpr h1
    simpa using h2
  have hy0 : (0:ℝ) < 4*Real.log (2/ε')/(δ'*δ') :=
    div_pos (mul_pos (by norm_num : (0:ℝ) < 4) hLpos) (mul_pos hδ' hδ')
  obtain ⟨hlow, hhigh⟩ := sign158_pow_ceil_bounds hy0
  obtain ⟨k, hkd⟩ : ∃ k : ℕ, k = Nat.ceil
      (Real.log (4*Real.log (2/ε')/(δ'*δ')) / Real.log 2) := ⟨_, rfl⟩
  obtain ⟨Q1, hQ1⟩ : ∃ q : Polynomial ℝ, q = (signPolynomial k).comp
      (C (1/2:ℝ) * (X + C t)) := ⟨_, rfl⟩
  obtain ⟨Q2, hQ2⟩ : ∃ q : Polynomial ℝ, q = (signPolynomial k).comp
      (C (1/2:ℝ) * (C t - X)) := ⟨_, rfl⟩
  obtain ⟨P, hPd⟩ : ∃ p : Polynomial ℝ, p = C ((1 - ε'/2)/2) * (Q1 + Q2) + C (ε'/2) :=
    ⟨_, rfl⟩
  rw [← hkd] at hlow hhigh
  have cnonneg : (0:ℝ) ≤ (1 - ε'/2)/2 := by nlinarith [hε'2]
  have chalf : (1 - ε'/2)/2 ≤ 1/2 := by linarith
  have hQ1e : ∀ z : ℝ, Q1.eval z = (signPolynomial k).eval ((z+t)/2) := by
    intro z
    rw [hQ1, eval_comp]
    simp only [eval_mul, eval_C, eval_add, eval_X]
    rw [show (1/2:ℝ)*(z+t) = (z+t)/2 from by ring]
  have hQ2e : ∀ z : ℝ, Q2.eval z = (signPolynomial k).eval ((t-z)/2) := by
    intro z
    rw [hQ2, eval_comp]
    simp only [eval_mul, eval_C, eval_sub, eval_X]
    rw [show (1/2:ℝ)*(t-z) = (t-z)/2 from by ring]
  have hPe : ∀ z : ℝ, P.eval z =
      (1 - ε'/2)/2 * ((signPolynomial k).eval ((z+t)/2) +
        (signPolynomial k).eval ((t-z)/2)) + ε'/2 := by
    intro z
    rw [hPd]
    simp only [eval_add, eval_mul, eval_C, hQ1e, hQ2e]
  have hhalf0 : (δ'/2)^2 = (δ'*δ')/4 := by ring
  have hE : (1 - (δ'*δ')/4)^(2^k) ≤ ε'/2 := by
    have hu0 : (0:ℝ) ≤ (δ'/2)^2 := sq_nonneg _
    have hu1' : (δ'/2)^2 ≤ 1 := by
      have hδh : δ'/2 ≤ 1 := by linarith
      nlinarith [sq_nonneg (δ'/2)]
    have hc1 := sign158_one_sub_pow_le_exp hu0 hu1' (2^k)
    rw [hhalf0] at hc1
    have hlowc : 4*Real.log (2/ε')/(δ'*δ') ≤ ((2^k : ℕ) : ℝ) := by
      push_cast
      exact hlow
    have hu2 : Real.log (2/ε') ≤ (δ'*δ')/4 * ((2^k : ℕ) : ℝ) := by
      have h2 : (δ'*δ')/4 * (4*Real.log (2/ε')/(δ'*δ')) = Real.log (2/ε') := by
        field_simp
      calc Real.log (2/ε') = (δ'*δ')/4 * (4*Real.log (2/ε')/(δ'*δ')) := h2.symm
        _ ≤ (δ'*δ')/4 * ((2^k : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hlowc
          (div_nonneg (mul_nonneg hδ'.le hδ'.le) (by norm_num : (0:ℝ) ≤ 4))
    have hch2 : Real.exp (-((δ'*δ')/4 * ((2^k : ℕ) : ℝ))) ≤
        Real.exp (-(Real.log (2/ε'))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hu2]
    have hch3 : Real.exp (-(Real.log (2/ε'))) = ε'/2 := by
      rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num : (0:ℝ) < 2) hε'0)]
      field_simp
    exact le_trans (le_trans hc1 hch2) (le_of_eq hch3)
  refine ⟨P, k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hPd]
    have hinner1 : (C (1/2:ℝ) * (X + C t)).natDegree = 1 := by
      rw [natDegree_C_mul (by norm_num : (1/2:ℝ) ≠ 0), natDegree_X_add_C]
    have hinner2 : (C (1/2:ℝ) * (C t - X)).natDegree = 1 := by
      rw [natDegree_C_mul (by norm_num : (1/2:ℝ) ≠ 0)]
      have hsub : C t - X = -(X - C t) := by ring
      rw [hsub, natDegree_neg, natDegree_X_sub_C]
    have hdQ1 : Q1.natDegree = 3^k := by
      rw [hQ1, natDegree_comp, hinner1, signPolynomial_natDegree, mul_one]
    have hdQ2 : Q2.natDegree ≤ 3^k := by
      rw [hQ2, natDegree_comp, hinner2, signPolynomial_natDegree, mul_one]
    have hsum : (Q1 + Q2).natDegree ≤ 3^k := by
      apply le_trans (natDegree_add_le Q1 Q2)
      apply max_le hdQ1.le hdQ2
    have hcmul : (C ((1 - ε'/2)/2) * (Q1 + Q2)).natDegree ≤ 3^k := by
      rw [natDegree_C_mul (by nlinarith [hε'2] : ((1 - ε'/2)/2 : ℝ) ≠ 0)]
      exact hsum
    exact le_trans (natDegree_add_le _ _)
      (max_le hcmul (by simp [natDegree_C]))
  · have heq : 2*(4*Real.log (2/ε')/(δ'*δ')) = 8*Real.log (2/ε')/(δ'*δ') := by ring
    linarith [hhigh, heq]
  · show P.comp (-X) = C ((-1:ℝ)^(3^k+1)) * P
    rw [sign158_neg_one_pow_three_pow_add_one, C_1, one_mul]
    apply Polynomial.funext
    intro x
    rw [eval_comp, eval_neg, eval_X, hPe (-x), hPe x]
    ring_nf
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
    have hm1I : (x+t)/2 ∈ Set.Icc (-1:ℝ) 1 := by
      constructor
      · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
      · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
    have hm2I : (t-x)/2 ∈ Set.Icc (-1:ℝ) 1 := by
      constructor
      · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
      · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
    have b1 := abs_le.mp (signPolynomial_abs_le_one k hm1I)
    have b2 := abs_le.mp (signPolynomial_abs_le_one k hm2I)
    have hBB : (signPolynomial k).eval ((x+t)/2) + (signPolynomial k).eval ((t-x)/2) ≤
        1 + 1 := by linarith
    have hDD : -1 + -1 ≤ (signPolynomial k).eval ((x+t)/2) +
        (signPolynomial k).eval ((t-x)/2) := by linarith
    have hmU : (1-ε'/2)/2 * ((signPolynomial k).eval ((x+t)/2) +
        (signPolynomial k).eval ((t-x)/2)) ≤ (1-ε'/2)/2 * (1+1) :=
      mul_le_mul_of_nonneg_left hBB cnonneg
    have hmD : (1-ε'/2)/2 * (-1 + -1) ≤ (1-ε'/2)/2 * ((signPolynomial k).eval ((x+t)/2) +
        (signPolynomial k).eval ((t-x)/2)) :=
      mul_le_mul_of_nonneg_left hDD cnonneg
    have hvalU : (1-ε'/2)/2 * (1+1) = 1 - ε'/2 := by ring
    have hvalD : (1-ε'/2)/2 * (-1 + -1) = -(1 - ε'/2) := by ring
    rw [hPe x, abs_le]
    constructor
    · linarith [hmD, hvalD]
    · linarith [hmU, hvalU]
  · intro x hx hm1 hm2
    obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
    have hp1 : (0:ℝ) < (x+t)/2 := by
      rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      norm_num
      linarith
    have hp2 : (0:ℝ) < (t-x)/2 := by
      rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      norm_num
      linarith
    have hg1 : δ'/2 ≤ |(x+t)/2| := by rw [abs_of_pos hp1]; linarith
    have hg2 : δ'/2 ≤ |(t-x)/2| := by rw [abs_of_pos hp2]; linarith
    have hb1 : |(x+t)/2| ≤ 1 := by rw [abs_of_pos hp1]; linarith
    have hb2 : |(t-x)/2| ≤ 1 := by rw [abs_of_pos hp2]; linarith
    have e1 := signPolynomial_error_le (k := k) (δ := δ'/2)
      (div_pos hδ' (by norm_num : (0:ℝ) < 2)) hg1 hb1
    have e2 := signPolynomial_error_le (k := k) (δ := δ'/2)
      (div_pos hδ' (by norm_num : (0:ℝ) < 2)) hg2 hb2
    rw [Real.sign_of_pos hp1] at e1
    rw [Real.sign_of_pos hp2] at e2
    unfold signPolynomialError at e1 e2
    rw [hhalf0] at e1 e2
    have hm1I : (x+t)/2 ∈ Set.Icc (-1:ℝ) 1 := by
      constructor
      · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
      · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
    have hm2I : (t-x)/2 ∈ Set.Icc (-1:ℝ) 1 := by
      constructor
      · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
      · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
    have d1 := abs_le.mp e1
    have d2 := abs_le.mp e2
    have l1 : 1 - ε'/2 ≤ (signPolynomial k).eval ((x+t)/2) := by
      linarith [d1.2, hE]
    have l2 : 1 - ε'/2 ≤ (signPolynomial k).eval ((t-x)/2) := by
      linarith [d2.2, hE]
    have uu1 : (signPolynomial k).eval ((x+t)/2) ≤ 1 :=
      (abs_le.mp (signPolynomial_abs_le_one k hm1I)).2
    have uu2 : (signPolynomial k).eval ((t-x)/2) ≤ 1 :=
      (abs_le.mp (signPolynomial_abs_le_one k hm2I)).2
    rw [hPe x]
    constructor
    · have hAA : (1-ε'/2) + (1-ε'/2) ≤ (signPolynomial k).eval ((x+t)/2) +
          (signPolynomial k).eval ((t-x)/2) := by linarith [l1, l2]
      have hm : (1-ε'/2)/2 * ((1-ε'/2) + (1-ε'/2)) ≤ (1-ε'/2)/2 *
          ((signPolynomial k).eval ((x+t)/2) + (signPolynomial k).eval ((t-x)/2)) :=
        mul_le_mul_of_nonneg_left hAA cnonneg
      have hval : (1-ε'/2)/2 * ((1-ε'/2) + (1-ε'/2)) = 1 - ε' + (ε'^2)/4 := by ring
      linarith [hm, hval, sq_nonneg ε']
    · have hBB : (signPolynomial k).eval ((x+t)/2) + (signPolynomial k).eval ((t-x)/2) ≤
          1 + 1 := by linarith [uu1, uu2]
      have hm : (1-ε'/2)/2 * ((signPolynomial k).eval ((x+t)/2) +
          (signPolynomial k).eval ((t-x)/2)) ≤ (1-ε'/2)/2 * (1+1) :=
        mul_le_mul_of_nonneg_left hBB cnonneg
      have hval : (1-ε'/2)/2 * (1+1) = 1 - ε'/2 := by ring
      linarith [hm, hval]
  · intro x hx hor
    obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
    have hm1I : (x+t)/2 ∈ Set.Icc (-1:ℝ) 1 := by
      constructor
      · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
      · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
    have hm2I : (t-x)/2 ∈ Set.Icc (-1:ℝ) 1 := by
      constructor
      · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
      · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
    have hfin : (signPolynomial k).eval ((x+t)/2) + (signPolynomial k).eval ((t-x)/2) ≤
        (1 - (δ'*δ')/4)^(2^k) →
        -(1 - (δ'*δ')/4)^(2^k) ≤
          (signPolynomial k).eval ((x+t)/2) + (signPolynomial k).eval ((t-x)/2) →
        0 ≤ P.eval x ∧ P.eval x ≤ ε' := by
      intro aUp aLo
      have hAbot : (-ε':ℝ) ≤
          (signPolynomial k).eval ((x+t)/2) + (signPolynomial k).eval ((t-x)/2) := by
        linarith [aLo, hE]
      have hAtop : (signPolynomial k).eval ((x+t)/2) + (signPolynomial k).eval ((t-x)/2) ≤
          ε' := by linarith [aUp, hE]
      have hm1 : -((1-ε'/2)/2 * ε') ≤
          (1-ε'/2)/2 * ((signPolynomial k).eval ((x+t)/2) +
            (signPolynomial k).eval ((t-x)/2)) := by
        have h := mul_le_mul_of_nonneg_left hAbot cnonneg
        rw [mul_neg] at h
        exact h
      have hm2 : (1-ε'/2)/2 * ((signPolynomial k).eval ((x+t)/2) +
          (signPolynomial k).eval ((t-x)/2)) ≤ (1-ε'/2)/2 * ε' :=
        mul_le_mul_of_nonneg_left hAtop cnonneg
      have hce : (1-ε'/2)/2 * ε' ≤ (1:ℝ)/2 * ε' :=
        mul_le_mul_of_nonneg_right chalf hε'0.le
      rw [hPe x]
      constructor
      · linarith [hm1, hce]
      · linarith [hm2, hce]
    rcases hor with hleft | hright
    · have hn1 : (x+t)/2 < 0 := by
        rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
      have hp2 : (0:ℝ) < (t-x)/2 := by
        rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
      have hg1 : δ'/2 ≤ |(x+t)/2| := by rw [abs_of_neg hn1]; linarith
      have hg2 : δ'/2 ≤ |(t-x)/2| := by rw [abs_of_pos hp2]; linarith
      have hb1 : |(x+t)/2| ≤ 1 := by rw [abs_of_neg hn1]; linarith
      have hb2 : |(t-x)/2| ≤ 1 := by rw [abs_of_pos hp2]; linarith
      have e1 := signPolynomial_error_le (k := k) (δ := δ'/2)
        (div_pos hδ' (by norm_num : (0:ℝ) < 2)) hg1 hb1
      have e2 := signPolynomial_error_le (k := k) (δ := δ'/2)
        (div_pos hδ' (by norm_num : (0:ℝ) < 2)) hg2 hb2
      rw [Real.sign_of_neg hn1] at e1
      rw [Real.sign_of_pos hp2] at e2
      unfold signPolynomialError at e1 e2
      rw [hhalf0] at e1 e2
      have d1 := abs_le.mp e1
      have d2 := abs_le.mp e2
      have lo1 : -1 ≤ (signPolynomial k).eval ((x+t)/2) :=
        (abs_le.mp (signPolynomial_abs_le_one k hm1I)).1
      have hi2 : (signPolynomial k).eval ((t-x)/2) ≤ 1 :=
        (abs_le.mp (signPolynomial_abs_le_one k hm2I)).2
      exact hfin (by linarith [d1.1, hi2]) (by linarith [lo1, d2.2])
    · have hp1 : (0:ℝ) < (x+t)/2 := by
        rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
      have hn2 : (t-x)/2 < 0 := by
        rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
      have hg1 : δ'/2 ≤ |(x+t)/2| := by rw [abs_of_pos hp1]; linarith
      have hg2 : δ'/2 ≤ |(t-x)/2| := by rw [abs_of_neg hn2]; linarith
      have hb1 : |(x+t)/2| ≤ 1 := by rw [abs_of_pos hp1]; linarith
      have hb2 : |(t-x)/2| ≤ 1 := by rw [abs_of_neg hn2]; linarith
      have e1 := signPolynomial_error_le (k := k) (δ := δ'/2)
        (div_pos hδ' (by norm_num : (0:ℝ) < 2)) hg1 hb1
      have e2 := signPolynomial_error_le (k := k) (δ := δ'/2)
        (div_pos hδ' (by norm_num : (0:ℝ) < 2)) hg2 hb2
      rw [Real.sign_of_pos hp1] at e1
      rw [Real.sign_of_neg hn2] at e2
      unfold signPolynomialError at e1 e2
      rw [hhalf0] at e1 e2
      have d1 := abs_le.mp e1
      have d2 := abs_le.mp e2
      have hi1 : (signPolynomial k).eval ((x+t)/2) ≤ 1 :=
        (abs_le.mp (signPolynomial_abs_le_one k hm1I)).2
      have lo2 : -1 ≤ (signPolynomial k).eval ((t-x)/2) :=
        (abs_le.mp (signPolynomial_abs_le_one k hm2I)).1
      exact hfin (by linarith [hi1, d2.1]) (by linarith [d1.2, lo2])

end Qatlib.Concepts.QsvtCore.PolyApprox
