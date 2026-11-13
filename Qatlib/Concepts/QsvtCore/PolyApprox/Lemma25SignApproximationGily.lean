/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PolyApprox.Lemma25SignApproximationStat
import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed

/-!
# Quantitative polynomial approximation of the sign function

`lemma25SignApproximation_answer` proves the sign approximation specification with an odd
polynomial bounded on `[-2, 2]`. Supporting estimates control powers, exponential decay, and the
natural ceiling used to choose the iteration count. See [GilyenSuLowWiebe2019].

## Main statements

* `sign158_one_sub_pow_le_exp`: bound a power by exponential decay.
* `lemma25SignApproximation_answer`: construct a sign approximant with the stated quantitative
  bounds.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.QsvtCore.PolyApprox

open Polynomial Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib

/-- Negative one raised to `3^k` equals negative one. -/
theorem sign158_neg_one_pow_three_pow (k : ℕ) : (-1:ℝ)^(3^k) = -1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ 3 k, pow_mul, ih]
    norm_num

/-- Negative one raised to `3^k + 1` equals one. -/
theorem sign158_neg_one_pow_three_pow_add_one (k : ℕ) : (-1:ℝ)^(3^k+1) = 1 := by
  rw [pow_succ, sign158_neg_one_pow_three_pow k]
  norm_num

/-- For `0 ≤ u ≤ 1`, the power `(1 - u)^n` is at most `exp (-u * n)`. -/
theorem sign158_one_sub_pow_le_exp {u : ℝ} (_hu : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) :
    (1 - u)^n ≤ Real.exp (-(u*(n:ℝ))) := by
  have h1 : 1 - u ≤ Real.exp (-u) := by
    have h := Real.add_one_le_exp (-u)
    linarith
  calc (1 - u)^n ≤ (Real.exp (-u))^n := pow_le_pow_left₀ (by nlinarith [hu1]) h1 n
    _ = Real.exp (-(u*(n:ℝ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-- For positive `y`, the power of two chosen using the natural ceiling of `log y / log 2` lies
between `y` and `2 * y + 2`. -/
theorem sign158_pow_ceil_bounds {y : ℝ} (hy0 : 0 < y) :
    y ≤ (2:ℝ)^(Nat.ceil (Real.log y / Real.log 2)) ∧
      (2:ℝ)^(Nat.ceil (Real.log y / Real.log 2)) ≤ 2*y + 2 := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2
  set k := Nat.ceil (Real.log y / Real.log 2) with hkd
  have hlow : y ≤ (2:ℝ)^k := by
    have hdiv : Real.log y / Real.log 2 ≤ (k:ℝ) := by exact_mod_cast Nat.le_ceil _
    have h1 : Real.log y ≤ (k:ℝ)*Real.log 2 := (div_le_iff₀ hlog2).mp hdiv
    have h2 : Real.log y ≤ Real.log ((2:ℝ)^k) := by
      rw [Real.log_pow]
      linarith
    exact (Real.log_le_log_iff hy0 (pow_pos two_pos k)).mp h2
  have hhigh : (2:ℝ)^k ≤ 2*y + 2 := by
    by_cases hx : Real.log y / Real.log 2 < 0
    · have hk0 : k = 0 := by
        have hkz : k ≤ 0 := (Nat.ceil_le).mpr (by
          rw [Nat.cast_zero]
          exact le_of_lt hx)
        exact Nat.le_zero.mp hkz
      rw [hk0]
      simp
      nlinarith [hy0]
    · have hx0 : 0 ≤ Real.log y / Real.log 2 := not_lt.mp hx
      have hkx : (k:ℝ) < Real.log y / Real.log 2 + 1 :=
        Nat.ceil_lt_add_one hx0
      have hxx : Real.log y / Real.log 2 * Real.log 2 = Real.log y := by
        field_simp
      have hkl : (k:ℝ)*Real.log 2 < Real.log y + Real.log 2 := by
        nlinarith [hkx, hlog2, hxx]
      have h2 : Real.log ((2:ℝ)^k) < Real.log (2*y) := by
        rw [Real.log_pow, Real.log_mul two_ne_zero (ne_of_gt hy0)]
        linarith
      have h3 : (2:ℝ)^k < 2*y :=
        (Real.log_lt_log_iff (pow_pos two_pos k) (by positivity)).mp h2
      linarith
  exact ⟨hlow, hhigh⟩

/-- For the stated gap and error range, an odd polynomial bounded on `[-2, 2]` approximates the
sign function outside the gap with the specified degree and iteration bounds, realizing the
formalized version of [Gilyén et al., Lemma 25][GilyenSuLowWiebe2019]. -/
theorem lemma25SignApproximation_answer : Lemma25SignApproximation := by
  intro δ ε hδ hδ2 hε hε2
  have hε0 : 0 < ε := hε
  have hinv : (2:ℝ) ≤ 1/ε := by
    rw [le_div_iff₀ hε0]
    rw [show 2*ε = 1 - (1 - 2*ε) from by ring]
    nlinarith [hε2]
  have hL2 : Real.log 2 ≤ Real.log (1/ε) :=
    (Real.log_le_log_iff (by norm_num : (0:ℝ) < 2) (one_div_pos.mpr hε0)).mpr hinv
  have hlogpos : (0:ℝ) < Real.log (1/ε) :=
    lt_of_lt_of_le (Real.log_pos (by norm_num : (1:ℝ) < 2)) hL2
  have hy0 : (0:ℝ) < 4*Real.log (1/ε)/(δ*δ) :=
    div_pos (mul_pos (by norm_num : (0:ℝ) < 4) hlogpos) (mul_pos hδ hδ)
  obtain ⟨hlow, hhigh⟩ := sign158_pow_ceil_bounds hy0
  set k := Nat.ceil (Real.log (4*Real.log (1/ε)/(δ*δ)) / Real.log 2) with hkd
  set P := (signPolynomial k).comp (C (1/2:ℝ) * X) with hPd
  have hPeval : ∀ z : ℝ, P.eval z = (signPolynomial k).eval (z/2) := by
    intro z
    rw [hPd, eval_comp, eval_mul, eval_C, eval_X, show (1/2:ℝ)*z = z/2 from by ring]
  refine ⟨P, k, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hPd, Polynomial.natDegree_comp, signPolynomial_natDegree,
      Polynomial.natDegree_C_mul (by norm_num : (1/2:ℝ) ≠ 0), Polynomial.natDegree_X, mul_one]
  · have heq : 2*(4*Real.log (1/ε)/(δ*δ)) = 8*Real.log (1/ε)/(δ*δ) := by ring
    linarith [hhigh, heq]
  · show P.comp (-X) = C ((-1:ℝ)^(3^k)) * P
    rw [sign158_neg_one_pow_three_pow k]
    apply Polynomial.funext
    intro x
    rw [eval_comp, Polynomial.eval_neg, Polynomial.eval_X, hPeval (-x),
      show (-x)/2 = -(x/2) from by ring, signPolynomial_eval_neg k (x/2),
      eval_mul, eval_C, hPeval x]
    ring
  · intro x hx
    have hx1 : (-2:ℝ) ≤ x := hx.1
    have hx2 : x ≤ 2 := hx.2
    have hq : x/2 ∈ Set.Icc (-1:ℝ) 1 := by
      rw [Set.mem_Icc]
      constructor
      · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
      · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
        norm_num
        linarith
    rw [hPeval x]
    exact signPolynomial_abs_le_one k hq
  · intro x hx hgap
    have hxe : x ≠ 0 := by
      intro h
      rw [h] at hgap
      simp at hgap
      exact absurd hgap (by linarith : ¬(δ ≤ 0))
    have hsign : Real.sign (x/2) = Real.sign x := by
      rcases lt_or_gt_of_ne hxe with hneg | hpos
      · rw [Real.sign_of_neg (by linarith : (0:ℝ) > x/2), Real.sign_of_neg hneg]
      · rw [Real.sign_of_pos (by linarith : (0:ℝ) < x/2), Real.sign_of_pos hpos]
    have hq1 : |x/2| ≤ 1 := by
      rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      have hax : |x| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2]
      linarith
    have hq2 : δ/2 ≤ |x/2| := by
      rw [abs_div, abs_two]
      nlinarith [hgap]
    have herr := signPolynomial_error_le (k := k) (δ := δ/2)
      (div_pos hδ (by norm_num : (0:ℝ) < 2)) hq2 hq1
    rw [hsign] at herr
    unfold signPolynomialError at herr
    rw [hPeval x, abs_sub_comm]
    have hu0 : (0:ℝ) ≤ (δ/2)^2 := sq_nonneg _
    have hu1 : (δ/2)^2 ≤ 1 := by
      have hδh : δ/2 ≤ 1 := by linarith
      nlinarith [sq_nonneg (δ/2)]
    have hchain1 := sign158_one_sub_pow_le_exp hu0 hu1 (2^k)
    have hhalf : (δ/2)^2 = (δ*δ)/4 := by ring
    rw [hhalf] at herr hchain1
    have hlowc : 4*Real.log (1/ε)/(δ*δ) ≤ ((2^k : ℕ) : ℝ) := by
      push_cast
      exact hlow
    have hu2 : Real.log (1/ε) ≤ (δ*δ)/4 * ((2^k : ℕ) : ℝ) := by
      have h2 : (δ*δ)/4 * (4*Real.log (1/ε)/(δ*δ)) = Real.log (1/ε) := by
        field_simp
      calc Real.log (1/ε) = (δ*δ)/4 * (4*Real.log (1/ε)/(δ*δ)) := h2.symm
        _ ≤ (δ*δ)/4 * ((2^k : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hlowc
          (div_nonneg (mul_nonneg hδ.le hδ.le) (by norm_num : (0:ℝ) ≤ 4))
    have hchain2 : Real.exp (-((δ*δ)/4 * ((2^k : ℕ) : ℝ))) ≤
        Real.exp (-(Real.log (1/ε))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hu2]
    have hchain3 : Real.exp (-(Real.log (1/ε))) = ε := by
      rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr hε0)]
      field_simp
    exact le_trans (le_trans herr hchain1) (le_trans hchain2 (le_of_eq hchain3))

end Qatlib.Concepts.QsvtCore.PolyApprox
