/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.ApproxToolkit.DolphWindow

/-!
# Extremality and degree bounds for Dolph windows

This module proves the central-width extremality of the Dolph–Chebyshev polynomial and a
sufficient degree for suppressing the interval of radius 1 − δ. The results package the
windowing construction associated with Lemma 35, together with the degree-zero and
unit-tolerance cases. Background and related constructions are discussed in
[GilyenSuLowWiebe2019].

## Main statements

* `dolphFlatCenter_le_scale_inv`: bounds the flat-center width of a normalized polynomial.
* `dolphWindow_degree_budget`: proves the sufficient degree bound.
* `clause39_accepted`: collects the window construction and extremality guarantees.

## References

* [Gilyén et al., Lemma 35][GilyenSuLowWiebe2019]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit

open Polynomial
open scoped Classical BigOperators
open Qatlib.Concepts.QsvtCore.ApproxToolkit

/-- States that, for 0 < ε < 1, feasibility of `P` forces every positive flat-center radius to
be at most the reciprocal Dolph scale. -/
def DolphFlatCenterOptimal (n : ℕ) (ε : ℝ) (P : Polynomial ℝ) : Prop :=
  0 < ε → ε < 1 → DolphFeasible n P →
    ∀ lam : ℝ, 0 < lam → DolphFlatCenter P ε lam →
      lam ≤ (dolphWindowScale ε n)⁻¹

/-- States that, for every 0 < δ < 1, the selected Dolph-window degree suppresses the interval
|x| ≤ 1 − δ to tolerance `ε`. -/
def DolphDegreeBudget (ε : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 →
    DolphFlatCenter (dolphWindowPolynomial ε (dolphWindowDegree ε δ)) ε (1 - δ)

/-- Combines the conditional flat-center optimality statement for the Dolph polynomial with its
sufficient degree budget. -/
def DolphWindowComplete (n : ℕ) (ε : ℝ) : Prop :=
  (0 < ε → ε < 1 →
    DolphFlatCenterOptimal n ε (dolphWindowPolynomial ε n)) ∧
  DolphDegreeBudget ε

/-- A real polynomial of degree at most `n` bounded by one on [−1, 1] has value at most Tₙ(x)
for x ≥ 1. -/
theorem chebyshev_growth_le_of_norm_le_one {n : ℕ} {P : Polynomial ℝ} {x : ℝ}
    (hx : 1 ≤ x) (hPdeg : P.degree ≤ n)
    (hPbnd : ∀ y : ℝ, |y| ≤ 1 → |P.eval y| ≤ 1) :
    P.eval x ≤ (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x := by
  have h := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (n := n) (P := P) (k := 0) (x := x) hx hPdeg
      (fun y hy => hPbnd y (abs_le.mpr hy))
  simpa using h

/-- For positive `n` and 0 < ε < 1, a polynomial of degree at most `n` normalized at one cannot
have a positive ε-flat radius larger than the reciprocal Dolph scale. -/
theorem dolphFlatCenter_le_scale_inv {n : ℕ} {ε : ℝ} {P : Polynomial ℝ}
    (hn : 0 < n) (hε : 0 < ε) (hε1 : ε < 1)
    (hdeg : P.degree ≤ n)
    (hone : P.eval 1 = 1) {lam : ℝ} (hlam : 0 < lam)
    (hflat : DolphFlatCenter P ε lam) :
    lam ≤ (dolphWindowScale ε n)⁻¹ := by
  have hlam1 : lam < 1 := by
    by_contra hcon
    have hle : 1 ≤ lam := le_of_not_gt hcon
    have h1 : |P.eval 1| ≤ ε := hflat 1 (abs_le.mpr ⟨by linarith, hle⟩)
    rw [hone, abs_one] at h1
    linarith

  set R : Polynomial ℝ :=
    P.comp (Polynomial.C lam * Polynomial.X) * Polynomial.C (ε⁻¹) with hRdef
  have hRdeg : R.degree ≤ n := by
    have hnd : P.natDegree ≤ n :=
      (Polynomial.natDegree_le_iff_degree_le (p := P) (n := n)).mpr hdeg
    have hqnd : (Polynomial.C lam * Polynomial.X).natDegree ≤ 1 := by
      have h := Polynomial.natDegree_C_mul_le lam Polynomial.X
      simpa using h
    have hcomp : (P.comp (Polynomial.C lam * Polynomial.X)).natDegree ≤ n * 1 :=
      Polynomial.natDegree_comp_le.trans (Nat.mul_le_mul hnd hqnd)
    have hmul : R.natDegree ≤ n := by
      rw [hRdef]
      have h := Polynomial.natDegree_mul_le
        (p := P.comp (Polynomial.C lam * Polynomial.X)) (q := Polynomial.C (ε⁻¹))
      have hC : (Polynomial.C (ε⁻¹)).natDegree = 0 := by simp
      omega
    exact (Polynomial.natDegree_le_iff_degree_le (p := R) (n := n)).mp hmul
  have hRbnd : ∀ y : ℝ, |y| ≤ 1 → |R.eval y| ≤ 1 := by
    intro y hy
    have hlamy : |lam * y| ≤ lam := by
      rw [abs_mul]
      calc |lam| * |y| ≤ lam * |y| := by
            exact mul_le_mul_of_nonneg_right (le_of_eq (abs_of_nonneg hlam.le)) (abs_nonneg y)
        _ ≤ lam * 1 := by
            exact mul_le_mul_of_nonneg_left hy (le_of_lt hlam)
        _ = lam := by ring
    have h1 : |P.eval (lam * y)| ≤ ε := hflat (lam * y) hlamy
    have hq : Polynomial.eval y (Polynomial.C lam * Polynomial.X) = lam * y := by
      rw [Polynomial.eval_C_mul, Polynomial.eval_X]
    have hval : R.eval y = P.eval (lam * y) * ε⁻¹ := by
      rw [hRdef, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, hq]
    rw [hval, abs_mul]
    have hεinv : |ε⁻¹| = ε⁻¹ := by rw [abs_of_pos (inv_pos.mpr hε)]
    calc |P.eval (lam * y)| * |ε⁻¹| = |P.eval (lam * y)| * ε⁻¹ := by rw [hεinv]
      _ ≤ ε * ε⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hε.le)
      _ = 1 := mul_inv_cancel₀ hε.ne'
  have hq : Polynomial.eval lam⁻¹ (Polynomial.C lam * Polynomial.X) = 1 := by
    rw [Polynomial.eval_C_mul, Polynomial.eval_X]
    field_simp
  have hRval : R.eval lam⁻¹ = ε⁻¹ := by
    rw [hRdef, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, hq, hone, one_mul]
  have hinv1 : 1 ≤ lam⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hlam).mpr (by linarith)
  have hgrow : R.eval lam⁻¹ ≤ (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval lam⁻¹ :=
    chebyshev_growth_le_of_norm_le_one hinv1 hRdeg hRbnd
  have hT : ε⁻¹ ≤ (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval lam⁻¹ := by
    rw [hRval] at hgrow
    exact hgrow
  have hTc : (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (dolphWindowScale ε n) = ε⁻¹ :=
    dolphWindowScale_eval ε n hn hε (le_of_lt hε1)
  have hscale1 : 1 ≤ dolphWindowScale ε n := dolphWindowScale_ge_one ε n hε
  have hlam_inv : lam⁻¹ ≥ dolphWindowScale ε n := by
    by_contra hcon
    have hlt : lam⁻¹ < dolphWindowScale ε n := lt_of_not_ge hcon
    have hmono := chebyshev_strictMonoOn_one_le (n := (n : ℤ)) (by exact_mod_cast hn)
      (by linarith) (by linarith) hlt
    rw [hTc] at hmono
    linarith
  have hcpos : 0 < dolphWindowScale ε n := lt_of_lt_of_le zero_lt_one hscale1
  have hmul : dolphWindowScale ε n * lam ≤ 1 := by
    have h1 : dolphWindowScale ε n ≤ lam⁻¹ := hlam_inv.le
    calc dolphWindowScale ε n * lam ≤ lam⁻¹ * lam :=
        mul_le_mul_of_nonneg_right h1 hlam.le
      _ = 1 := by rw [inv_mul_cancel₀ hlam.ne']
  have hfinal : lam ≤ (dolphWindowScale ε n)⁻¹ := by
    have h1 : lam * dolphWindowScale ε n ≤ 1 := by
      calc lam * dolphWindowScale ε n = dolphWindowScale ε n * lam := mul_comm _ _
        _ ≤ 1 := hmul
    have h2 : lam ≤ 1 / dolphWindowScale ε n := (le_div_iff₀ hcpos).mpr h1
    have h3 : 1 / dolphWindowScale ε n = (dolphWindowScale ε n)⁻¹ := one_div _
    exact h2.trans_eq h3
  exact hfinal

/-- For positive degree and tolerance strictly between zero and one, the Dolph polynomial
satisfies `DolphFlatCenterOptimal`. -/
theorem dolphFlatCenter_optimal {n : ℕ} {ε : ℝ} (hn : 0 < n) (hε : 0 < ε) (hε1 : ε < 1) :
    DolphFlatCenterOptimal n ε (dolphWindowPolynomial ε n) := by
  intro _ _ hfeas
  obtain ⟨hdeg, _, hone, _⟩ := hfeas
  intro lam hlam hflat
  exact dolphFlatCenter_le_scale_inv hn hε hε1 hdeg hone hlam hflat

/-- For positive degree and 0 < ε ≤ 1, the Dolph polynomial satisfies the degree, interval
bound, and endpoint requirements of `DolphFeasible`. -/
theorem dolphWindow_feasible {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    DolphFeasible n (dolphWindowPolynomial ε n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hnd : (dolphWindowPolynomial ε n).natDegree = n :=
      dolphWindowPolynomial_natDegree ε n hn hε
    have hle : (dolphWindowPolynomial ε n).natDegree ≤ n := by omega
    exact (Polynomial.natDegree_le_iff_degree_le
      (p := dolphWindowPolynomial ε n) (n := n)).mp hle
  · exact dolphWindowPolynomial_norm_le_one ε n hn hε hε1
  · exact dolphWindowPolynomial_eval_one ε n hn hε hε1
  · exact dolphWindowPolynomial_eval_neg_one ε n hn hε hε1

/-- For 0 < ε ≤ 1, arcosh(ε⁻¹) is at most log(2/ε). -/
theorem arcosh_inv_le_log_two_div (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.arcosh (ε⁻¹) ≤ Real.log (2 / ε) := by
  have hεinv : 1 ≤ ε⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hε).mpr (by linarith)
  have hc1 : Real.cosh (Real.arcosh (ε⁻¹)) = ε⁻¹ := Real.cosh_arcosh hεinv
  have hc2 : Real.cosh (Real.log (2 / ε)) = (2 / ε + (2 / ε)⁻¹) / 2 :=
    Real.cosh_log (by positivity)
  have hge : ε⁻¹ ≤ (2 / ε + (2 / ε)⁻¹) / 2 := by
    have hinv : (2 / ε)⁻¹ = ε / 2 := by
      field_simp
    rw [hinv, inv_eq_one_div]
    field_simp; nlinarith [sq_nonneg ε]
  have hstep : Real.cosh (Real.arcosh (ε⁻¹)) ≤ Real.cosh (Real.log (2 / ε)) := by
    rw [hc1, hc2]
    exact hge
  have hlog0 : 0 ≤ Real.log (2 / ε) := by
    have h1 : (1 : ℝ) ≤ 2 / ε := (le_div_iff₀ hε).2 (by linarith)
    exact Real.log_nonneg h1
  exact (Real.cosh_strictMonoOn.le_iff_le (Real.arcosh_nonneg hεinv) hlog0).mp hstep

/-- For 0 < ε ≤ 1, the selected degree makes the Dolph polynomial ε-flat on every target
interval of radius 1 − δ with 0 < δ < 1. -/
theorem dolphWindow_degree_budget {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    DolphDegreeBudget ε := by
  intro δ hδ hδ1
  have hsqrt : 0 < Real.sqrt (2 * δ) := Real.sqrt_pos.mpr (by positivity)
  have hlog : 0 < Real.log (2 / ε) := Real.log_pos (by
    apply (lt_div_iff₀ hε).2
    linarith)
  have hq : 0 < Real.log (2 / ε) / Real.sqrt (2 * δ) := div_pos hlog hsqrt
  have hnpos : 0 < dolphWindowDegree ε δ := Nat.ceil_pos.mpr hq
  set n := dolphWindowDegree ε δ with hndef
  have hnge : Real.log (2 / ε) / Real.sqrt (2 * δ) ≤ (dolphWindowDegree ε δ : ℝ) := by
    have h := Nat.le_ceil (Real.log (2 / ε) / Real.sqrt (2 * δ))
    simpa [dolphWindowDegree] using h
  have hscale : dolphWindowScale ε n ≤ 1 / (1 - δ) := by
    unfold dolphWindowScale generalizedChebyshev
    have harcosh : Real.arcosh (ε⁻¹) ≤ Real.log (2 / ε) :=
      arcosh_inv_le_log_two_div ε hε hε1
    have hεinv : 1 ≤ ε⁻¹ := by
      rw [inv_eq_one_div]
      exact (le_div_iff₀ hε).mpr (by linarith)
    have h1 : (1 / (n : ℝ)) * Real.arcosh (ε⁻¹) ≤ (1 / (n : ℝ)) * Real.log (2 / ε) := by
      exact mul_le_mul_of_nonneg_left harcosh (by positivity)
    have h2 : (1 / (n : ℝ)) * Real.log (2 / ε) ≤ Real.sqrt (2 * δ) := by
      have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hmul : Real.log (2 / ε) ≤ (n : ℝ) * Real.sqrt (2 * δ) := by
        have h := (div_le_iff₀ hsqrt).mp hnge
        simpa [hndef] using h
      have hmul' : Real.log (2 / ε) ≤ Real.sqrt (2 * δ) * (n : ℝ) := by
        simpa [mul_comm] using hmul
      have h2' := (div_le_iff₀ hnreal).mpr hmul'
      convert! h2' using 1; ring
    have h3 : Real.cosh ((1 / (n : ℝ)) * Real.arcosh (ε⁻¹))
        ≤ Real.cosh (Real.sqrt (2 * δ)) := by
      refine (Real.cosh_strictMonoOn.le_iff_le ?_ ?_).mpr ?_
      · have hnonneg : 0 ≤ (1 / (n : ℝ)) * Real.arcosh (ε⁻¹) :=
          mul_nonneg (div_nonneg (by norm_num) (by positivity))
            (Real.arcosh_nonneg hεinv)
        exact hnonneg
      · exact hsqrt.le
      · exact h1.trans h2
    have h4 : Real.cosh (Real.sqrt (2 * δ)) ≤ 1 / (1 - δ) := by
      have hc := Real.cosh_le_exp_half_sq (Real.sqrt (2 * δ))
      have hexp : Real.exp ((Real.sqrt (2 * δ)) ^ 2 / 2) = Real.exp δ := by
        rw [Real.sq_sqrt (by positivity)]
        norm_num
      rw [hexp] at hc
      have hinexp : Real.exp δ ≤ 1 / (1 - δ) := by
        have hone : 1 - δ ≤ Real.exp (-δ) := by
          have := Real.add_one_le_exp (-δ)
          linarith
        have hexppos : 0 < Real.exp δ := Real.exp_pos _
        have hcancel : Real.exp (-δ) * Real.exp δ = 1 := by
          rw [Real.exp_neg, inv_mul_cancel₀ hexppos.ne']
        have hmm : Real.exp δ * (1 - δ) ≤ Real.exp δ * Real.exp (-δ) :=
          mul_le_mul_of_nonneg_left hone hexppos.le
        have hmul : (1 - δ) * Real.exp δ ≤ 1 := by
          calc (1 - δ) * Real.exp δ = Real.exp δ * (1 - δ) := by ring
            _ ≤ Real.exp δ * Real.exp (-δ) := hmm
            _ = 1 := by rw [Real.exp_neg, mul_inv_cancel₀ hexppos.ne']
        have hmul' : Real.exp δ * (1 - δ) ≤ 1 := by simpa [mul_comm] using hmul
        exact (le_div_iff₀ (by linarith)).mpr hmul'
      exact hc.trans hinexp
    exact h3.trans h4
  have hscale_pos : 0 < dolphWindowScale ε n := by
    unfold dolphWindowScale generalizedChebyshev
    exact Real.cosh_pos _
  have hflat : DolphFlatCenter (dolphWindowPolynomial ε n) ε (1 - δ) := by
    have hiff := dolphWindow_flatCenter_iff ε n hnpos hε hε1 (1 - δ) (by linarith)
    refine hiff.mpr ?_
    have hmul : (1 - δ) * dolphWindowScale ε n ≤ 1 := by
      have hle := mul_le_mul_of_nonneg_right hscale (by linarith : (0 : ℝ) ≤ 1 - δ)
      have hcancel : (1 - δ) * (1 / (1 - δ)) = 1 := by
        rw [one_div]
        exact mul_inv_cancel₀ (by linarith : (1 : ℝ) - δ ≠ 0)
      linarith
    have h1 : 1 - δ ≤ 1 / dolphWindowScale ε n := (le_div_iff₀ hscale_pos).mpr hmul
    rw [← inv_eq_one_div] at h1
    exact h1
  simpa [hndef] using hflat

/-- At degree zero, the Dolph scale is one and the Dolph polynomial is the constant polynomial
`ε`. -/
theorem dolphWindow_degree_zero (ε : ℝ) :
    dolphWindowScale ε 0 = 1 ∧
      dolphWindowPolynomial ε 0 = Polynomial.C ε ∧
      (∀ x : ℝ, (dolphWindowPolynomial ε 0).eval x = ε) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold dolphWindowScale generalizedChebyshev
    have hone : (1 : ℝ) / ((0 : ℕ) : ℝ) = 0 := by norm_num
    rw [hone, zero_mul, Real.cosh_zero]
  · unfold dolphWindowPolynomial
    have hT : Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ) = 1 := by
      simp [Polynomial.Chebyshev.T_zero]
    rw [hT, Polynomial.one_comp, mul_one]
  · intro x
    have h : dolphWindowPolynomial ε 0 = Polynomial.C ε := by
      unfold dolphWindowPolynomial
      have hT : Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ) = 1 := by
        simp [Polynomial.Chebyshev.T_zero]
      rw [hT, Polynomial.one_comp, mul_one]
    rw [h, Polynomial.eval_C]

/-- At tolerance one and positive degree, the Dolph scale is one and the window equals the
ordinary Chebyshev polynomial, bounded by one on [−1, 1]. -/
theorem dolphWindow_eps_one {n : ℕ} (hn : 0 < n) :
    dolphWindowScale 1 n = 1 ∧
      (∀ x : ℝ, (dolphWindowPolynomial 1 n).eval x =
        (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x) ∧
      (∀ x : ℝ, |x| ≤ 1 → |(dolphWindowPolynomial 1 n).eval x| ≤ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold dolphWindowScale generalizedChebyshev
    have hone : Real.arcosh (1 : ℝ)⁻¹ = 0 := by
      rw [inv_one, Real.arcosh_zero]
    rw [hone, mul_zero, Real.cosh_zero]
  · intro x
    have hscale : dolphWindowScale 1 n = 1 := by
      unfold dolphWindowScale generalizedChebyshev
      have hone : Real.arcosh (1 : ℝ)⁻¹ = 0 := by
        rw [inv_one, Real.arcosh_zero]
      rw [hone, mul_zero, Real.cosh_zero]
    rw [dolphWindowPolynomial_eval, hscale]
    simp only [one_mul]
  · intro x hx
    exact dolphWindowPolynomial_norm_le_one 1 n hn (by norm_num) (le_refl 1) x hx

/-- For positive degree and tolerance strictly between zero and one, the Dolph polynomial
satisfies the combined optimality and degree-budget specification. -/
theorem dolphWindowComplete {n : ℕ} {ε : ℝ} (hn : 0 < n) (hε : 0 < ε) (hε1 : ε < 1) :
    DolphWindowComplete n ε := by
  refine ⟨?_, ?_⟩
  · intro hε' hε1'
    exact dolphFlatCenter_optimal hn hε' hε1'
  · exact dolphWindow_degree_budget hε (le_of_lt hε1)

/-- Collects the exact degree, feasibility, sharp flat-center characterization, extremal width
bound, and sufficient degree formula for the Dolph window, including its degree-zero and
unit-tolerance cases [Gilyén et al., Lemma 35][GilyenSuLowWiebe2019]. -/
theorem clause39_accepted :
    (∀ (n : ℕ) (ε : ℝ), 0 < n → 0 < ε → ε < 1 →
      (dolphWindowPolynomial ε n).natDegree = n ∧
      DolphFeasible n (dolphWindowPolynomial ε n) ∧
      (∀ lam : ℝ, 0 < lam →
        (DolphFlatCenter (dolphWindowPolynomial ε n) ε lam ↔
          lam ≤ (dolphWindowScale ε n)⁻¹)) ∧
      (∀ P : Polynomial ℝ, DolphFeasible n P →
        ∀ lam : ℝ, 0 < lam → DolphFlatCenter P ε lam →
          lam ≤ (dolphWindowScale ε n)⁻¹)) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ δ : ℝ, 0 < δ → δ < 1 →
      dolphWindowDegree ε δ =
        Nat.ceil (Real.log (2 / ε) / Real.sqrt (2 * δ)) ∧
      DolphFlatCenter
        (dolphWindowPolynomial ε (dolphWindowDegree ε δ)) ε (1 - δ)) ∧
    (∀ ε : ℝ, dolphWindowScale ε 0 = 1 ∧
      dolphWindowPolynomial ε 0 = Polynomial.C ε ∧
      ∀ x : ℝ, (dolphWindowPolynomial ε 0).eval x = ε) ∧
    (∀ n : ℕ, 0 < n → dolphWindowScale 1 n = 1 ∧
      (∀ x : ℝ, (dolphWindowPolynomial 1 n).eval x =
        (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x) ∧
      ∀ x : ℝ, |x| ≤ 1 → |(dolphWindowPolynomial 1 n).eval x| ≤ 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n ε hn hε hε1
    refine ⟨dolphWindowPolynomial_natDegree ε n hn hε,
      dolphWindow_feasible hn hε hε1.le, ?_, ?_⟩
    · intro lam hlam
      exact dolphWindow_flatCenter_iff ε n hn hε hε1.le lam hlam
    · intro P hP lam hlam hflat
      exact dolphFlatCenter_le_scale_inv hn hε hε1 hP.1 hP.2.2.1 hlam hflat
  · intro ε hε hε1 δ hδ hδ1
    exact ⟨rfl, dolphWindow_degree_budget hε hε1 δ hδ hδ1⟩
  · intro ε
    exact dolphWindow_degree_zero ε
  · intro n hn
    exact dolphWindow_eps_one hn

end Qatlib.Concepts.QsvtCore.ApproxToolkit
