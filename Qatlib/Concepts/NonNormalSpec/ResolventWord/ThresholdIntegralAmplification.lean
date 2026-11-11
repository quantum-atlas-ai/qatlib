/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralDefs
import Qatlib.Concepts.LchsSimulation.Quadrature.GaussLegendreAuxiliary
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Integrated threshold amplification bounds

Integrating the complement of an even threshold polynomial gives an odd polynomial that
approximates `γ * x` on a smaller interval while remaining bounded on `[-1, 1]`. The module
proves primitive identities, scalar approximation estimates, and an explicit cutoff degree bound
for this construction in the context of [GilyenSuLowWiebe2019]

## Main statements

* `polynomial_increment_bounds`: controls polynomial increments using derivative bounds.
* `integratedThresholdPolynomial_scalar_bounds`: proves the global bound and inner approximation
  estimate.
* `integrated_threshold_amplifier`: packages oddness, degree, and approximation guarantees.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord
open Polynomial
open scoped BigOperators

/-- The derivative of the zero constant term polynomial primitive is the original polynomial. -/
theorem thresholdIntegralPrimitive_derivative (p : Polynomial ℝ) :
    (thresholdIntegralPrimitive p).derivative = p := by
  unfold thresholdIntegralPrimitive
  rw [Polynomial.derivative_sum]
  calc
    (∑ i ∈ Finset.range (p.natDegree + 1),
        (Polynomial.monomial (i + 1) (p.coeff i / (i + 1 : ℝ))).derivative) =
        ∑ i ∈ Finset.range (p.natDegree + 1), Polynomial.monomial i (p.coeff i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Polynomial.derivative_monomial_succ]
      congr 1
      exact div_mul_cancel₀ _ (by positivity)
    _ = p := p.as_sum_range.symm

/-- The polynomial primitive with zero constant term evaluates to zero at zero. -/
@[simp] theorem thresholdIntegralPrimitive_eval_zero (p : Polynomial ℝ) :
    (thresholdIntegralPrimitive p).eval 0 = 0 := by
  simp [thresholdIntegralPrimitive, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- Taking the polynomial primitive increases natural degree by at most one. -/
theorem thresholdIntegralPrimitive_natDegree_le (p : Polynomial ℝ) :
    (thresholdIntegralPrimitive p).natDegree ≤ p.natDegree + 1 := by
  unfold thresholdIntegralPrimitive
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_monomial_le _).trans (by
    have := Finset.mem_range.mp hi
    omega)

/-- The zero constant term primitive of an even polynomial evaluates as an odd function. -/
theorem thresholdIntegralPrimitive_odd (p : Polynomial ℝ)
    (heven : p.comp (-Polynomial.X) = p) (x : ℝ) :
    (thresholdIntegralPrimitive p).eval (-x) = -(thresholdIntegralPrimitive p).eval x := by
  let q := (thresholdIntegralPrimitive p).comp (-Polynomial.X) + thresholdIntegralPrimitive p
  have hder : q.derivative = 0 := by
    simp only [q, Polynomial.derivative_add, Polynomial.derivative_comp,
      thresholdIntegralPrimitive_derivative, Polynomial.derivative_neg,
      Polynomial.derivative_X, heven]
    ring
  have hz : q.eval 0 = 0 := by
    simp [q, Polynomial.eval_comp]
  have hq : q = 0 := by
    calc q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_derivative_eq_zero hder
      _ = 0 := by rw [Polynomial.coeff_zero_eq_eval_zero, hz]; simp
  have h := congrArg (fun r : Polynomial ℝ => r.eval x) hq
  simp only [q, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_neg,
    Polynomial.eval_X, Polynomial.eval_zero] at h
  linarith

/-- The integrated threshold polynomial has natural degree at most `2 * 3^k + 1`. -/
theorem integratedThresholdPolynomial_natDegree_le (γ δ : ℝ) (k : ℕ) :
    (integratedThresholdPolynomial γ δ k).natDegree ≤ 2 * 3 ^ k + 1 := by
  have hwin := thresholdPolynomial_natDegree_le ((1 - δ / 2) / γ) k
  have hc : (1 - thresholdPolynomial ((1 - δ / 2) / γ) k).natDegree ≤ 2 * 3 ^ k :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) hwin)
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((thresholdIntegralPrimitive_natDegree_le _).trans (Nat.add_le_add_right hc 1))

/-- The integrated threshold polynomial is odd under evaluation. -/
theorem integratedThresholdPolynomial_odd (γ δ : ℝ) (k : ℕ) (x : ℝ) :
    (integratedThresholdPolynomial γ δ k).eval (-x) =
      -(integratedThresholdPolynomial γ δ k).eval x := by
  have heven : (1 - thresholdPolynomial ((1 - δ / 2) / γ) k).comp (-Polynomial.X) =
      1 - thresholdPolynomial ((1 - δ / 2) / γ) k := by
    rw [Polynomial.sub_comp, Polynomial.one_comp, thresholdPolynomial_comp_neg_X]
  have h := thresholdIntegralPrimitive_odd _ heven x
  simp only [integratedThresholdPolynomial, Polynomial.eval_C_mul, h]
  ring

/-- The integrated threshold polynomial evaluates to zero at zero. -/
@[simp] theorem integratedThresholdPolynomial_eval_zero (γ δ : ℝ) (k : ℕ) :
    (integratedThresholdPolynomial γ δ k).eval 0 = 0 := by
  simp [integratedThresholdPolynomial]

/-- The derivative of the integrated threshold polynomial is `γ` times the complement of the
threshold polynomial at `(1 - δ / 2) / γ`. -/
theorem integratedThresholdPolynomial_derivative (γ δ : ℝ) (k : ℕ) :
    (integratedThresholdPolynomial γ δ k).derivative =
      Polynomial.C γ * (1 - thresholdPolynomial ((1 - δ / 2) / γ) k) := by
  simp [integratedThresholdPolynomial, thresholdIntegralPrimitive_derivative]

/-- Under the stated parameter bounds, the integrated threshold cutoff achieves the required
sign polynomial tolerance and degree at most `1 + 2048 * γ⁸ / δ⁴ * log (1 / tolerance)²`. -/
theorem integratedThresholdCutoff_bounds (γ δ ε : ℝ)
    (hγ : 1 ≤ γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hε : 0 < ε) (_hε1 : ε ≤ 1 / 2) :
    signPolynomialError (integratedThresholdGap γ δ) (integratedThresholdCutoff γ δ ε) ≤
        integratedThresholdTolerance γ δ ε ∧
    (2 * 3 ^ integratedThresholdCutoff γ δ ε + 1 : ℝ) ≤
      1 + 2048 * γ ^ 8 / δ ^ 4 *
        (Real.log (1 / integratedThresholdTolerance γ δ ε)) ^ 2 := by
  let g := integratedThresholdGap γ δ
  let t := integratedThresholdTolerance γ δ ε
  let L := Real.log (1 / t)
  let A := g⁻¹ ^ 2 * L
  let k := integratedThresholdCutoff γ δ ε
  have hγpos : 0 < γ := by linarith
  have hgpos : 0 < g := by dsimp [g, integratedThresholdGap]; positivity
  have hg8 : g ≤ 1 / 8 := by
    dsimp [g, integratedThresholdGap]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * γ ^ 2)).mpr
    nlinarith
  have htpos : 0 < t := by dsimp [t, integratedThresholdTolerance]; positivity
  have htδ : t ≤ δ / (4 * γ) := min_le_right _ _
  have ht8 : t ≤ 1 / 8 := by
    refine htδ.trans ?_
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * γ)).mpr
    nlinarith
  have h1t : (8 : ℝ) ≤ 1 / t := by
    apply (le_div_iff₀ htpos).mpr
    linarith
  have hL1 : 1 ≤ L := by
    dsimp [L]
    rw [Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < 1 / t)]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans h1t
  have hLpos : 0 < L := by linarith
  have hg1 : g ≤ 1 := by linarith
  have hginv : 1 ≤ g⁻¹ := by
    exact (one_le_inv₀ hgpos).mpr hg1
  have hA1 : 1 ≤ A := by
    have hinv2 : 1 ≤ g⁻¹ ^ 2 := by nlinarith
    simpa only [one_mul, A] using
      mul_le_mul hinv2 hL1 (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
  have hApos : 0 < A := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hkdef : k = Nat.ceil (Real.log A / Real.log 2) := rfl
  have hklow : Real.log A / Real.log 2 ≤ (k : ℝ) := by
    rw [hkdef]
    exact Nat.le_ceil _
  have hkupp : (k : ℝ) ≤ Real.log A / Real.log 2 + 1 := by
    rw [hkdef]
    exact (Nat.ceil_lt_add_one (div_nonneg hlogA hlog2.le)).le
  have hexp2 : Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have h2low : A ≤ (2 : ℝ) ^ k := by
    calc A = Real.exp (Real.log A) := (Real.exp_log hApos).symm
      _ ≤ Real.exp ((k : ℝ) * Real.log 2) := Real.exp_le_exp.mpr
        ((div_le_iff₀ hlog2).mp hklow)
      _ = (2 : ℝ) ^ k := hexp2
  have h2upp : (2 : ℝ) ^ k ≤ 2 * A := by
    calc (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := hexp2.symm
      _ ≤ Real.exp (Real.log A + Real.log 2) := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_right hkupp hlog2.le
        have he : (Real.log A / Real.log 2 + 1) * Real.log 2 =
            Real.log A + Real.log 2 := by field_simp
        rwa [he] at hh)
      _ = 2 * A := by
        rw [Real.exp_add, Real.exp_log hApos, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        ring
  have hgA : g ^ 2 * A = L := by
    dsimp [A]
    field_simp [hgpos.ne']
  have hbase : 1 - g ^ 2 ≤ Real.exp (-(g ^ 2)) := by
    have hh := Real.add_one_le_exp (-(g ^ 2))
    linarith
  have hbase0 : 0 ≤ 1 - g ^ 2 := by nlinarith
  have herr : signPolynomialError g k ≤ t := by
    unfold signPolynomialError
    calc (1 - g ^ 2) ^ (2 ^ k) ≤ (Real.exp (-(g ^ 2))) ^ (2 ^ k) :=
        pow_le_pow_left₀ hbase0 hbase _
      _ = Real.exp (((2 ^ k : ℕ) : ℝ) * (-(g ^ 2))) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_left h2low (sq_nonneg g)
        rw [hgA] at hh
        push_cast
        nlinarith)
      _ = t := by
        rw [Real.exp_neg]
        dsimp [L]
        rw [Real.exp_log (by positivity : (0 : ℝ) < 1 / t)]
        simp
  have h3 : (3 : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ 2 := by
    calc (3 : ℝ) ^ k ≤ (4 : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = ((2 : ℝ) ^ k) ^ 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, pow_two]
  have h3A : (3 : ℝ) ^ k ≤ 4 * A ^ 2 := by
    have hh := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
      (by positivity : (0 : ℝ) ≤ 2 * A)).mpr h2upp
    nlinarith
  have hginvdef : g⁻¹ = 4 * γ ^ 2 / δ := by
    dsimp [g, integratedThresholdGap]
    field_simp [hγpos.ne', hδ.ne']
  have hbudgeteq : 8 * A ^ 2 = 2048 * γ ^ 8 / δ ^ 4 * L ^ 2 := by
    dsimp [A]
    rw [hginvdef]
    field_simp [hδ.ne']
    ring
  constructor
  · exact herr
  · change 2 * (3 : ℝ) ^ k + 1 ≤ 1 + 2048 * γ ^ 8 / δ ^ 4 * L ^ 2
    rw [← hbudgeteq]
    linarith

/-- If a polynomial derivative lies between `lo` and `hi` on `[a, b]` with `a ≤ b`, its
increment lies between `lo * (b - a)` and `hi * (b - a)`. -/
theorem polynomial_increment_bounds (p : Polynomial ℝ) (a b lo hi : ℝ)
    (hab : a ≤ b)
    (hder : ∀ x ∈ Set.Icc a b, lo ≤ p.derivative.eval x ∧ p.derivative.eval x ≤ hi) :
    lo * (b - a) ≤ p.eval b - p.eval a ∧ p.eval b - p.eval a ≤ hi * (b - a) := by
  have hp := Qatlib.Concepts.LchsSimulation.Quadrature.intervalIntegrable_eval p.derivative a b
  have hlo := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => lo) MeasureTheory.volume a b)
    hp (fun x hx => (hder x hx).1)
  have hhi := intervalIntegral.integral_mono_on hab hp
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => hi) MeasureTheory.volume a b)
    (fun x hx => (hder x hx).2)
  rw [Qatlib.Concepts.LchsSimulation.Quadrature.integral_poly_derivative] at hlo hhi
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hlo hhi
  constructor <;> nlinarith

/-- If the sign polynomial error is within the integrated threshold tolerance, the amplifier has
absolute value at most `1 - δ / 8` on `[-1, 1]` and approximates `γ * x` within `ε / 2`
whenever `|x| ≤ (1 - δ) / γ`. -/
theorem integratedThresholdPolynomial_scalar_bounds (γ δ ε : ℝ) (k : ℕ)
    (hγ : 1 ≤ γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hε : 0 < ε)
    (herr : signPolynomialError (integratedThresholdGap γ δ) k ≤
      integratedThresholdTolerance γ δ ε) :
    (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |(integratedThresholdPolynomial γ δ k).eval x| ≤ 1 - δ / 8) ∧
    (∀ x : ℝ, |x| ≤ (1 - δ) / γ →
      |(integratedThresholdPolynomial γ δ k).eval x - γ * x| ≤ ε / 2) := by
  let p := integratedThresholdPolynomial γ δ k
  let τ := (1 - δ / 2) / γ
  let s := (1 - δ) / γ
  let u := (1 - δ / 4) / γ
  let g := integratedThresholdGap γ δ
  let t := integratedThresholdTolerance γ δ ε
  have hγpos : 0 < γ := by linarith
  have htpos : 0 < t := by dsimp [t, integratedThresholdTolerance]; positivity
  have htε : t ≤ ε := min_le_left _ _
  have htδ : t ≤ δ / (4 * γ) := min_le_right _ _
  have hγt : γ * t ≤ δ / 4 := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * γ)).mp htδ
    nlinarith
  have hτ : τ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [τ]; exact div_nonneg (by linarith) hγpos.le
    · dsimp [τ]; apply (div_le_iff₀ hγpos).mpr; linarith
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [s]; exact div_nonneg (by linarith) hγpos.le
    · dsimp [s]; apply (div_le_iff₀ hγpos).mpr; linarith
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [u]; exact div_nonneg (by linarith) hγpos.le
    · dsimp [u]; apply (div_le_iff₀ hγpos).mpr; linarith
  have hgpos : 0 < g := by dsimp [g, integratedThresholdGap]; positivity
  have hτγ : τ * γ = 1 - δ / 2 := by dsimp [τ]; field_simp
  have huγ : u * γ = 1 - δ / 4 := by dsimp [u]; field_simp
  have hτsq : τ ^ 2 * γ ^ 2 = (1 - δ / 2) ^ 2 := by
    rw [← mul_pow, hτγ]
  have hgsq : g * γ ^ 2 = δ / 4 := by
    dsimp [g, integratedThresholdGap]
    field_simp
  have hlow : ∀ x ∈ Set.Icc (0 : ℝ) s, (thresholdPolynomial τ k).eval x ≤ t / 2 := by
    intro x hx
    have hxγ : x * γ ≤ 1 - δ := by
      exact (le_div_iff₀ hγpos).mp hx.2
    have hxsq := (sq_le_sq₀ (mul_nonneg hx.1 hγpos.le)
      (by linarith : (0 : ℝ) ≤ 1 - δ)).mpr hxγ
    rw [mul_pow] at hxsq
    have hsep : g ≤ τ ^ 2 - x ^ 2 := by
      apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hγpos)).mp
      nlinarith
    have hind : thresholdIndicator τ x = 0 := by
      unfold thresholdIndicator
      rw [if_neg (by linarith : ¬ τ ^ 2 < x ^ 2)]
    have hgap : g ≤ |x ^ 2 - τ ^ 2| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have he := thresholdPolynomial_error_le k hτ hgpos hgap
      (abs_le.mpr ⟨by linarith [hx.1], hx.2.trans hs.2⟩)
    rw [hind, zero_sub, abs_neg] at he
    have hh : |(thresholdPolynomial τ k).eval x| ≤ t / 2 :=
      he.trans (div_le_div_of_nonneg_right herr (by norm_num))
    exact (le_abs_self _).trans hh
  have hhigh : ∀ x ∈ Set.Icc u (1 : ℝ), 1 - (thresholdPolynomial τ k).eval x ≤ t / 2 := by
    intro x hx
    have hx0 : 0 ≤ x := hu.1.trans hx.1
    have hxγ : 1 - δ / 4 ≤ x * γ := by
      exact (div_le_iff₀ hγpos).mp hx.1
    have hxsq := (sq_le_sq₀ (by linarith : (0 : ℝ) ≤ 1 - δ / 4)
      (mul_nonneg hx0 hγpos.le)).mpr hxγ
    rw [mul_pow] at hxsq
    have hsep : g ≤ x ^ 2 - τ ^ 2 := by
      apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hγpos)).mp
      nlinarith
    have hind : thresholdIndicator τ x = 1 := by
      unfold thresholdIndicator
      rw [if_pos (by linarith : τ ^ 2 < x ^ 2)]
    have hgap : g ≤ |x ^ 2 - τ ^ 2| := hsep.trans (le_abs_self _)
    have he := thresholdPolynomial_error_le k hτ hgpos hgap
      (abs_le.mpr ⟨by linarith [hu.1], hx.2⟩)
    rw [hind] at he
    exact (le_abs_self _).trans
      (he.trans (div_le_div_of_nonneg_right herr (by norm_num)))
  have hpder : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ p.derivative.eval x ∧ p.derivative.eval x ≤ γ := by
    intro x hx
    have hm := thresholdPolynomial_eval_mem_Icc k hτ (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)
    simp only [p, integratedThresholdPolynomial_derivative, Polynomial.eval_C_mul,
      Polynomial.eval_sub, Polynomial.eval_one]
    constructor <;> nlinarith [hm.1, hm.2]
  have hpu : p.eval u ≤ γ * u := by
    have hh := polynomial_increment_bounds p 0 u 0 γ hu.1
      (fun x hx => hpder x ⟨hx.1, hx.2.trans hu.2⟩)
    simpa [p] using hh.2
  have hpu1 : p.eval 1 - p.eval u ≤ γ * (t / 2) * (1 - u) := by
    apply (polynomial_increment_bounds p u 1 0 (γ * (t / 2)) hu.2 ?_).2
    intro x hx
    have hd := (hpder x ⟨hu.1.trans hx.1, hx.2⟩).1
    have he := mul_le_mul_of_nonneg_left (hhigh x hx) hγpos.le
    constructor
    · exact hd
    · simpa only [p, integratedThresholdPolynomial_derivative, Polynomial.eval_C_mul,
        Polynomial.eval_sub, Polynomial.eval_one] using he
  have hp1 : p.eval 1 ≤ 1 - δ / 8 := by
    have hh : γ * (t / 2) * (1 - u) ≤ γ * (t / 2) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (by linarith [hu.1] : 1 - u ≤ (1 : ℝ))
          (by positivity : (0 : ℝ) ≤ γ * (t / 2))
    nlinarith [hpu, hpu1, huγ, hγt]
  have hpnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ p.eval x := by
    intro x hx
    have hh := polynomial_increment_bounds p 0 x 0 γ hx.1
      (fun y hy => hpder y ⟨hy.1, hy.2.trans hx.2⟩)
    simpa [p] using hh.1
  have hpupper : ∀ x ∈ Set.Icc (0 : ℝ) 1, p.eval x ≤ 1 - δ / 8 := by
    intro x hx
    have hh := polynomial_increment_bounds p x 1 0 γ hx.2
      (fun y hy => hpder y ⟨hx.1.trans hy.1, hy.2⟩)
    linarith [hh.1, hp1]
  have hodd : ∀ x : ℝ, p.eval (-x) = -p.eval x := integratedThresholdPolynomial_odd γ δ k
  have hinnerpos : ∀ x ∈ Set.Icc (0 : ℝ) s, |p.eval x - γ * x| ≤ ε / 2 := by
    intro x hx
    let q := p - Polynomial.C γ * Polynomial.X
    have hdq : ∀ y ∈ Set.Icc (0 : ℝ) x,
        -(γ * (t / 2)) ≤ q.derivative.eval y ∧ q.derivative.eval y ≤ 0 := by
      intro y hy
      have hys : y ∈ Set.Icc (0 : ℝ) s := ⟨hy.1, hy.2.trans hx.2⟩
      have hm := thresholdPolynomial_eval_mem_Icc k hτ
        (abs_le.mpr ⟨by linarith [hy.1], hys.2.trans hs.2⟩)
      have he := mul_le_mul_of_nonneg_left (hlow y hys) hγpos.le
      simp only [q, p, Polynomial.derivative_sub, integratedThresholdPolynomial_derivative,
        Polynomial.derivative_C_mul_X, Polynomial.eval_sub, Polynomial.eval_C_mul,
        Polynomial.eval_one, Polynomial.eval_C]
      constructor <;> nlinarith [hm.1]
    have hh := polynomial_increment_bounds q 0 x (-(γ * (t / 2))) 0 hx.1 hdq
    have hqzero : q.eval 0 = 0 := by simp [q, p]
    simp only [hqzero, sub_zero, zero_mul] at hh
    have hxγ : γ * x ≤ 1 := by
      have hhx := (le_div_iff₀ hγpos).mp hx.2
      nlinarith
    have hsize : γ * (t / 2) * x ≤ t / 2 := by
      have he := mul_le_mul_of_nonneg_right hxγ (by positivity : (0 : ℝ) ≤ t / 2)
      nlinarith
    have hqe : |q.eval x| ≤ t / 2 := by
      rw [abs_of_nonpos hh.2]
      nlinarith [hh.1, hsize]
    have he : q.eval x = p.eval x - γ * x := by simp [q]
    rw [he] at hqe
    linarith
  constructor
  · intro x hx
    by_cases hx0 : 0 ≤ x
    · rw [abs_of_nonneg (hpnonneg x ⟨hx0, hx.2⟩)]
      exact hpupper x ⟨hx0, hx.2⟩
    · have hn : -x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hx.1]⟩
      have hh : |p.eval (-x)| ≤ 1 - δ / 8 := by
        rw [abs_of_nonneg (hpnonneg (-x) hn)]
        exact hpupper (-x) hn
      simpa only [hodd, abs_neg] using hh
  · intro x hx
    by_cases hx0 : 0 ≤ x
    · exact hinnerpos x ⟨hx0, by simpa only [abs_of_nonneg hx0] using hx⟩
    · have hn : -x ∈ Set.Icc (0 : ℝ) s :=
        ⟨by linarith, by simpa only [abs_of_neg (by linarith : x < 0)] using hx⟩
      have hh := hinnerpos (-x) hn
      have he : p.eval (-x) - γ * (-x) = -(p.eval x - γ * x) := by rw [hodd]; ring
      simpa only [he, abs_neg] using hh

/-- At the integrated threshold cutoff, the amplifier is odd, has the stated explicit degree
bound, is bounded by `1 - δ / 8` on `[-1, 1]`, and approximates `γ * x` within `ε / 2` on
`|x| ≤ (1 - δ) / γ`. -/
theorem integrated_threshold_amplifier (γ δ ε : ℝ)
    (hγ : 1 ≤ γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    let k := integratedThresholdCutoff γ δ ε
    let p := integratedThresholdPolynomial γ δ k
    p.natDegree ≤ 2 * 3 ^ k + 1 ∧
    (2 * 3 ^ k + 1 : ℝ) ≤
      1 + 2048 * γ ^ 8 / δ ^ 4 *
        (Real.log (1 / integratedThresholdTolerance γ δ ε)) ^ 2 ∧
    (∀ x : ℝ, p.eval (-x) = -p.eval x) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1 - δ / 8) ∧
    (∀ x : ℝ, |x| ≤ (1 - δ) / γ → |p.eval x - γ * x| ≤ ε / 2) := by
  obtain ⟨herr, hbudget⟩ := integratedThresholdCutoff_bounds γ δ ε hγ hδ hδ1 hε hε1
  obtain ⟨hglobal, hinner⟩ := integratedThresholdPolynomial_scalar_bounds γ δ ε
    (integratedThresholdCutoff γ δ ε) hγ hδ hδ1 hε herr
  exact ⟨integratedThresholdPolynomial_natDegree_le γ δ _, hbudget,
    integratedThresholdPolynomial_odd γ δ _, hglobal, hinner⟩

end Qatlib.Concepts.NonNormalSpec.ResolventWord
