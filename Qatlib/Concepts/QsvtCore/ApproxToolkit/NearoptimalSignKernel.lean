/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralAmplification
import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralCoefficients
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Qatlib.Concepts.RandCompile.EffectiveInput.QuantizedCoefficientQDrift
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Chebyshev kernels for sign separation

This module integrates a nonnegative even kernel formed from second-kind Chebyshev polynomials
to obtain the odd bounded `separator`. It proves a constant-error sign approximation outside a
gap and implements the kernel, primitive, normalization, and coefficient rounding using rational
lists. Background and related constructions are discussed in [GilyenSuLowWiebe2019].

## Main statements

* `sign_error`: bounds sign error by 32/((n + 1)δ).
* `separator_degree`: gives the degree bound 4n + 3.
* `nativeSeparator_semantics`: connects rational coefficients to the separator polynomial.
* `nativeRounded_eval_error`: controls evaluation error after dyadic rounding.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit
open Polynomial
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open Qatlib
open scoped Classical BigOperators

/-- The even kernel (1 − X²/4) Uₙ(1 − X²/2)² built from the second-kind Chebyshev polynomial. -/
def polynomial (n : ℕ) : Polynomial ℝ :=
  (1-C (1/4)*X^2) * ((Polynomial.Chebyshev.U ℝ (n:ℤ)).comp (1-C (1/2)*X^2))^2

/-- Evaluating the kernel at `x` gives (1 − x²/4) Uₙ(1 − x²/2)². -/
theorem eval (n : ℕ) (x : ℝ) :
    (polynomial n).eval x = (1-x^2/4)*((Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (1-x^2/2))^2 := by
  simp only [polynomial,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_one,
    Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_comp]
  rw [show (1/4:ℝ)*x^2 = x^2/4 by ring, show (1/2:ℝ)*x^2 = x^2/2 by ring]

/-- The kernel polynomial is invariant under substitution of −X for X. -/
theorem even (n : ℕ) : (polynomial n).comp (-X) = polynomial n := by
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_comp,Polynomial.eval_neg,Polynomial.eval_X,eval,neg_sq]

/-- A real number of absolute value at most two has square at most four. -/
theorem square_le_four {x : ℝ} (hx : |x| ≤ 2) : x^2 ≤ 4 := by
  have h := mul_self_le_mul_self (abs_nonneg x) hx
  nlinarith [sq_abs x]

/-- The kernel is nonnegative throughout [−2, 2]. -/
theorem nonneg (n : ℕ) {x : ℝ} (hx : |x| ≤ 2) : 0 ≤ (polynomial n).eval x := by
  rw [eval]
  exact mul_nonneg (by nlinarith [square_le_four hx]) (sq_nonneg _)

/-- On [−1, 1], the Chebyshev identity (1 − z²) Uₙ(z)² + Tₙ₊₁(z)² = 1 holds for every integer
order. -/
theorem energy (n : ℤ) (z : ℝ) (hz0 : -1 ≤ z) (hz1 : z ≤ 1) :
    (1-z^2)*((Polynomial.Chebyshev.U ℝ n).eval z)^2+
      ((Polynomial.Chebyshev.T ℝ (n+1)).eval z)^2 = 1 := by
  let θ := Real.arccos z
  have hc : Real.cos θ = z := Real.cos_arccos hz0 hz1
  have hu := Polynomial.Chebyshev.U_real_cos θ n
  have ht := Polynomial.Chebyshev.T_real_cos θ (n+1)
  rw [hc] at hu ht
  have hsq := congrArg (fun x : ℝ => x^2) hu

  rw [mul_pow] at hsq
  have htrig := Real.sin_sq_add_cos_sq (((n:ℝ)+1)*θ)
  have hθ := Real.sin_sq_add_cos_sq θ
  rw [hc] at hθ
  have ht' : (Polynomial.Chebyshev.T ℝ (n+1)).eval z = Real.cos (((n:ℝ)+1)*θ) := by
    simpa only [Int.cast_add,Int.cast_one] using! ht
  rw [ht']
  nlinarith [hsq]

/-- On [−2, 2], the kernel multiplied by x² is at most one. -/
theorem weighted_le_one (n : ℕ) {x : ℝ} (hx : |x| ≤ 2) :
    x^2*(polynomial n).eval x ≤ 1 := by
  have hx2 := square_le_four hx
  have he := energy (n:ℤ) (1-x^2/2) (by nlinarith) (by nlinarith [sq_nonneg x])
  rw [eval]
  nlinarith [sq_nonneg ((Polynomial.Chebyshev.T ℝ ((n:ℤ)+1)).eval (1-x^2/2))]

/-- For 0 < x ≤ 2, the kernel is at most 1/x². -/
theorem le_inverse_square (n : ℕ) {x : ℝ} (hx : |x| ≤ 2) (hpos : 0 < x) :
    (polynomial n).eval x ≤ 1/x^2 := by
  exact (le_div_iff₀ (sq_pos_of_pos hpos)).mpr (by
    simpa only [mul_comm] using! weighted_le_one n hx)

/-- For x in [0, 1], arcsin(x) is at most 2x. -/
theorem arcsin_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.arcsin x ≤ 2*x := by
  have h := Real.mul_le_sin (Real.arcsin_nonneg.mpr hx0) (Real.arcsin_le_pi_div_two x)
  rw [Real.sin_arcsin (by linarith) hx1] at h
  have hh := (div_le_iff₀ Real.pi_pos).mp (show 2*Real.arcsin x/Real.pi ≤ x by
    convert! h using 1; ring)
  nlinarith [mul_nonneg hx0 (show 0 ≤ 4-Real.pi by linarith [Real.pi_lt_four])]

/-- For x in [0, π/2], sin(x) is at least x/2. -/
theorem half_le_sin {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ Real.pi/2) :
    x/2 ≤ Real.sin x := by
  have h := Real.mul_le_sin hx0 hx1
  have hs : 0 ≤ Real.sin x := (show 0 ≤ 2/Real.pi*x by positivity).trans h
  have hh := (div_le_iff₀ Real.pi_pos).mp (show 2*x/Real.pi ≤ Real.sin x by
    convert! h using 1; ring)
  nlinarith [mul_nonneg hs (show 0 ≤ 4-Real.pi by linarith [Real.pi_lt_four])]

/-- The polynomial `thresholdIntegralPrimitive p` evaluates to the integral of `p` from zero to
the input. -/
theorem primitive_eval (p : Polynomial ℝ) (x : ℝ) :
    (thresholdIntegralPrimitive p).eval x = ∫ t in (0:ℝ)..x,p.eval t := by
  have h :=
      Qatlib.Concepts.LchsSimulation.Quadrature.integral_poly_derivative
      (thresholdIntegralPrimitive p) 0 x
  rw [thresholdIntegralPrimitive_derivative,thresholdIntegralPrimitive_eval_zero,sub_zero] at h
  exact h.symm

/-- For 0 ≤ x ≤ 1/(4(n + 1)), the kernel is at least (n + 1)²/8. -/
theorem near_zero_lower (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 1/(4*((n:ℝ)+1))) :
    ((n:ℝ)+1)^2/8 ≤ (polynomial n).eval x := by
  by_cases hz : x=0
  · subst x
    norm_num [eval,Polynomial.Chebyshev.U_eval_one]
    nlinarith [sq_nonneg ((n:ℝ)+1)]
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hz)
  let N : ℝ := (n:ℝ)+1
  have hN : 1 ≤ N := by dsimp [N]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hNp : 0 < N := by linarith
  have hprod : 4*N*x ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : (0:ℝ)<4*N)).mp hx
    nlinarith
  have hxquarter : x ≤ 1/4 := by nlinarith [mul_nonneg (show 0 ≤ N-1 by linarith) hx0]
  have hx1 : x/2 ≤ 1 := by linarith
  let θ : ℝ := 2*Real.arcsin (x/2)
  have hθp : 0 < θ := by
    dsimp [θ]
    exact mul_pos (by norm_num) (Real.arcsin_pos.mpr (by positivity))
  have hθ0 : 0 ≤ θ := hθp.le
  have hθle : θ ≤ 2*x := by
    have h := arcsin_le_two_mul (show 0 ≤ x/2 by positivity) hx1
    dsimp [θ]
    linarith
  have hNθ : N*θ ≤ 1/2 := by
    have h := mul_le_mul_of_nonneg_left hθle hNp.le
    nlinarith
  have hθsmall : θ ≤ 1/2 := by
    nlinarith [mul_nonneg (show 0 ≤ N-1 by linarith) hθ0]
  have hsinp : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθp (by linarith [Real.pi_gt_three])
  have hc : Real.cos θ = 1-x^2/2 := by
    have hi := Real.sin_sq_add_cos_sq (Real.arcsin (x/2))
    rw [Real.sin_arcsin (by linarith) hx1] at hi
    dsimp [θ]
    rw [Real.cos_two_mul]
    nlinarith
  have hu := Polynomial.Chebyshev.U_real_cos θ (n:ℤ)
  rw [hc] at hu
  have hu' : (Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (1-x^2/2)*Real.sin θ =
      Real.sin (N*θ) := by simpa only [Int.cast_natCast,N] using! hu
  have hs := half_le_sin (show 0 ≤ N*θ by positivity)
    (show N*θ ≤ Real.pi/2 by linarith [Real.pi_gt_three])
  have hl : (N/2)*Real.sin θ ≤ (Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (1-x^2/2)*Real.sin θ := by
    calc
      _ ≤ (N/2)*θ := mul_le_mul_of_nonneg_left (Real.sin_le hθ0) (by positivity)
      _ = (N*θ)/2 := by ring
      _ ≤ Real.sin (N*θ) := hs
      _ = _ := hu'.symm
  have hU : N/2 ≤ (Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (1-x^2/2) := by
    nlinarith [hl]
  have hUsq : (N/2)^2 ≤ ((Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (1-x^2/2))^2 := by
    simpa only [pow_two] using! mul_self_le_mul_self (show 0 ≤ N/2 by positivity) hU
  have hxsq : x^2 ≤ 1 := by
    have h := mul_self_le_mul_self hx0 (show x ≤ 1 by linarith)
    nlinarith
  have hfac : (3/4:ℝ) ≤ 1-x^2/4 := by linarith
  have hb := mul_le_mul hfac hUsq (sq_nonneg (N/2)) (by linarith : 0 ≤ 1-x^2/4)
  change N^2/8 ≤ (polynomial n).eval x
  rw [eval]
  nlinarith [sq_nonneg N]

/-- The value at two of the kernel primitive, representing its integral from zero to two. -/
def mass (n : ℕ) : ℝ := (thresholdIntegralPrimitive (polynomial n)).eval 2

/-- The kernel primitive is monotone between any ordered pair of points in [−2, 2]. -/
theorem primitive_mono (n : ℕ) {a b : ℝ} (ha : -2 ≤ a) (hb : b ≤ 2) (hab : a ≤ b) :
    (thresholdIntegralPrimitive (polynomial n)).eval a ≤
      (thresholdIntegralPrimitive (polynomial n)).eval b := by
  have hid := Qatlib.Concepts.LchsSimulation.Quadrature.integral_poly_derivative
    (thresholdIntegralPrimitive (polynomial n)) a b
  rw [thresholdIntegralPrimitive_derivative] at hid
  have hnon : 0 ≤ ∫ x in a..b,(polynomial n).eval x := by
    apply intervalIntegral.integral_nonneg hab
    intro x hx
    exact nonneg n (abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩)
  rw [hid] at hnon
  linarith

/-- The kernel mass is at least (n + 1)/32. -/
theorem mass_lower (n : ℕ) : ((n:ℝ)+1)/32 ≤ mass n := by
  let N : ℝ := (n:ℝ)+1
  let w : ℝ := 1/(4*N)
  have hN : 1 ≤ N := by dsimp [N]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hNp : 0 < N := by linarith
  have hw : 0 < w := by dsimp [w]; positivity
  have hwsmall : w ≤ 1/4 := by
    dsimp [w]
    apply (div_le_iff₀ (show 0 < 4*N by positivity)).mpr
    nlinarith
  have hlo := intervalIntegral.integral_mono_on hw.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => N^2/8) MeasureTheory.volume 0 w)
    (Qatlib.Concepts.LchsSimulation.Quadrature.intervalIntegrable_eval (polynomial n) 0 w)
    (fun x hx => near_zero_lower n hx.1 hx.2)
  rw [intervalIntegral.integral_const] at hlo
  rw [← primitive_eval] at hlo
  have heq : w*(N^2/8) = N/32 := by dsimp [w]; field_simp; ring
  simp only [sub_zero,smul_eq_mul] at hlo
  rw [heq] at hlo
  exact hlo.trans (primitive_mono n (by linarith) (by norm_num) (by linarith [hwsmall]))

/-- The kernel mass is strictly positive. -/
theorem mass_pos (n : ℕ) : 0 < mass n :=
  lt_of_lt_of_le (by positivity) (mass_lower n)

/-- The kernel primitive divided by its mass, giving a normalized polynomial separator. -/
def separator (n : ℕ) : Polynomial ℝ :=
  C ((mass n)⁻¹)*thresholdIntegralPrimitive (polynomial n)

/-- The separator value equals the kernel primitive value divided by the kernel mass. -/
theorem separator_eval (n : ℕ) (x : ℝ) :
    (separator n).eval x = (thresholdIntegralPrimitive (polynomial n)).eval x/mass n := by
  simp only [separator,Polynomial.eval_mul,Polynomial.eval_C,div_eq_mul_inv,mul_comm]

/-- The normalized separator is odd. -/
theorem separator_odd (n : ℕ) (x : ℝ) : (separator n).eval (-x) = -(separator n).eval x := by
  rw [separator_eval,separator_eval,thresholdIntegralPrimitive_odd _ (even n)]
  ring

/-- The normalized separator has absolute value at most one on [−2, 2]. -/
theorem separator_abs_le (n : ℕ) {x : ℝ} (hx : |x| ≤ 2) : |(separator n).eval x| ≤ 1 := by
  have hpos (y : ℝ) (hy : 0 ≤ y) (hy2 : y ≤ 2) : |(separator n).eval y| ≤ 1 := by
    have hlo := primitive_mono n (a := 0) (b := y) (by norm_num) hy2 hy
    simp only [thresholdIntegralPrimitive_eval_zero] at hlo
    have hhi := primitive_mono n (a := y) (b := 2) (by linarith) (by norm_num) hy2
    rw [separator_eval,abs_of_nonneg (div_nonneg hlo (mass_pos n).le)]
    exact (div_le_one (mass_pos n)).mpr hhi
  by_cases h : 0 ≤ x
  · exact hpos x h (abs_le.mp hx).2
  · rw [show (separator n).eval x = -(separator n).eval (-x) by rw [separator_odd]; ring,abs_neg]
    exact hpos (-x) (by linarith) (by linarith [(abs_le.mp hx).1])

/-- For 0 < x ≤ 2, the kernel mass beyond `x` is at most 1/x. -/
theorem primitive_tail (n : ℕ) {x : ℝ} (hx : 0 < x) (hx2 : x ≤ 2) :
    mass n-(thresholdIntegralPrimitive (polynomial n)).eval x ≤ 1/x := by
  have hno : (0:ℝ) ∉ Set.uIcc x 2 := by
    rw [Set.uIcc_of_le hx2]
    intro h
    linarith [h.1]
  have hi : IntervalIntegrable (fun y : ℝ => 1/y^2) MeasureTheory.volume x 2 := by
    simpa only [zpow_neg,zpow_ofNat,one_div] using!
      (intervalIntegral.intervalIntegrable_zpow (n := (-2:ℤ)) (Or.inr hno) :
        IntervalIntegrable (fun y : ℝ => y^(-2:ℤ)) MeasureTheory.volume x 2)
  have he : (∫ y in x..2,1/y^2) = 1/x-1/2 := by
    calc
      _ = ∫ y in x..2,y^(-2:ℤ) := by
        congr 1
        funext y
        simp only [zpow_neg,zpow_ofNat,one_div]
      _ = _ := integral_zpow (Or.inr ⟨by decide,hno⟩)
      _ = _ := by norm_num; ring
  have hmono := intervalIntegral.integral_mono_on hx2
    (Qatlib.Concepts.LchsSimulation.Quadrature.intervalIntegrable_eval (polynomial n) x 2) hi (fun y hy =>
      le_inverse_square n (abs_le.mpr ⟨by linarith [hy.1],hy.2⟩) (by linarith [hy.1]))
  rw [he] at hmono
  have hid := Qatlib.Concepts.LchsSimulation.Quadrature.integral_poly_derivative
    (thresholdIntegralPrimitive (polynomial n)) x 2
  rw [thresholdIntegralPrimitive_derivative] at hid
  change (∫ y in x..2,(polynomial n).eval y) = mass n-(thresholdIntegralPrimitive (polynomial n)).eval x at hid
  rw [hid] at hmono
  linarith

/-- For 0 < x ≤ 2, the separator differs from one by at most 32/((n + 1)x). -/
theorem positive_error (n : ℕ) {x : ℝ} (hx : 0 < x) (hx2 : x ≤ 2) :
    |(separator n).eval x-1| ≤ 32/(((n:ℝ)+1)*x) := by
  have hm := mass_pos n
  have hN : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hb := separator_abs_le n (abs_le.mpr ⟨by linarith,hx2⟩)
  have ht := primitive_tail n hx hx2
  calc
    _ = (mass n-(thresholdIntegralPrimitive (polynomial n)).eval x)/mass n := by
      rw [abs_of_nonpos (by linarith [(abs_le.mp hb).2]),separator_eval]
      field_simp
      ring
    _ ≤ (1/x)/mass n := div_le_div_of_nonneg_right ht hm.le
    _ ≤ (1/x)/(((n:ℝ)+1)/32) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (mass_lower n)
    _ = _ := by field_simp

/-- On [−2, 2] outside a positive gap `δ`, the separator approximates the sign function with
error at most 32/((n + 1)δ). -/
theorem sign_error (n : ℕ) {δ x : ℝ} (hδ : 0 < δ) (hx : |x| ≤ 2) (hgap : δ ≤ |x|) :
    |(separator n).eval x-Real.sign x| ≤ 32/(((n:ℝ)+1)*δ) := by
  have hN : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hpos (y : ℝ) (hy : 0 < y) (hy2 : y ≤ 2) (hδy : δ ≤ y) :
      |(separator n).eval y-1| ≤ 32/(((n:ℝ)+1)*δ) :=
    (positive_error n hy hy2).trans (div_le_div_of_nonneg_left (by norm_num)
      (by positivity) (mul_le_mul_of_nonneg_left hδy hN.le))
  by_cases hp : 0 < x
  · rw [Real.sign_of_pos hp]
    exact hpos x hp (abs_le.mp hx).2 (by simpa only [abs_of_pos hp] using! hgap)
  · have hn : x < 0 := by
      by_contra hh
      have hz : x=0 := by linarith
      simp [hz] at hgap
      linarith
    rw [Real.sign_of_neg hn,sub_neg_eq_add]
    have he : (separator n).eval x+1 = -((separator n).eval (-x)-1) := by
      rw [separator_odd]
      ring
    rw [he,abs_neg]
    exact hpos (-x) (by linarith) (by linarith [(abs_le.mp hx).1])
      (by simpa only [abs_of_neg hn] using! hgap)

/-- The kernel polynomial has natural degree at most 4n + 2. -/
theorem degree (n : ℕ) : (polynomial n).natDegree ≤ 4*n+2 := by
  have hb (a : ℝ) : (1-C a*X^2 : Polynomial ℝ).natDegree ≤ 2 := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have hc : ((Polynomial.Chebyshev.U ℝ (n:ℤ)).comp (1-C (1/2)*X^2)).natDegree ≤ 2*n := by
    refine Polynomial.natDegree_comp_le.trans ?_
    rw [Polynomial.Chebyshev.natDegree_U_natCast]
    exact (Nat.mul_le_mul_left n (hb (1/2))).trans (by omega)
  have hs : (((Polynomial.Chebyshev.U ℝ (n:ℤ)).comp (1-C (1/2)*X^2))^2).natDegree ≤ 4*n := by
    rw [Polynomial.natDegree_pow]
    omega
  unfold polynomial
  exact Polynomial.natDegree_mul_le.trans (by have h := hb (1/4); omega)

/-- The separator polynomial has natural degree at most 4n + 3. -/
theorem separator_degree (n : ℕ) : (separator n).natDegree ≤ 4*n+3 := by
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((thresholdIntegralPrimitive_natDegree_le _).trans (by have h := degree n; omega))

/-- If (n + 1)δ ≥ 128, the separator approximates the sign function within 1/4 on [−2, 2]
outside the gap. -/
theorem constant_error (n : ℕ) {δ x : ℝ} (hδ : 0 < δ) (hlevel : 128 ≤ ((n:ℝ)+1)*δ)
    (hx : |x| ≤ 2) (hgap : δ ≤ |x|) : |(separator n).eval x-Real.sign x| ≤ 1/4 := by
  exact (sign_error n hδ hx hgap).trans ((div_le_iff₀ (by positivity)).mpr (by linarith))

end Qatlib.Concepts.QsvtCore.ApproxToolkit

end

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit.Kernel
open Polynomial
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open Qatlib
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord

/-- Computes rational coefficient lists for the consecutive second-kind Chebyshev polynomials Uₙ
and Uₙ₊₁ using their recurrence. -/
def nativeUPair : ℕ → List ℚ × List ℚ
  | 0 => ([1],[0,2])
  | n+1 => let p := nativeUPair n
      (p.2,ratSubList (ratMulList [0,2] p.2) p.1)

/-- The rational coefficient list for the order-`n` second-kind Chebyshev polynomial obtained
from `nativeUPair`. -/
def nativeU (n : ℕ) : List ℚ := (nativeUPair n).1

/-- The rational coefficient list implementing the even Chebyshev kernel. -/
def nativeKernel (n : ℕ) : List ℚ :=
  let us := rationalPolynomialCompose (nativeU n) [1,0,-1/2]
  ratMulList [1,0,-1/4] (ratMulList us us)

/-- Evaluates a rational coefficient list at a rational input by Horner's rule. -/
def nativeEval (xs : List ℚ) (x : ℚ) : ℚ := xs.foldr (fun a b => a+x*b) 0

/-- The rational coefficient list for the zero-constant primitive of the kernel. -/
def nativePrimitive (n : ℕ) : List ℚ := rationalIntegralCoefficients 1 (nativeKernel n)
/-- The rational value obtained by evaluating the kernel primitive at two. -/
def nativeMass (n : ℕ) : ℚ := nativeEval (nativePrimitive n) 2

/-- The rational coefficient list obtained by dividing the primitive coefficients by `nativeMass
n`. -/
def nativeSeparator (n : ℕ) : List ℚ :=
  (nativePrimitive n).map (fun a => a/nativeMass n)

/-- The two rational lists computed by `nativeUPair n` represent Uₙ and Uₙ₊₁ over the real
numbers. -/
theorem nativeUPair_semantics (n : ℕ) :
    realTarget (nativeUPair n).1 = Chebyshev.U ℝ (n:ℤ) ∧
    realTarget (nativeUPair n).2 = Chebyshev.U ℝ ((n+1:ℕ):ℤ) := by
  induction n with
  | zero =>
    constructor
    · simp [nativeUPair,realTarget_cons]
    · simp [nativeUPair,realTarget_cons,Polynomial.C_ofNat]; ring
  | succ n ih =>
    change realTarget (nativeUPair n).2 = Chebyshev.U ℝ ((n+1:ℕ):ℤ) ∧
      realTarget (ratSubList (ratMulList [0,2] (nativeUPair n).2) (nativeUPair n).1) =
        Chebyshev.U ℝ ((n+2:ℕ):ℤ)
    refine ⟨ih.2,?_⟩
    rw [realTarget_sub,realTarget_mul,ih.1,ih.2]
    rw [show ((n+2:ℕ):ℤ) = (n:ℤ)+2 by omega,Chebyshev.U_add_two]
    simp only [realTarget_cons,realTarget_nil,Rat.cast_zero,Rat.cast_ofNat,
      Polynomial.C_0,Polynomial.C_ofNat,mul_zero,add_zero,zero_add]
    push_cast
    ring

/-- The rational list `nativeU n` represents the real second-kind Chebyshev polynomial Uₙ. -/
theorem nativeU_semantics (n : ℕ) : realTarget (nativeU n) = Chebyshev.U ℝ (n:ℤ) :=
  (nativeUPair_semantics n).1

/-- The rational list `nativeKernel n` represents the real kernel polynomial. -/
theorem nativeKernel_semantics (n : ℕ) : realTarget (nativeKernel n) = polynomial n := by
  simp only [nativeKernel,realTarget_mul,rationalPolynomialCompose_semantics,nativeU_semantics]
  have hquarter : realTarget [1,0,-1/4] = (1-C (1/4)*X^2 : Polynomial ℝ) := by
    simp [realTarget_cons,neg_div,Polynomial.C_neg]
    ring
  have hhalf : realTarget [1,0,-1/2] = (1-C (1/2)*X^2 : Polynomial ℝ) := by
    simp [realTarget_cons,neg_div,Polynomial.C_neg]
    ring
  rw [hquarter,hhalf,polynomial]
  simp only [pow_two]

/-- Casting rational Horner evaluation to the reals agrees with evaluation of the represented
real polynomial. -/
theorem nativeEval_semantics (xs : List ℚ) (x : ℚ) :
    ((nativeEval xs x : ℚ):ℝ) = (realTarget xs).eval (x:ℝ) := by
  induction xs with
  | nil => simp [nativeEval]
  | cons a xs ih =>
    simp only [nativeEval,List.foldr_cons,Rat.cast_add,Rat.cast_mul,realTarget_cons,
      Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X]
    rw [show ((xs.foldr (fun a b => a+x*b) 0:ℚ):ℝ) =
      (realTarget xs).eval (x:ℝ) from ih]

/-- The rational primitive list represents `thresholdIntegralPrimitive (polynomial n)`. -/
theorem nativePrimitive_semantics (n : ℕ) :
    realTarget (nativePrimitive n) = thresholdIntegralPrimitive (polynomial n) := by
  simp [nativePrimitive,rationalIntegralCoefficients_semantics,nativeKernel_semantics]

/-- The rational kernel mass casts to the real kernel mass. -/
theorem nativeMass_semantics (n : ℕ) : ((nativeMass n:ℚ):ℝ) = mass n := by
  rw [nativeMass,nativeEval_semantics,nativePrimitive_semantics]
  rfl

/-- The rational kernel mass is strictly positive. -/
theorem nativeMass_pos (n : ℕ) : 0 < nativeMass n := by
  have h := mass_pos n
  rw [← nativeMass_semantics] at h
  exact_mod_cast h

/-- The rational separator coefficients represent the normalized real separator. -/
theorem nativeSeparator_semantics (n : ℕ) : realTarget (nativeSeparator n) = separator n := by
  rw [nativeSeparator,realTarget_div,nativePrimitive_semantics]
  simp only [one_div,Rat.cast_inv,nativeMass_semantics,separator]

/-- Rounds a rational coefficient to a dyadic rational with denominator 2ᵇ using
`dyadicCoefficient`. -/
def nativeRoundedCoefficient (b : ℕ) (a : ℚ) : ℚ :=
  (Qatlib.Concepts.RandCompile.EffectiveInput.dyadicCoefficient b a:ℚ)/(2:ℚ)^b

/-- Rounds each coefficient of a rational list using `nativeRoundedCoefficient b`. -/
def nativeRounded (b : ℕ) (xs : List ℚ) : List ℚ := xs.map (nativeRoundedCoefficient b)

/-- Dyadic rounding of one coefficient changes its real value by at most 2⁻⁽ᵇ⁺¹⁾. -/
theorem nativeRoundedCoefficient_error (b : ℕ) (a : ℚ) :
    |((nativeRoundedCoefficient b a:ℚ):ℝ)-(a:ℝ)| ≤ 1/(2:ℝ)^(b+1) := by
  simpa only [nativeRoundedCoefficient,Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,
    Rat.cast_ofNat] using! Qatlib.Concepts.RandCompile.EffectiveInput.dyadicCoefficient_error b a

/-- On [−2, 2], rounding a coefficient list of length `xs.length` changes its polynomial value
by at most (2^xs.length − 1)/2^(b + 1). -/
theorem nativeRounded_eval_error (b : ℕ) (xs : List ℚ) {x : ℝ} (hx : |x| ≤ 2) :
    |(realTarget (nativeRounded b xs)).eval x-(realTarget xs).eval x| ≤
      ((2:ℝ)^xs.length-1)/(2:ℝ)^(b+1) := by
  induction xs with
  | nil => simp [nativeRounded]
  | cons a xs ih =>
    simp only [nativeRounded,List.map_cons,realTarget_cons,Polynomial.eval_add,
      Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X] at ih ⊢
    have hm := mul_le_mul hx ih (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
    calc
      _ = |(((nativeRoundedCoefficient b a:ℚ):ℝ)-(a:ℝ))+
          x*((realTarget (nativeRounded b xs)).eval x-(realTarget xs).eval x)| := by dsimp only [nativeRounded]; congr 1; ring
      _ ≤ |((nativeRoundedCoefficient b a:ℚ):ℝ)-(a:ℝ)|+
          |x*((realTarget (nativeRounded b xs)).eval x-(realTarget xs).eval x)| := abs_add_le _ _
      _ ≤ 1/(2:ℝ)^(b+1)+2*(((2:ℝ)^xs.length-1)/(2:ℝ)^(b+1)) := by
        rw [abs_mul]
        exact add_le_add (nativeRoundedCoefficient_error b a) hm
      _ = _ := by simp only [List.length_cons,pow_succ]; ring

end Qatlib.Concepts.QsvtCore.ApproxToolkit.Kernel
