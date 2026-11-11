/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option backward.isDefEq.respectTransparency false

/-!
# Liouvillian propagators and the backward-evolution norm bound

Kliesch--Barthel--Gogolin--Kastoryano--Eisert,
"A dissipative quantum Church-Turing theorem", fixed arXiv:1105.3986v4.

This module formalizes the propagator interface of Eq. (5)--(6) and Lemma 4 of the
appendix.  The Liouvillian `L r` is represented as a matrix superoperator acting on
the (vectorized) operator space, and `propagator L s t` is the time-ordered
exponential solving `d/dt T(t,s) = L t * T(t,s)` with `T(s,s) = 1`.

The paper's `(1 -> 1)` superoperator norm is the induced trace norm; the estimates
below are proved for the operator (L2) norm of the same matrix superoperator.  This
is the submultiplicative norm used by the analytic estimates, but it is not claimed
to coincide with the induced trace norm.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DissipCTT11.MainResults.LiouvillianPropagator

open Matrix
open scoped Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The propagator of the time-dependent Liouvillian `L`, defined as the
time-ordered exponential solving `d/dt T(t,s) = L t * T(t,s)` and `T(s,s) = 1`. -/
noncomputable def propagator (L : ℝ → Matrix I I ℂ) (s t : ℝ) : Matrix I I ℂ :=
  Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution (fun r => -L r) s t

/-- The propagator vanishes to the identity at equal times, `T(s,s) = 1`. -/
@[simp] theorem propagator_self (L : ℝ → Matrix I I ℂ) (s : ℝ) :
    propagator L s s = 1 := by
  simp [propagator]

/-- The propagator solves the Liouvillian initial value problem `d/dt T = L t * T`. -/
theorem propagator_hasDerivAt (L : ℝ → Matrix I I ℂ) (hL : Continuous L) (s t : ℝ) :
    HasDerivAt (propagator L s) (L t * propagator L s t) t := by
  have h := Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution_hasDerivAt
    (fun r => -L r) hL.neg s t
  unfold propagator
  simpa only [neg_mul, neg_neg] using h

/-- Propagators compose, `T(b,c) * T(a,b) = T(a,c)`, for any intermediate time. -/
theorem propagator_cocycle (L : ℝ → Matrix I I ℂ) (hL : Continuous L) (a b c : ℝ) :
    propagator L b c * propagator L a b = propagator L a c :=
  Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution_cocycle
    (fun r => -L r) hL.neg a b c

/-- Lemma 4(i): the propagator is invertible and its inverse is the backward
propagator obtained by exchanging the time arguments. -/
theorem propagator_ringInverse (L : ℝ → Matrix I I ℂ) (hL : Continuous L) (s t : ℝ) :
    Ring.inverse (propagator L s t) = propagator L t s :=
  Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution_ringInverse
    (fun r => -L r) hL.neg s t

/-! ## Dyson-series bounds with the time integral of the generator norm -/

/-- Scalar identity for the forward Dyson bound: integrating the generator norm
weighted by the `n`-th power of the accumulated norm gives the `(n+1)`-st power,
up to the factorial denominator. -/
theorem integral_norm_mul_cum_pow_div (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    {s t : ℝ} (_hst : s ≤ t) (n : ℕ) :
    (∫ u in s..t, ‖A u‖ * (∫ v in s..u, ‖A v‖) ^ n / (n.factorial : ℝ)) =
      (∫ u in s..t, ‖A u‖) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hcont : Continuous fun u => ‖A u‖ := hA.norm
  have hprim : Continuous fun u => ∫ v in s..u, ‖A v‖ :=
    intervalIntegral.continuous_primitive (fun a b => hcont.intervalIntegrable a b) s
  have hJ : ∀ u, HasDerivAt (fun u => ∫ v in s..u, ‖A v‖) (‖A u‖) u := by
    intro u
    exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable s u)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hder : ∀ u ∈ Set.uIcc s t,
      HasDerivAt (fun u => (∫ v in s..u, ‖A v‖) ^ (n + 1) / ((n + 1).factorial : ℝ))
        (‖A u‖ * (∫ v in s..u, ‖A v‖) ^ n / (n.factorial : ℝ)) u := by
    intro u _
    have h := ((hJ u).pow (n + 1)).div_const ((n + 1).factorial : ℝ)
    refine h.congr_deriv ?_
    have hfac : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [hfac]
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hpow : n + 1 - 1 = n := Nat.add_sub_cancel n 1
    rw [hpow]
    push_cast
    field_simp
  have hint : IntervalIntegrable
      (fun u => ‖A u‖ * (∫ v in s..u, ‖A v‖) ^ n / (n.factorial : ℝ)) MeasureTheory.volume
        s t := by
    exact (((hcont.mul (hprim.pow n)).div_const _)).intervalIntegrable s t
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  have hs : (∫ v in s..s, ‖A v‖) = 0 := by simp
  rw [hs] at h
  simpa using h

/-- Scalar identity for the reverse Dyson bound: integrating the generator norm
weighted by the `n`-th power of the remaining norm also gives the `(n+1)`-st power,
up to the factorial denominator. -/
theorem integral_norm_mul_tail_pow_div (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    {s t : ℝ} (_hst : s ≤ t) (n : ℕ) :
    (∫ u in s..t, ‖A u‖ * (∫ v in u..t, ‖A v‖) ^ n / (n.factorial : ℝ)) =
      (∫ u in s..t, ‖A u‖) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hcont : Continuous fun u => ‖A u‖ := hA.norm
  have hprim' : Continuous fun u => ∫ v in t..u, ‖A v‖ :=
    intervalIntegral.continuous_primitive (fun a b => hcont.intervalIntegrable a b) t
  have hprim : Continuous fun u => ∫ v in u..t, ‖A v‖ := by
    have hfun : (fun u => ∫ v in u..t, ‖A v‖) = fun u => -(∫ v in t..u, ‖A v‖) := by
      funext u
      exact intervalIntegral.integral_symm t u
    rw [hfun]
    exact hprim'.neg
  have hJ : ∀ u, HasDerivAt (fun u => ∫ v in u..t, ‖A v‖) (-‖A u‖) u := by
    intro u
    exact intervalIntegral.integral_hasDerivAt_left (hcont.intervalIntegrable u t)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hder : ∀ u ∈ Set.uIcc s t,
      HasDerivAt (fun u => (∫ v in u..t, ‖A v‖) ^ (n + 1) / ((n + 1).factorial : ℝ))
        (-(‖A u‖ * (∫ v in u..t, ‖A v‖) ^ n / (n.factorial : ℝ))) u := by
    intro u _
    have h := ((hJ u).pow (n + 1)).div_const ((n + 1).factorial : ℝ)
    refine h.congr_deriv ?_
    have hfac : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [hfac]
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hpow : n + 1 - 1 = n := Nat.add_sub_cancel n 1
    rw [hpow]
    push_cast
    field_simp
  have hint : IntervalIntegrable
      (fun u => ‖A u‖ * (∫ v in u..t, ‖A v‖) ^ n / (n.factorial : ℝ)) MeasureTheory.volume
        s t := by
    exact (((hcont.mul (hprim.pow n)).div_const _)).intervalIntegrable s t
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint.neg
  rw [intervalIntegral.integral_neg] at h
  have ht : (∫ v in t..t, ‖A v‖) = 0 := by simp
  have h' : -(∫ u in s..t, ‖A u‖ * (∫ v in u..t, ‖A v‖) ^ n / (n.factorial : ℝ)) =
      0 - (∫ v in s..t, ‖A v‖) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
    simpa [ht] using h
  linarith

/-- Forward Dyson term bound: the `n`-th iterated integral is bounded by the
`n`-th power of the accumulated generator norm divided by `n!`. -/
theorem norm_orderedDysonTerm_forward_le (A : ℝ → Matrix I I ℂ) (hA : Continuous A) :
    ∀ (n : ℕ) {s t : ℝ}, s ≤ t →
      ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm A s n t‖ ≤
        (∫ u in s..t, ‖A u‖) ^ n / (n.factorial : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro s t _
      simpa [Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm] using
        (Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_one_le (I := I))
  | succ n ih =>
      intro s t hst
      have hcont : Continuous fun u => ‖A u‖ := hA.norm
      have hprim : Continuous fun u => ∫ v in s..u, ‖A v‖ :=
        intervalIntegral.continuous_primitive (fun a b => hcont.intervalIntegrable a b) s
      have hterm : IntervalIntegrable
          (fun u => ‖A u * Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
            A s n u‖) MeasureTheory.volume s t := by
        have hc : Continuous
            (fun u => A u * Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
              A s n u) :=
          hA.mul (Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm_continuous
            A hA s n)
        exact hc.norm.intervalIntegrable s t
      have hrhs : IntervalIntegrable
          (fun u => ‖A u‖ * (∫ v in s..u, ‖A v‖) ^ n / (n.factorial : ℝ)) MeasureTheory.volume
            s t :=
        (((hcont.mul (hprim.pow n)).div_const _)).intervalIntegrable s t
      calc ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm A s (n + 1) t‖
          = ‖∫ u in s..t,
              -(A u * Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
                A s n u)‖ := by
            rw [Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm]
        _ = ‖∫ u in s..t,
              A u * Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
                A s n u‖ := by
            rw [intervalIntegral.integral_neg, norm_neg]
        _ ≤ ∫ u in s..t,
              ‖A u * Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
                A s n u‖ :=
            intervalIntegral.norm_integral_le_integral_norm hst
        _ ≤ ∫ u in s..t, ‖A u‖ * (∫ v in s..u, ‖A v‖) ^ n / (n.factorial : ℝ) := by
            apply intervalIntegral.integral_mono_on hst hterm hrhs
            intro u hu
            have hu' : s ≤ u := hu.1
            have hb := ih hu'
            have hmul : ‖A u * Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
                A s n u‖ ≤
                ‖A u‖ * ((∫ v in s..u, ‖A v‖) ^ n / (n.factorial : ℝ)) :=
              (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
            calc ‖A u * Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
                  A s n u‖ ≤ ‖A u‖ * ((∫ v in s..u, ‖A v‖) ^ n / (n.factorial : ℝ)) := hmul
              _ = ‖A u‖ * (∫ v in s..u, ‖A v‖) ^ n / (n.factorial : ℝ) := by ring
        _ = (∫ u in s..t, ‖A u‖) ^ (n + 1) / ((n + 1).factorial : ℝ) :=
            integral_norm_mul_cum_pow_div A hA hst n

/-- Reverse Dyson term bound: the iterated integrals taken from `t` down to `s`
are bounded by the same power of the accumulated generator norm. -/
theorem norm_orderedDysonTerm_reverse_le (A : ℝ → Matrix I I ℂ) (hA : Continuous A) :
    ∀ (n : ℕ) {s t : ℝ}, s ≤ t →
      ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm A t n s‖ ≤
        (∫ u in s..t, ‖A u‖) ^ n / (n.factorial : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro s t _
      simpa [Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm] using
        (Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_one_le (I := I))
  | succ n ih =>
      intro s t hst
      have hcont : Continuous fun u => ‖A u‖ := hA.norm
      have hprim' : Continuous fun u => ∫ v in t..u, ‖A v‖ :=
        intervalIntegral.continuous_primitive (fun a b => hcont.intervalIntegrable a b) t
      have hprim : Continuous fun u => ∫ v in u..t, ‖A v‖ := by
        have hfun : (fun u => ∫ v in u..t, ‖A v‖) = fun u => -(∫ v in t..u, ‖A v‖) := by
          funext u
          exact intervalIntegral.integral_symm t u
        rw [hfun]
        exact hprim'.neg
      have hterm : IntervalIntegrable
          (fun u => ‖A u * Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
            A t n u‖) MeasureTheory.volume s t := by
        have hc : Continuous
            (fun u => A u * Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
              A t n u) :=
          hA.mul (Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm_continuous
            A hA t n)
        exact hc.norm.intervalIntegrable s t
      have hrhs : IntervalIntegrable
          (fun u => ‖A u‖ * (∫ v in u..t, ‖A v‖) ^ n / (n.factorial : ℝ)) MeasureTheory.volume
            s t :=
        (((hcont.mul (hprim.pow n)).div_const _)).intervalIntegrable s t
      calc ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm A t (n + 1) s‖
          = ‖∫ u in t..s,
              -(A u * Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
                A t n u)‖ := by
            rw [Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm]
        _ = ‖∫ u in s..t,
              A u * Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
                A t n u‖ := by
            rw [intervalIntegral.integral_symm, intervalIntegral.integral_neg, neg_neg]
        _ ≤ ∫ u in s..t,
              ‖A u * Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
                A t n u‖ :=
            intervalIntegral.norm_integral_le_integral_norm hst
        _ ≤ ∫ u in s..t, ‖A u‖ * (∫ v in u..t, ‖A v‖) ^ n / (n.factorial : ℝ) := by
            apply intervalIntegral.integral_mono_on hst hterm hrhs
            intro u hu
            have hu' : u ≤ t := hu.2
            have hb := ih hu'
            have hmul : ‖A u * Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
                A t n u‖ ≤
                ‖A u‖ * ((∫ v in u..t, ‖A v‖) ^ n / (n.factorial : ℝ)) :=
              (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
            calc ‖A u * Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
                  A t n u‖ ≤ ‖A u‖ * ((∫ v in u..t, ‖A v‖) ^ n / (n.factorial : ℝ)) := hmul
              _ = ‖A u‖ * (∫ v in u..t, ‖A v‖) ^ n / (n.factorial : ℝ) := by ring
        _ = (∫ u in s..t, ‖A u‖) ^ (n + 1) / ((n + 1).factorial : ℝ) :=
            integral_norm_mul_tail_pow_div A hA hst n

/-- The forward propagator is bounded by the exponential of the time integral of
the generator norm. -/
theorem norm_orderedEvolution_le (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    {s t : ℝ} (hst : s ≤ t) :
    ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution A s t‖ ≤
      Real.exp (∫ u in s..t, ‖A u‖) := by
  let I : ℝ := ∫ u in s..t, ‖A u‖
  have hterm : ∀ n : ℕ,
      ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm A s n t‖ ≤
        I ^ n / (n.factorial : ℝ) :=
    fun n => norm_orderedDysonTerm_forward_le A hA n hst
  have hsum : Summable
      (fun n : ℕ => ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
        A s n t‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm
      (Real.summable_pow_div_factorial I)
  have hseries : Summable (fun n : ℕ => I ^ n / (n.factorial : ℝ)) :=
    Real.summable_pow_div_factorial I
  calc ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution A s t‖
      = ‖∑' n : ℕ,
          Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm A s n t‖ := by
        rw [Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution]
    _ ≤ ∑' n : ℕ,
          ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm A s n t‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, I ^ n / (n.factorial : ℝ) :=
        Summable.tsum_le_tsum hterm hsum hseries
    _ = Real.exp I := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- The reverse propagator is bounded by the exponential of the same time integral
of the generator norm. -/
theorem norm_orderedEvolution_reverse_le (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    {s t : ℝ} (hst : s ≤ t) :
    ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution A t s‖ ≤
      Real.exp (∫ u in s..t, ‖A u‖) := by
  let I : ℝ := ∫ u in s..t, ‖A u‖
  have hterm : ∀ n : ℕ,
      ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm A t n s‖ ≤
        I ^ n / (n.factorial : ℝ) :=
    fun n => norm_orderedDysonTerm_reverse_le A hA n hst
  have hsum : Summable
      (fun n : ℕ => ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
        A t n s‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm
      (Real.summable_pow_div_factorial I)
  have hseries : Summable (fun n : ℕ => I ^ n / (n.factorial : ℝ)) :=
    Real.summable_pow_div_factorial I
  calc ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution A t s‖
      = ‖∑' n : ℕ,
          Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm A t n s‖ := by
        rw [Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution]
    _ ≤ ∑' n : ℕ,
          ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm A t n s‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, I ^ n / (n.factorial : ℝ) :=
        Summable.tsum_le_tsum hterm hsum hseries
    _ = Real.exp I := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- The forward Liouvillian propagator obeys the exponential norm bound. -/
theorem propagator_norm_le (L : ℝ → Matrix I I ℂ) (hL : Continuous L)
    {s t : ℝ} (hst : s ≤ t) :
    ‖propagator L s t‖ ≤ Real.exp (∫ u in s..t, ‖L u‖) := by
  have h := norm_orderedEvolution_le (fun r => -L r) hL.neg hst
  have hnorm : (∫ u in s..t, ‖-L u‖) = ∫ u in s..t, ‖L u‖ := by
    congr 1 with u
    exact norm_neg (L u)
  simpa [propagator, hnorm] using h

/-- Lemma 4(ii): the backward propagator obeys
`‖T^-(t,s)‖ ≤ exp (∫_s^t ‖L_r‖ dr)` for `t ≥ s`. -/
theorem propagator_backward_norm_le (L : ℝ → Matrix I I ℂ) (hL : Continuous L)
    {s t : ℝ} (hst : s ≤ t) :
    ‖propagator L t s‖ ≤ Real.exp (∫ u in s..t, ‖L u‖) := by
  have h := norm_orderedEvolution_reverse_le (fun r => -L r) hL.neg hst
  have hnorm : (∫ u in s..t, ‖-L u‖) = ∫ u in s..t, ‖L u‖ := by
    congr 1 with u
    exact norm_neg (L u)
  simpa [propagator, hnorm] using h

end Qatlib.Papers.DissipCTT11.MainResults.LiouvillianPropagator
