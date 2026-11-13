/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.SpecialFuncs.KummerODE.KummerEquation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Kummer-function solution for the inverse schedule

This module constructs `invAmplitude` from a logarithmic phase and a confluent hypergeometric
function, as used in the inverse-schedule analysis of [KadowakiNishimori1998]. It computes first
and second real-time derivatives and applies Kummer's differential equation.

For positive time and nonzero `h`, the amplitude satisfies the displayed second-order equation.
The companion expression `invAmplitudeA` also yields the `b` component of the inverse-schedule
Schrödinger system when `c` is nonzero.

## Main statements

* `kummer_series_relation`: verifies the confluent hypergeometric differential equation.
* `invAmplitude_second_order`: verifies the inverse-schedule second-order amplitude equation.
* `invAmplitude_schrodinger_b`: verifies the `b` component with the companion amplitude.

## References

* [Kadowaki and Nishimori, 1998][KadowakiNishimori1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Complex
open Qatlib.Foundations.SpecialFuncs.KummerODE

namespace Qatlib.Papers.TITCMTReport98.MainResults.KummerSolution

/-- At positive real `t`, the complex logarithm restricted to the real line has derivative `(t :
ℂ)⁻¹`. -/
theorem hasDerivAt_log_real (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Complex.log (s : ℂ)) ((t : ℂ)⁻¹) t := by
  have hlog : HasDerivAt Complex.log ((t : ℂ)⁻¹) (t : ℂ) :=
    Complex.hasDerivAt_log (Complex.ofReal_mem_slitPlane.mpr ht)
  have hof : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t :=
    Complex.ofRealCLM.hasDerivAt
  simpa only [Function.comp_apply, smul_eq_mul, one_mul] using! hlog.scomp t hof

/-- The linear complex argument `-2iht` for the inverse-schedule confluent hypergeometric
function. -/
def invArg (h : ℝ) (t : ℝ) : ℂ := (-2 * Complex.I * (h : ℂ)) * (t : ℂ)

/-- The real-time derivative of `invArg h` is the constant `-2ih`. -/
theorem hasDerivAt_invArg (h t : ℝ) :
    HasDerivAt (invArg h) (-2 * Complex.I * (h : ℂ)) t := by
  have hlin : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
  have := hlin.const_mul (-2 * Complex.I * (h : ℂ))
  simpa only [invArg, Function.comp_apply, smul_eq_mul, mul_one] using! this

/-- Under the stated nonvanishing parameter conditions, the derivative of the confluent
hypergeometric function along `invArg h` is `confHyperDeriv` times `-2ih`. -/
theorem hasDerivAt_invF (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0) (hb : ∀ n : ℕ, b + n ≠ 0)
    (h : ℝ) (t : ℝ) :
    HasDerivAt (fun s => confHyper a b (invArg h s))
      (confHyperDeriv a b (invArg h t) * (-2 * Complex.I * (h : ℂ))) t := by
  have := (hasDerivAt_confHyper a b ha hb (invArg h t)).scomp t (hasDerivAt_invArg h t)
  simpa only [Function.comp_apply, smul_eq_mul, mul_comm] using! this

/-- Under the stated nonvanishing parameter conditions, differentiating the first
time-derivative expression along `invArg h` gives `confHyperSecond` times two factors of
`-2ih`. -/
theorem hasDerivAt_invF_deriv (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0) (hb : ∀ n : ℕ, b + n ≠ 0)
    (h : ℝ) (t : ℝ) :
    HasDerivAt (fun s => confHyperDeriv a b (invArg h s) * (-2 * Complex.I * (h : ℂ)))
      (confHyperSecond a b (invArg h t) * (-2 * Complex.I * (h : ℂ))
        * (-2 * Complex.I * (h : ℂ))) t := by
  have hd := (hasDerivAt_confHyperDeriv a b ha hb (invArg h t)).scomp t (hasDerivAt_invArg h t)
  have h2 := hd.mul_const (-2 * Complex.I * (h : ℂ))
  simpa only [Function.comp_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using h2

/-- The complex phase `exp (i * (h * t + c * Complex.log t))`. -/
def clockPhase (c h : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((h : ℂ) * (t : ℂ) + (c : ℂ) * Complex.log (t : ℂ)))

/-- At positive time, the derivative of the clock-phase exponent is `i * (h + c / t)`. -/
theorem hasDerivAt_clockArg (c h : ℝ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Complex.I * ((h : ℂ) * (s : ℂ) + (c : ℂ) * Complex.log (s : ℂ)))
      (Complex.I * ((h : ℂ) + (c : ℂ) * (t : ℂ)⁻¹)) t := by
  have hlin : HasDerivAt (fun s : ℝ => (h : ℂ) * (s : ℂ)) (h : ℂ) t := by
    have := Complex.ofRealCLM.hasDerivAt (x := t)
    simpa using this.const_mul (h : ℂ)
  have hlog := hasDerivAt_log_real t ht
  have hsum : HasDerivAt
      (fun s : ℝ => (h : ℂ) * (s : ℂ) + (c : ℂ) * Complex.log (s : ℂ))
      ((h : ℂ) + (c : ℂ) * (t : ℂ)⁻¹) t :=
    hlin.add (hlog.const_mul (c : ℂ))
  simpa [mul_add] using hsum.const_mul Complex.I

/-- At positive time, the derivative of `clockPhase c h` equals the phase times `i * (h + c /
t)`. -/
theorem hasDerivAt_clockPhase (c h : ℝ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (clockPhase c h)
      (clockPhase c h t * (Complex.I * ((h : ℂ) + (c : ℂ) * (t : ℂ)⁻¹))) t := by
  have hexp := Complex.hasDerivAt_exp
    (Complex.I * ((h : ℂ) * (t : ℂ) + (c : ℂ) * Complex.log (t : ℂ)))
  have hcomp := hexp.scomp t (hasDerivAt_clockArg c h t ht)
  simpa [clockPhase, mul_comm, mul_assoc, mul_left_comm] using! hcomp

/-- At positive time, the derivative of `i * (h + c / t)` is `-ic / t ^ 2`. -/
theorem hasDerivAt_clockLogDeriv (c h : ℝ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Complex.I * ((h : ℂ) + (c : ℂ) * (s : ℂ)⁻¹))
      (Complex.I * (-(c : ℂ) * ((t : ℂ)⁻¹) ^ 2)) t := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hlin : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
  have hinv : HasDerivAt (fun s : ℝ => ((s : ℂ))⁻¹) (-((t : ℂ)⁻¹) ^ 2) t := by
    have h := (hasDerivAt_inv (x := (t : ℂ)) htC).scomp t hlin
    simpa only [Function.comp_apply, smul_eq_mul, mul_comm, one_mul, ← inv_pow] using! h
  have hsum := (hinv.const_mul (c : ℂ)).const_add (h : ℂ)
  simpa [mul_comm, mul_assoc, mul_left_comm] using hsum.const_mul Complex.I

/-- At positive time, the derivative of the clock-phase derivative expression is the phase times
the sum of the squared logarithmic derivative and `-ic / t ^ 2`. -/
theorem hasDerivAt_clockPhase_deriv (c h : ℝ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => clockPhase c h s * (Complex.I * ((h : ℂ) + (c : ℂ) * (s : ℂ)⁻¹)))
      (clockPhase c h t * ((Complex.I * ((h : ℂ) + (c : ℂ) * (t : ℂ)⁻¹)) ^ 2
        + Complex.I * (-(c : ℂ) * ((t : ℂ)⁻¹) ^ 2))) t := by
  have h1 := hasDerivAt_clockPhase c h t ht
  have h2 := hasDerivAt_clockLogDeriv c h t ht
  have hprod := h1.mul h2
  convert hprod using 1
  ring

/-- The confluent hypergeometric parameter `1 + ic`. -/
def kummerA (c : ℝ) : ℂ := 1 + Complex.I * (c : ℂ)

/-- The confluent hypergeometric parameter `1 + 2ic`. -/
def kummerB (c : ℝ) : ℂ := 1 + 2 * Complex.I * (c : ℂ)

/-- Adding any natural number to `kummerA c` gives a nonzero complex number. -/
theorem kummerA_add_nat_ne_zero (c : ℝ) : ∀ n : ℕ, kummerA c + n ≠ 0 := by
  intro n hn
  have hre := congrArg Complex.re hn
  simp [kummerA] at hre
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- Adding any natural number to `kummerB c` gives a nonzero complex number. -/
theorem kummerB_add_nat_ne_zero (c : ℝ) : ∀ n : ℕ, kummerB c + n ≠ 0 := by
  intro n hn
  have hre := congrArg Complex.re hn
  simp [kummerB] at hre
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The product of `clockPhase c h t` and the confluent hypergeometric function with parameters
`kummerA c`, `kummerB c` at `invArg h t`. -/
def invAmplitude (c h : ℝ) (t : ℝ) : ℂ :=
  clockPhase c h t * confHyper (kummerA c) (kummerB c) (invArg h t)

/-- At positive time, the inverse-schedule amplitude has the displayed product-rule derivative
involving `confHyper` and `confHyperDeriv`. -/
theorem hasDerivAt_invAmplitude (c h : ℝ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (invAmplitude c h)
      (clockPhase c h t * (Complex.I * ((h : ℂ) + (c : ℂ) * (t : ℂ)⁻¹))
          * confHyper (kummerA c) (kummerB c) (invArg h t)
        + clockPhase c h t
          * (confHyperDeriv (kummerA c) (kummerB c) (invArg h t)
              * (-2 * Complex.I * (h : ℂ)))) t := by
  have h1 := hasDerivAt_clockPhase c h t ht
  have h2 := hasDerivAt_invF (kummerA c) (kummerB c) (kummerA_add_nat_ne_zero c)
    (kummerB_add_nat_ne_zero c) h t
  have := h1.mul h2
  simpa [invAmplitude] using! this

/-- At positive time, the first derivative expression for `invAmplitude` has the displayed
second derivative involving the phase and the first two hypergeometric derivatives. -/
theorem hasDerivAt_invAmplitude_deriv (c h : ℝ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (fun s => clockPhase c h s * (Complex.I * ((h : ℂ) + (c : ℂ) * (s : ℂ)⁻¹))
          * confHyper (kummerA c) (kummerB c) (invArg h s)
        + clockPhase c h s
          * (confHyperDeriv (kummerA c) (kummerB c) (invArg h s)
              * (-2 * Complex.I * (h : ℂ))))
      (clockPhase c h t * ((Complex.I * ((h : ℂ) + (c : ℂ) * (t : ℂ)⁻¹)) ^ 2
            + Complex.I * (-(c : ℂ) * ((t : ℂ)⁻¹) ^ 2))
          * confHyper (kummerA c) (kummerB c) (invArg h t)
        + 2 * (clockPhase c h t * (Complex.I * ((h : ℂ) + (c : ℂ) * (t : ℂ)⁻¹)))
          * (confHyperDeriv (kummerA c) (kummerB c) (invArg h t)
              * (-2 * Complex.I * (h : ℂ)))
        + clockPhase c h t
          * (confHyperSecond (kummerA c) (kummerB c) (invArg h t)
              * (-2 * Complex.I * (h : ℂ)) * (-2 * Complex.I * (h : ℂ)))) t := by
  have ha := kummerA_add_nat_ne_zero c
  have hb := kummerB_add_nat_ne_zero c
  have h1 := hasDerivAt_clockPhase_deriv c h t ht
  have h2 := hasDerivAt_invF (kummerA c) (kummerB c) ha hb h t
  have h3 := hasDerivAt_invF_deriv (kummerA c) (kummerB c) ha hb h t
  have hL := hasDerivAt_clockPhase c h t ht
  have hA := h1.mul h2
  have hB := hL.mul h3
  have hsum := hA.add hB
  convert hsum using 1
  ring

/-- Under the stated nonvanishing parameter conditions, `confHyper`, `confHyperDeriv`, and
`confHyperSecond` satisfy Kummer's equation `wF'' + (b - w)F' - aF = 0`
[KadowakiNishimori1998]. -/
theorem kummer_series_relation (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (w : ℂ) :
    w * confHyperSecond a b w + (b - w) * confHyperDeriv a b w - a * confHyper a b w = 0 := by
  have hderiv1 : deriv (confHyper a b) = confHyperDeriv a b := by
    funext z
    exact (hasDerivAt_confHyper a b ha hb z).deriv
  have hderiv2 : deriv (deriv (confHyper a b)) w = confHyperSecond a b w := by
    rw [hderiv1]
    exact (hasDerivAt_confHyperDeriv a b ha hb w).deriv
  have h := kummer_equation a b ha hb w
  rw [hderiv2, hderiv1] at h
  exact h

/-- The inverse-schedule argument is nonzero when `h` is nonzero and time is positive. -/
theorem invArg_ne_zero (h : ℝ) (hh0 : h ≠ 0) (t : ℝ) (ht : 0 < t) :
    invArg h t ≠ 0 := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh0
  have h2 : (-2 : ℂ) ≠ 0 := by norm_num
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  simp only [invArg]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hI) hhC) htC

/-- At positive time, gives the second derivative of `invAmplitude` as the sum of phase, mixed,
and second hypergeometric derivative terms. -/
theorem deriv_deriv_invAmplitude (c h : ℝ) (t : ℝ) (ht : 0 < t) :
    deriv (deriv (invAmplitude c h)) t
      = (clockPhase c h t * ((Complex.I * ((h : ℂ) + (c : ℂ) * (t : ℂ)⁻¹)) ^ 2
            + Complex.I * (-(c : ℂ) * ((t : ℂ)⁻¹) ^ 2))
          * confHyper (kummerA c) (kummerB c) (invArg h t)
        + 2 * (clockPhase c h t * (Complex.I * ((h : ℂ) + (c : ℂ) * (t : ℂ)⁻¹)))
          * (confHyperDeriv (kummerA c) (kummerB c) (invArg h t)
              * (-2 * Complex.I * (h : ℂ)))
        + clockPhase c h t
          * (confHyperSecond (kummerA c) (kummerB c) (invArg h t)
              * (-2 * Complex.I * (h : ℂ)) * (-2 * Complex.I * (h : ℂ)))) := by
  have hloc : deriv (invAmplitude c h)
      =ᶠ[nhds t] fun s => clockPhase c h s * (Complex.I * ((h : ℂ) + (c : ℂ) * (s : ℂ)⁻¹))
          * confHyper (kummerA c) (kummerB c) (invArg h s)
        + clockPhase c h s
          * (confHyperDeriv (kummerA c) (kummerB c) (invArg h s)
              * (-2 * Complex.I * (h : ℂ))) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (hasDerivAt_invAmplitude c h s hs).deriv
  rw [hloc.deriv_eq]
  exact (hasDerivAt_invAmplitude_deriv c h t ht).deriv

/-- At positive time, evaluates `deriv (invAmplitude c h)` by the product and chain rules. -/
theorem deriv_invAmplitude (c h : ℝ) (t : ℝ) (ht : 0 < t) :
    deriv (invAmplitude c h) t
      = (clockPhase c h t * (Complex.I * ((h : ℂ) + (c : ℂ) * (t : ℂ)⁻¹))
          * confHyper (kummerA c) (kummerB c) (invArg h t)
        + clockPhase c h t
          * (confHyperDeriv (kummerA c) (kummerB c) (invArg h t)
              * (-2 * Complex.I * (h : ℂ)))) :=
  (hasDerivAt_invAmplitude c h t ht).deriv

/-- For nonzero `h` and positive time, `invAmplitude` satisfies `b'' + b' / t + (h ^ 2 + c ^ 2 /
t ^ 2 + ih / t) * b = 0` [KadowakiNishimori1998]. -/
theorem invAmplitude_second_order (c h : ℝ) (hh0 : h ≠ 0) (t : ℝ) (ht : 0 < t) :
    deriv (deriv (invAmplitude c h)) t
      + (t : ℂ)⁻¹ * deriv (invAmplitude c h) t
      + ((h : ℂ) ^ 2 + (c : ℂ) ^ 2 * ((t : ℂ)⁻¹) ^ 2
          + Complex.I * (h : ℂ) * (t : ℂ)⁻¹) * invAmplitude c h t = 0 := by
  have ha := kummerA_add_nat_ne_zero c
  have hb := kummerB_add_nat_ne_zero c
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hw := invArg_ne_zero h hh0 t ht
  have hφ : clockPhase c h t ≠ 0 := Complex.exp_ne_zero _
  have hkm := kummer_series_relation (kummerA c) (kummerB c) ha hb (invArg h t)
  have hSecond : confHyperSecond (kummerA c) (kummerB c) (invArg h t)
      = (kummerA c * confHyper (kummerA c) (kummerB c) (invArg h t)
          - (kummerB c - invArg h t)
            * confHyperDeriv (kummerA c) (kummerB c) (invArg h t)) / invArg h t := by
    rw [eq_div_iff hw]
    linear_combination hkm
  have hdiv : (deriv (deriv (invAmplitude c h)) t
      + (t : ℂ)⁻¹ * deriv (invAmplitude c h) t
      + ((h : ℂ) ^ 2 + (c : ℂ) ^ 2 * ((t : ℂ)⁻¹) ^ 2
          + Complex.I * (h : ℂ) * (t : ℂ)⁻¹) * invAmplitude c h t)
      / clockPhase c h t = 0 := by
    rw [deriv_deriv_invAmplitude c h t ht, deriv_invAmplitude c h t ht]
    simp only [invAmplitude]
    rw [hSecond]
    simp only [invArg, kummerA, kummerB] at hkm ⊢
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [div_eq_zero_iff] at hdiv
  exact hdiv.resolve_right hφ

/-- The companion amplitude `(h * invAmplitude - i * deriv invAmplitude) / (c / t)`. -/
def invAmplitudeA (c h : ℝ) (t : ℝ) : ℂ :=
  ((h : ℂ) * invAmplitude c h t - Complex.I * deriv (invAmplitude c h) t)
    / ((c : ℂ) / (t : ℂ))

/-- For nonzero `c` and positive time, the inverse-schedule amplitudes satisfy `i * b' = -(c /
t) * a + h * b` [KadowakiNishimori1998]. -/
theorem invAmplitude_schrodinger_b (c h : ℝ) (hc : c ≠ 0) (t : ℝ) (ht : 0 < t) :
    Complex.I * deriv (invAmplitude c h) t
      = -((c : ℂ) / (t : ℂ)) * invAmplitudeA c h t + (h : ℂ) * invAmplitude c h t := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hG : (c : ℂ) / (t : ℂ) ≠ 0 := div_ne_zero hcC htC
  unfold invAmplitudeA
  field_simp
  ring

end Qatlib.Papers.TITCMTReport98.MainResults.KummerSolution
