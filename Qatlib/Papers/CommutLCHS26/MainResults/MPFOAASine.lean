/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.Amplification

/-!
# Sine response of odd amplification sequences

This module computes the two-step recurrence for the response polynomials with repeated phase i
and proves the resulting odd-angle sine and cosine identities. These identities determine the
exact amplification response used for the multi-product encodings associated with
[AftabAnTrivisa2026].

## Main statements

* `response_two`: gives the simultaneous two-phase recurrence.
* `sine_response`: evaluates an odd-length phase sequence at sin θ.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFOAASine

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

/-- Prepending two phases i gives the stated coupled recurrence for the P and Q response
polynomials. -/
theorem response_two (zs : List ℂ) (x : ℂ) :
    (responseP (-Complex.I) (Complex.I :: Complex.I :: zs)).eval x =
      (1 - 2 * x ^ 2) * (responseP (-Complex.I) zs).eval x -
        2 * x * (1 - x ^ 2) * (responseQ (-Complex.I) zs).eval x ∧
    (responseQ (-Complex.I) (Complex.I :: Complex.I :: zs)).eval x =
      2 * x * (responseP (-Complex.I) zs).eval x +
        (1 - 2 * x ^ 2) * (responseQ (-Complex.I) zs).eval x := by
  simp only [responseP_cons, responseQ_cons, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_pow, Complex.star_def, Complex.conj_I]
  constructor <;> ring_nf <;> norm_num [Complex.I_sq] <;> ring

/-- At sin θ, the response P for 2n + 1 phases i equals sin((2n + 1)θ), while cos θ times the
response Q equals -cos((2n + 1)θ). -/
theorem sine_response (n : ℕ) (θ : ℝ) :
    (responseP (-Complex.I) (List.replicate (2 * n + 1) Complex.I)).eval (Real.sin θ : ℂ) =
      (Real.sin (((2 * n + 1 : ℕ) : ℝ) * θ) : ℂ) ∧
    (Real.cos θ : ℂ) *
      (responseQ (-Complex.I) (List.replicate (2 * n + 1) Complex.I)).eval (Real.sin θ : ℂ) =
        -(Real.cos (((2 * n + 1 : ℕ) : ℝ) * θ) : ℂ) := by
  induction n with
  | zero =>
    norm_num [responseP_cons, responseQ_cons]
    ring_nf
    norm_num [Complex.I_sq]
  | succ n ih =>
    have hr : List.replicate (2 * (n + 1) + 1) Complex.I =
        Complex.I :: Complex.I :: List.replicate (2 * n + 1) Complex.I := by
      rw [show 2 * (n + 1) + 1 = 2 + (2 * n + 1) by omega, List.replicate_add]
      rfl
    have ha : (((2 * (n + 1) + 1 : ℕ) : ℝ) * θ) =
        (((2 * n + 1 : ℕ) : ℝ) * θ) + 2 * θ := by push_cast; ring
    have hs : Real.sin (((2 * (n + 1) + 1 : ℕ) : ℝ) * θ) =
        (1 - 2 * Real.sin θ ^ 2) * Real.sin (((2 * n + 1 : ℕ) : ℝ) * θ) +
          2 * Real.sin θ * Real.cos θ * Real.cos (((2 * n + 1 : ℕ) : ℝ) * θ) := by
      rw [ha, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul_eq_one_sub]
      ring
    have hc : Real.cos (((2 * (n + 1) + 1 : ℕ) : ℝ) * θ) =
        (1 - 2 * Real.sin θ ^ 2) * Real.cos (((2 * n + 1 : ℕ) : ℝ) * θ) -
          2 * Real.sin θ * Real.cos θ * Real.sin (((2 * n + 1 : ℕ) : ℝ) * θ) := by
      rw [ha, Real.cos_add, Real.sin_two_mul, Real.cos_two_mul_eq_one_sub]
      ring
    have hc2 : (Real.cos θ : ℂ) ^ 2 = 1 - (Real.sin θ : ℂ) ^ 2 := by
      have h : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
      exact_mod_cast h
    have hrec := response_two (List.replicate (2 * n + 1) Complex.I) (Real.sin θ : ℂ)
    rw [hr]
    constructor
    · calc
        _ = (1 - 2 * (Real.sin θ : ℂ) ^ 2) *
              (responseP (-Complex.I) (List.replicate (2 * n + 1) Complex.I)).eval (Real.sin θ : ℂ) -
            2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ) * ((Real.cos θ : ℂ) *
              (responseQ (-Complex.I) (List.replicate (2 * n + 1) Complex.I)).eval (Real.sin θ : ℂ)) := by
          rw [hrec.1, ← hc2]
          ring
        _ = _ := by rw [ih.1, ih.2, hs]; push_cast; ring
    · calc
        _ = 2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ) *
              (responseP (-Complex.I) (List.replicate (2 * n + 1) Complex.I)).eval (Real.sin θ : ℂ) +
            (1 - 2 * (Real.sin θ : ℂ) ^ 2) * ((Real.cos θ : ℂ) *
              (responseQ (-Complex.I) (List.replicate (2 * n + 1) Complex.I)).eval (Real.sin θ : ℂ)) := by
          rw [hrec.2]
          ring
        _ = _ := by rw [ih.1, ih.2, hc]; push_cast; ring

end Qatlib.Papers.CommutLCHS26.MainResults.MPFOAASine
