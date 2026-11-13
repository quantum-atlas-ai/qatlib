/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lemma9ChebyshevWordStat
import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitWordTransportGily

/-!
# Chebyshev polynomials from reflection words

This module proves that the reflection word determined by `chebyshevAngles d` has upper-left
entry `T_d(x)` on the unit interval, as in [GilyenSuLowWiebe2019]. The proof computes the
response polynomials for repeated phases equal to `i` and transports the result to the
single-qubit reflection word.

## Main statements

* `repeated_half_pi`: the response pair in terms of first- and second-kind Chebyshev
  polynomials.
* `lemma9ChebyshevWord`: the reflection-word realization of `T_d`.

## References

* [Gilyén et al., Lemma 9][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.QsvtCore.QsVtMain

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial Polynomial.Chebyshev Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

/-- Angle phases turn addition of real angles into multiplication. -/
private theorem angle_add (a b : ℝ) : anglePhase (a + b) = anglePhase a * anglePhase b := by
  apply Complex.ext <;>
    simp [anglePhase, Real.cos_add, Real.sin_add, Complex.mul_re, Complex.mul_im, add_comm]

/-- The phase at angle `-n * π/2` is `(-i)^n`. -/
private theorem angle_negative_half_pi (n : ℕ) :
    anglePhase (-(n : ℝ) * (Real.pi / 2)) = (-Complex.I) ^ n := by
  induction n with
  | zero => apply Complex.ext <;> simp [anglePhase]
  | succ n ih =>
    have he : -((n + 1 : ℕ) : ℝ) * (Real.pi / 2) =
        -(n : ℝ) * (Real.pi / 2) + -(Real.pi / 2) := by push_cast; ring
    rw [he, angle_add, ih, pow_succ]
    congr 1
    apply Complex.ext <;> simp [anglePhase]

/-- A list of `n` phases equal to `i` gives response polynomials `i^n * T_n` and `-i^n *
U_(n-1)`. -/
private theorem repeated_half_pi (n : ℕ) :
    responseP 1 (List.replicate n Complex.I) = C (Complex.I ^ n) * T ℂ (n : ℤ) ∧
    responseQ 1 (List.replicate n Complex.I) = -C (Complex.I ^ n) * U ℂ ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht : T ℂ ((n : ℤ) + 1) = X * T ℂ (n : ℤ) -
        (1 - X ^ 2) * U ℂ ((n : ℤ) - 1) := by
      have h := T_eq_X_mul_T_sub_pol_U ℂ ((n : ℤ) - 1)
      rw [show (n : ℤ) - 1 + 2 = (n : ℤ) + 1 by omega,
        show (n : ℤ) - 1 + 1 = (n : ℤ) by omega] at h
      exact h
    have hu : U ℂ (n : ℤ) = T ℂ (n : ℤ) + X * U ℂ ((n : ℤ) - 1) := by
      rw [T_eq_U_sub_X_mul_U]
      ring
    simp only [List.replicate_succ, responseP_cons, responseQ_cons, ih.1, ih.2,
      Nat.cast_add, Nat.cast_one, pow_succ, map_mul, Complex.star_def, Complex.conj_I]
    constructor
    · rw [ht]
      ring
    · rw [show (n : ℤ) + 1 - 1 = n by omega, hu]
      simp only [map_neg]
      ring

/-- The reflection word with `chebyshevAngles d` has `(0, 0)` entry equal to the real Chebyshev
polynomial `T_d` on `[-1, 1]`. See [Gilyén et al., Lemma 9][GilyenSuLowWiebe2019]. -/
theorem lemma9ChebyshevWord : Lemma9ChebyshevWord := by
  intro d x hx
  rw [(singleQubitWordTransport (chebyshevAngles d) x hx).1]
  have hi : anglePhase (Real.pi / 2) = Complex.I := by
    apply Complex.ext <;> simp [anglePhase]
  have hpoly : sourcePhaseResponse (chebyshevAngles d) = T ℂ (d : ℤ) := by
    cases d with
    | zero => simp [chebyshevAngles, sourcePhaseResponse]
    | succ n =>
      have hfirst : (1 - ((n + 1 : ℕ) : ℝ)) * (Real.pi / 2) =
          -(n : ℝ) * (Real.pi / 2) := by push_cast; ring
      simp only [sourcePhaseResponse, chebyshevAngles, List.map_cons,
        List.map_replicate, hfirst, angle_negative_half_pi, hi, responseP_cons]
      rw [(repeated_half_pi n).1, (repeated_half_pi n).2]
      have ht := T_eq_X_mul_T_sub_pol_U ℂ ((n : ℤ) - 1)
      rw [show (n : ℤ) - 1 + 2 = (n : ℤ) + 1 by omega,
        show (n : ℤ) - 1 + 1 = (n : ℤ) by omega] at ht
      have hcancel : (-Complex.I) ^ n * Complex.I ^ n = 1 := by
        rw [← mul_pow]
        simp
      calc
        _ = C ((-Complex.I) ^ n * Complex.I ^ n) *
            (X * T ℂ (n : ℤ) - (1 - X ^ 2) * U ℂ ((n : ℤ) - 1)) := by rw [map_mul]; ring
        _ = T ℂ ((n + 1 : ℕ) : ℤ) := by
          rw [hcancel]
          simpa only [C_1, one_mul, Nat.cast_add, Nat.cast_one] using ht.symm
  rw [hpoly, ← map_T Complex.ofRealHom]
  exact eval_map_apply Complex.ofRealHom x

end Qatlib.Concepts.QsvtCore.PhaseExistence
