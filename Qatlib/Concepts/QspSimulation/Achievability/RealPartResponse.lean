/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.Eval.SMul
import Qatlib.Concepts.QspSimulation.Achievability.ResponseFactorization

/-!
# Conjugation and real parts of QSP responses

Conjugating the base phase and every phase in a list conjugates the coefficients of both QSP
response polynomials. The polynomial `realPartPolynomial` averages a polynomial with its
coefficient conjugate, so its coefficients are real parts and its evaluation at a real argument
is the real part of the original evaluation. The identity `realPartPolynomial_responseP`
expresses this operation as an average of two phase responses, within the QSP setting of
[LowChuang2017].

The normalization results record constraints on the full complex response: its value at one has
norm one, and its value at zero also has norm one for even phase-list length. The endpoint
estimate `responseP_endpoint_error_lower` bounds the distance from the response at one to an
arbitrary complex target.

## Main statements

* `response_conjugate` identifies the two responses produced by conjugated phase data.
* `realPartPolynomial_eval` identifies real-argument evaluation with the real part of the
  original value.
* `realPartPolynomial_responseP` rewrites the real-part response as a two-response average.
* `responseP_norm_one` and `responseP_norm_zero_of_even` give unit-norm response values.
* `responseP_endpoint_error_lower` gives the endpoint approximation lower bound.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.QspSimulation.Achievability

open Polynomial

/-- Complex conjugation preserves the phase condition. -/
theorem IsPhase.conjugate {z : ℂ} (hz : IsPhase z) : IsPhase (star z) := by
  simpa only [IsPhase, star_star, mul_comm] using hz

/-- Conjugating every entry of a list of phases produces another list of phases. -/
theorem phases_conjugate (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    ∀ z ∈ zs.map star, IsPhase z := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
  exact IsPhase.conjugate (hzs w hw)

/-- Conjugating the base and every phase parameter conjugates the coefficients of both response
polynomials. -/
theorem response_conjugate (base : ℂ) (zs : List ℂ) :
    responseP (star base) (zs.map star) = (responseP base zs).map (starRingEnd ℂ) ∧
    responseQ (star base) (zs.map star) = (responseQ base zs).map (starRingEnd ℂ) := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    simp only [List.map_cons, responseP_cons, responseQ_cons]
    rw [ih.1, ih.2]
    simp

/-- Each coefficient of the first response for conjugated phase data is the conjugate of the
corresponding original coefficient. -/
theorem responseP_conjugate_coeff (base : ℂ) (zs : List ℂ) (n : ℕ) :
    (responseP (star base) (zs.map star)).coeff n = star ((responseP base zs).coeff n) := by
  rw [(response_conjugate base zs).1]
  simp

/-- Each coefficient of the second response for conjugated phase data is the conjugate of the
corresponding original coefficient. -/
theorem responseQ_conjugate_coeff (base : ℂ) (zs : List ℂ) (n : ℕ) :
    (responseQ (star base) (zs.map star)).coeff n = star ((responseQ base zs).coeff n) := by
  rw [(response_conjugate base zs).2]
  simp

/-- At a real argument, evaluation of a polynomial with conjugated coefficients is the conjugate
of the original evaluation. -/
theorem eval_conjugatePolynomial_real (p : Polynomial ℂ) (x : ℝ) :
    (p.map (starRingEnd ℂ)).eval (x : ℂ) = star (p.eval (x : ℂ)) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    simp [hp, hq]
  · intro n a
    simp

/-- At a real argument, the first response for conjugated phase data evaluates to the conjugate
of the original first response. -/
theorem responseP_conjugate_eval (base : ℂ) (zs : List ℂ) (x : ℝ) :
    (responseP (star base) (zs.map star)).eval (x : ℂ) =
      star ((responseP base zs).eval (x : ℂ)) := by
  rw [(response_conjugate base zs).1, eval_conjugatePolynomial_real]

/-- The polynomial obtained by averaging `p` with its coefficientwise complex conjugate. -/
noncomputable def realPartPolynomial (p : Polynomial ℂ) : Polynomial ℂ :=
  (2 : ℂ)⁻¹ • (p + p.map (starRingEnd ℂ))

/-- The arithmetic mean of a complex number and its conjugate is its real part embedded in the
complex numbers. -/
theorem half_add_star (z : ℂ) : (2 : ℂ)⁻¹ * (z + star z) = (z.re : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  ring

/-- Each coefficient of `realPartPolynomial p` is the real part of the corresponding coefficient
of `p`, embedded in the complex numbers. -/
theorem realPartPolynomial_coeff (p : Polynomial ℂ) (n : ℕ) :
    (realPartPolynomial p).coeff n = ((p.coeff n).re : ℂ) := by
  simpa [realPartPolynomial, mul_add] using half_add_star (p.coeff n)

/-- At a real argument, `realPartPolynomial p` evaluates to the real part of the evaluation of
`p`, embedded in the complex numbers. -/
theorem realPartPolynomial_eval (p : Polynomial ℂ) (x : ℝ) :
    (realPartPolynomial p).eval (x : ℂ) = ((p.eval (x : ℂ)).re : ℂ) := by
  simpa [realPartPolynomial, eval_conjugatePolynomial_real, mul_add] using
    half_add_star (p.eval (x : ℂ))

/-- The real-part polynomial of the first response is the arithmetic mean of the responses for
the original and conjugated phase data. -/
theorem realPartPolynomial_responseP (base : ℂ) (zs : List ℂ) :
    realPartPolynomial (responseP base zs) =
      (2 : ℂ)⁻¹ • (responseP base zs + responseP (star base) (zs.map star)) := by
  rw [(response_conjugate base zs).1]
  rfl

/-- For phase-valued base and list entries, the squared complex norm of the first response at
one is one. -/
theorem responseP_normSq_one {base : ℂ} (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) :
    Complex.normSq ((responseP base zs).eval 1) = 1 := by
  simpa using response_normalization hb zs hzs 1

/-- For phase-valued base and list entries, the first response at one has norm one. -/
theorem responseP_norm_one {base : ℂ} (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) : ‖(responseP base zs).eval 1‖ = 1 := by
  have h := responseP_normSq_one hb zs hzs
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg ((responseP base zs).eval 1)]

/-- For phase-valued parameters, the distance from the first response at one to any complex
target `c` is at least `1 - ‖c‖`. -/
theorem responseP_endpoint_error_lower {base : ℂ} (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) (c : ℂ) :
    1 - ‖c‖ ≤ ‖(responseP base zs).eval 1 - c‖ := by
  simpa only [responseP_norm_one hb zs hzs] using
    norm_sub_norm_le ((responseP base zs).eval 1) c

/-- For an even phase-list length, the second response vanishes at zero. -/
theorem responseQ_eval_zero_of_even (base : ℂ) (zs : List ℂ)
    (heven : zs.length % 2 = 0) : (responseQ base zs).eval 0 = 0 := by
  rw [responseQ_factor_even base zs heven]
  simp [oddSingularPolynomial]

/-- For phase-valued parameters and an even phase-list length, the squared complex norm of the
first response at zero is one. -/
theorem responseP_normSq_zero_of_even {base : ℂ} (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0) :
    Complex.normSq ((responseP base zs).eval 0) = 1 := by
  simpa [responseQ_eval_zero_of_even base zs heven] using
    response_normalization hb zs hzs 0

/-- For phase-valued parameters and an even phase-list length, the first response at zero has
norm one. -/
theorem responseP_norm_zero_of_even {base : ℂ} (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0) :
    ‖(responseP base zs).eval 0‖ = 1 := by
  have h := responseP_normSq_zero_of_even hb zs hzs heven
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg ((responseP base zs).eval 0)]

end Qatlib.Concepts.QspSimulation.Achievability
