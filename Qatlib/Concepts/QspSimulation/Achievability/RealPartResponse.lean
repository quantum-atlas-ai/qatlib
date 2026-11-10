/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.Eval.SMul
import Qatlib.Concepts.QspSimulation.Achievability.ResponseFactorization
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.QspSimulation.Achievability

open Polynomial

theorem IsPhase.conjugate {z : ℂ} (hz : IsPhase z) : IsPhase (star z) := by
  simpa only [IsPhase, star_star, mul_comm] using hz

theorem phases_conjugate (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    ∀ z ∈ zs.map star, IsPhase z := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
  exact IsPhase.conjugate (hzs w hw)

theorem response_conjugate (base : ℂ) (zs : List ℂ) :
    responseP (star base) (zs.map star) = (responseP base zs).map (starRingEnd ℂ) ∧
    responseQ (star base) (zs.map star) = (responseQ base zs).map (starRingEnd ℂ) := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    simp only [List.map_cons, responseP_cons, responseQ_cons]
    rw [ih.1, ih.2]
    simp

theorem responseP_conjugate_coeff (base : ℂ) (zs : List ℂ) (n : ℕ) :
    (responseP (star base) (zs.map star)).coeff n = star ((responseP base zs).coeff n) := by
  rw [(response_conjugate base zs).1]
  simp

theorem responseQ_conjugate_coeff (base : ℂ) (zs : List ℂ) (n : ℕ) :
    (responseQ (star base) (zs.map star)).coeff n = star ((responseQ base zs).coeff n) := by
  rw [(response_conjugate base zs).2]
  simp

theorem eval_conjugatePolynomial_real (p : Polynomial ℂ) (x : ℝ) :
    (p.map (starRingEnd ℂ)).eval (x : ℂ) = star (p.eval (x : ℂ)) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    simp [hp, hq]
  · intro n a
    simp

theorem responseP_conjugate_eval (base : ℂ) (zs : List ℂ) (x : ℝ) :
    (responseP (star base) (zs.map star)).eval (x : ℂ) =
      star ((responseP base zs).eval (x : ℂ)) := by
  rw [(response_conjugate base zs).1, eval_conjugatePolynomial_real]

noncomputable def realPartPolynomial (p : Polynomial ℂ) : Polynomial ℂ :=
  (2 : ℂ)⁻¹ • (p + p.map (starRingEnd ℂ))

theorem half_add_star (z : ℂ) : (2 : ℂ)⁻¹ * (z + star z) = (z.re : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  ring

theorem realPartPolynomial_coeff (p : Polynomial ℂ) (n : ℕ) :
    (realPartPolynomial p).coeff n = ((p.coeff n).re : ℂ) := by
  simpa [realPartPolynomial, mul_add] using half_add_star (p.coeff n)

theorem realPartPolynomial_eval (p : Polynomial ℂ) (x : ℝ) :
    (realPartPolynomial p).eval (x : ℂ) = ((p.eval (x : ℂ)).re : ℂ) := by
  simpa [realPartPolynomial, eval_conjugatePolynomial_real, mul_add] using
    half_add_star (p.eval (x : ℂ))

theorem realPartPolynomial_responseP (base : ℂ) (zs : List ℂ) :
    realPartPolynomial (responseP base zs) =
      (2 : ℂ)⁻¹ • (responseP base zs + responseP (star base) (zs.map star)) := by
  rw [(response_conjugate base zs).1]
  rfl

theorem responseP_normSq_one {base : ℂ} (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) :
    Complex.normSq ((responseP base zs).eval 1) = 1 := by
  simpa using response_normalization hb zs hzs 1

theorem responseP_norm_one {base : ℂ} (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) : ‖(responseP base zs).eval 1‖ = 1 := by
  have h := responseP_normSq_one hb zs hzs
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg ((responseP base zs).eval 1)]

theorem responseP_endpoint_error_lower {base : ℂ} (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) (c : ℂ) :
    1 - ‖c‖ ≤ ‖(responseP base zs).eval 1 - c‖ := by
  simpa only [responseP_norm_one hb zs hzs] using
    norm_sub_norm_le ((responseP base zs).eval 1) c

theorem responseQ_eval_zero_of_even (base : ℂ) (zs : List ℂ)
    (heven : zs.length % 2 = 0) : (responseQ base zs).eval 0 = 0 := by
  rw [responseQ_factor_even base zs heven]
  simp [oddSingularPolynomial]

theorem responseP_normSq_zero_of_even {base : ℂ} (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0) :
    Complex.normSq ((responseP base zs).eval 0) = 1 := by
  simpa [responseQ_eval_zero_of_even base zs heven] using
    response_normalization hb zs hzs 0

theorem responseP_norm_zero_of_even {base : ℂ} (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0) :
    ‖(responseP base zs).eval 0‖ = 1 := by
  have h := responseP_normSq_zero_of_even hb zs hzs heven
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg ((responseP base zs).eval 0)]

end Qatlib.Concepts.QspSimulation.Achievability
