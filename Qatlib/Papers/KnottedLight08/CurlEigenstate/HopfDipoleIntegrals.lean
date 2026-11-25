/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKModes
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfRadialMoments

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Exact radial integration of the dipole curl eigenstates

The weighted Cartesian multipole and its curl reduce to three
integrable radial combinations of the Laplace sine and cosine moments.
The resulting rational functions have the same denominator as the
Hopf pulse in spacetime.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open MeasureTheory Set

/-- The five shifted exponential moments needed by the dipole and its
curl have explicit rational forms. -/
private theorem hopf_dipole_moment_fractions {a : ℂ} (ha : 0 < a.re) (r : ℝ) :
    let p := a + Complex.I * (r : ℂ)
    let q := a - Complex.I * (r : ℂ)
    let D := a ^ 2 + (r : ℂ) ^ 2
    (Complex.I / 2) * (1 / p - 1 / q) = (r : ℂ) / D ∧
    (1 / 2 : ℂ) * (1 / p ^ 2 + 1 / q ^ 2) = (a ^ 2 - (r : ℂ) ^ 2) / D ^ 2 ∧
    (Complex.I / 2) * (1 / p ^ 2 - 1 / q ^ 2) = 2 * a * (r : ℂ) / D ^ 2 ∧
    (1 / 2 : ℂ) * (2 / p ^ 3 + 2 / q ^ 3) =
      2 * a * (a ^ 2 - 3 * (r : ℂ) ^ 2) / D ^ 3 ∧
    (Complex.I / 2) * (2 / p ^ 3 - 2 / q ^ 3) =
      2 * (r : ℂ) * (3 * a ^ 2 - (r : ℂ) ^ 2) / D ^ 3 := by
  let p := a + Complex.I * (r : ℂ)
  let q := a - Complex.I * (r : ℂ)
  have hp : p ≠ 0 := by
    have hp' : 0 < p.re := by simpa [p, Complex.add_re, Complex.mul_re] using ha
    intro h
    simp [h] at hp'
  have hq : q ≠ 0 := by
    have hq' : 0 < q.re := by simpa [q, Complex.sub_re, Complex.mul_re] using ha
    intro h
    simp [h] at hq'
  have hD : p * q = a ^ 2 + (r : ℂ) ^ 2 := by
    dsimp [p, q]
    linear_combination -((r : ℂ) ^ 2) * Complex.I_mul_I
  have hd : a ^ 2 + (r : ℂ) ^ 2 ≠ 0 := hD ▸ mul_ne_zero hp hq
  have hc (n : ℕ) (c : ℂ) :
      (p ^ n * q ^ n) * (c / p ^ n) = c * q ^ n ∧
      (p ^ n * q ^ n) * (c / q ^ n) = c * p ^ n := by
    constructor
    · calc
        _ = q ^ n * ((c / p ^ n) * p ^ n) := by ring
        _ = _ := by rw [div_mul_cancel₀ _ (pow_ne_zero n hp), mul_comm]
    · calc
        _ = p ^ n * ((c / q ^ n) * q ^ n) := by ring
        _ = _ := by rw [div_mul_cancel₀ _ (pow_ne_zero n hq), mul_comm]
  change (Complex.I / 2) * (1 / p - 1 / q) = (r : ℂ) / (a ^ 2 + (r : ℂ) ^ 2) ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hD]
    field_simp [hp, hq]
    dsimp [p, q]
    ring_nf
    norm_num [Complex.I_mul_I, pow_succ]
  · apply (eq_div_iff (pow_ne_zero 2 hd)).2
    rw [← hD, mul_pow, mul_comm, ← mul_assoc, mul_comm _ (1 / 2 : ℂ), mul_assoc,
      mul_add, (hc 2 1).1, (hc 2 1).2]
    dsimp [p, q]
    ring_nf
    norm_num [Complex.I_mul_I, pow_succ, sub_eq_add_neg]
  · apply (eq_div_iff (pow_ne_zero 2 hd)).2
    rw [← hD, mul_pow, mul_comm, ← mul_assoc, mul_comm _ (Complex.I / 2), mul_assoc,
      mul_sub, (hc 2 1).1, (hc 2 1).2]
    dsimp [p, q]
    ring_nf
    norm_num [Complex.I_mul_I, pow_succ]
  · apply (eq_div_iff (pow_ne_zero 3 hd)).2
    rw [← hD, mul_pow, mul_comm, ← mul_assoc, mul_comm _ (1 / 2 : ℂ), mul_assoc,
      mul_add, (hc 3 2).1, (hc 3 2).2]
    dsimp [p, q]
    ring_nf
    norm_num [Complex.I_mul_I, pow_succ]
  · apply (eq_div_iff (pow_ne_zero 3 hd)).2
    rw [← hD, mul_pow, mul_comm, ← mul_assoc, mul_comm _ (Complex.I / 2), mul_assoc,
      mul_sub, (hc 3 2).1, (hc 3 2).2]
    dsimp [p, q]
    ring_nf
    norm_num [Complex.I_mul_I, pow_succ]

/-- The three radial combinations in the Cartesian dipole and its
first curl are integrable against the complex pulse damping. -/
theorem hopf_dipole_radial_integrals {a : ℂ} (ha : 0 < a.re) (r : ℝ) :
    let E := fun k : ℝ => Complex.exp (-a * (k : ℂ))
    let G := fun k : ℝ => E k * (ckKernel (k * r) : ℂ)
    let J := fun k : ℝ => E k * (k : ℂ) * (ckKernel (k * r) : ℂ)
    let H := fun k : ℝ => E k * ((k ^ 2 * r ^ 2 * Real.sin (k * r) - 3 * ckKernel (k * r) : ℝ) : ℂ)
    let D := a ^ 2 + (r : ℂ) ^ 2
    IntegrableOn G (Ioi 0) ∧ IntegrableOn J (Ioi 0) ∧ IntegrableOn H (Ioi 0) ∧
      (∫ k in Ioi (0 : ℝ), G k) = 2 * (r : ℂ) ^ 3 / D ^ 2 ∧
      (∫ k in Ioi (0 : ℝ), J k) = 8 * a * (r : ℂ) ^ 3 / D ^ 3 ∧
      (∫ k in Ioi (0 : ℝ), H k) = -(8 * (r : ℂ) ^ 5) / D ^ 3 := by
  dsimp only
  let E := fun k : ℝ => Complex.exp (-a * (k : ℂ))
  let G := fun k : ℝ => E k * (ckKernel (k * r) : ℂ)
  let J := fun k : ℝ => E k * (k : ℂ) * (ckKernel (k * r) : ℂ)
  let H := fun k : ℝ => E k * ((k ^ 2 * r ^ 2 * Real.sin (k * r) - 3 * ckKernel (k * r) : ℝ) : ℂ)
  let D := a ^ 2 + (r : ℂ) ^ 2
  let S := fun n : ℕ => fun k : ℝ => (k : ℂ) ^ n * E k * (Real.sin (r * k) : ℂ)
  let C := fun n : ℕ => fun k : ℝ => (k : ℂ) ^ n * E k * (Real.cos (r * k) : ℂ)
  have hD : D ≠ 0 := by
    have hfactor : (a + Complex.I * (r : ℂ)) * (a - Complex.I * (r : ℂ)) = D := by
      dsimp [D]
      linear_combination -((r : ℂ) ^ 2) * Complex.I_mul_I
    rw [← hfactor]
    apply mul_ne_zero
    · intro h
      have hre := congrArg Complex.re h
      simp [Complex.add_re, Complex.mul_re] at hre
      linarith
    · intro h
      have hre := congrArg Complex.re h
      simp [Complex.sub_re, Complex.mul_re] at hre
      linarith
  have hSi (n : ℕ) : IntegrableOn (S n) (Ioi 0) := (hopf_laplace_trig_moments ha r n).1
  have hCi (n : ℕ) : IntegrableOn (C n) (Ioi 0) := (hopf_laplace_trig_moments ha r n).2.1
  obtain ⟨hSin₀, hCos₁, hSin₁, hCos₂, hSin₂⟩ := hopf_dipole_moment_fractions ha r
  have hS₀ : (∫ k in Ioi (0 : ℝ), S 0 k) = (r : ℂ) / D := by
    refine Eq.trans (hopf_laplace_trig_moments ha r 0).2.2.1 ?_
    simpa [D] using hSin₀
  have hC₁ : (∫ k in Ioi (0 : ℝ), C 1 k) = (a ^ 2 - (r : ℂ) ^ 2) / D ^ 2 := by
    refine Eq.trans (hopf_laplace_trig_moments ha r 1).2.2.2 ?_
    simpa [D] using hCos₁
  have hS₁ : (∫ k in Ioi (0 : ℝ), S 1 k) = 2 * a * (r : ℂ) / D ^ 2 := by
    refine Eq.trans (hopf_laplace_trig_moments ha r 1).2.2.1 ?_
    simpa [D] using hSin₁
  have hC₂ : (∫ k in Ioi (0 : ℝ), C 2 k) = 2 * a * (a ^ 2 - 3 * (r : ℂ) ^ 2) / D ^ 3 := by
    refine Eq.trans (hopf_laplace_trig_moments ha r 2).2.2.2 ?_
    simpa [D] using hCos₂
  have hS₂ : (∫ k in Ioi (0 : ℝ), S 2 k) = 2 * (r : ℂ) * (3 * a ^ 2 - (r : ℂ) ^ 2) / D ^ 3 := by
    refine Eq.trans (hopf_laplace_trig_moments ha r 2).2.2.1 ?_
    simpa [D] using hSin₂
  have eqG : G = fun k => S 0 k - (r : ℂ) * C 1 k := by
    funext k
    dsimp [G, S, C]
    rw [ckKernel, mul_comm k r]
    push_cast
    ring
  have eqJ : J = fun k => S 1 k - (r : ℂ) * C 2 k := by
    funext k
    dsimp [J, S, C]
    rw [ckKernel, mul_comm k r]
    push_cast
    ring
  have eqH : H = fun k => (r : ℂ) ^ 2 * S 2 k - 3 * G k := by
    funext k
    dsimp [H, S, G]
    rw [mul_comm k r]
    push_cast
    ring
  have hGi : IntegrableOn G (Ioi 0) := by
    rw [eqG]
    exact (hSi 0).sub ((hCi 1).const_mul _)
  have hJi : IntegrableOn J (Ioi 0) := by
    rw [eqJ]
    exact (hSi 1).sub ((hCi 2).const_mul _)
  have hHi : IntegrableOn H (Ioi 0) := by
    rw [eqH]
    exact ((hSi 2).const_mul _).sub (hGi.const_mul _)
  have hGv : (∫ k in Ioi (0 : ℝ), G k) = 2 * (r : ℂ) ^ 3 / D ^ 2 := by
    rw [eqG, integral_sub (hSi 0) ((hCi 1).const_mul _), integral_const_mul, hS₀, hC₁]
    field_simp [hD]
    dsimp [D]
    ring
  have hJv : (∫ k in Ioi (0 : ℝ), J k) = 8 * a * (r : ℂ) ^ 3 / D ^ 3 := by
    rw [eqJ, integral_sub (hSi 1) ((hCi 2).const_mul _), integral_const_mul, hS₁, hC₂]
    field_simp [hD]
    dsimp [D]
    ring
  have hHv : (∫ k in Ioi (0 : ℝ), H k) = -(8 * (r : ℂ) ^ 5) / D ^ 3 := by
    rw [eqH, integral_sub ((hSi 2).const_mul _) (hGi.const_mul _),
      integral_const_mul, integral_const_mul, hS₂, hGv]
    field_simp [hD]
    dsimp [D]
    ring
  exact ⟨hGi, hJi, hHi, hGv, hJv, hHv⟩

end Qatlib.Papers.KnottedLight08.CurlEigenstate
