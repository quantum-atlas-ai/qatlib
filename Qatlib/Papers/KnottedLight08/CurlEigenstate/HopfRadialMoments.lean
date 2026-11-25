/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfLaplaceMoments

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring

/-!
# The radial sine and cosine moments of the Hopf pulse

The Cartesian dipole multipole and its curl combine the first few sine
and cosine moments. Complex Laplace moments evaluate these integrals
while keeping the real damping and temporal phase together.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open MeasureTheory Set

/-- The damped polynomial sine and cosine moments are both integrable.
Their values are the difference and sum of the two complex Laplace
moments at the shifted damping parameters. -/
theorem hopf_laplace_trig_moments {a : ℂ} (ha : 0 < a.re) (r : ℝ) (n : ℕ) :
    let S := fun k : ℝ => (k : ℂ) ^ n * Complex.exp (-a * (k : ℂ)) * (Real.sin (r * k) : ℂ)
    let C := fun k : ℝ => (k : ℂ) ^ n * Complex.exp (-a * (k : ℂ)) * (Real.cos (r * k) : ℂ)
    let u := (n.factorial : ℂ) / (a + Complex.I * (r : ℂ)) ^ (n + 1)
    let v := (n.factorial : ℂ) / (a - Complex.I * (r : ℂ)) ^ (n + 1)
    IntegrableOn S (Ioi 0) ∧ IntegrableOn C (Ioi 0) ∧
      (∫ k in Ioi (0 : ℝ), S k) = (Complex.I / 2) * (u - v) ∧
      (∫ k in Ioi (0 : ℝ), C k) = (1 / 2 : ℂ) * (u + v) := by
  let p := a + Complex.I * (r : ℂ)
  let q := a - Complex.I * (r : ℂ)
  let P := fun k : ℝ => (k : ℂ) ^ n * Complex.exp (-p * (k : ℂ))
  let Q := fun k : ℝ => (k : ℂ) ^ n * Complex.exp (-q * (k : ℂ))
  let S := fun k : ℝ => (k : ℂ) ^ n * Complex.exp (-a * (k : ℂ)) * (Real.sin (r * k) : ℂ)
  let C := fun k : ℝ => (k : ℂ) ^ n * Complex.exp (-a * (k : ℂ)) * (Real.cos (r * k) : ℂ)
  have hp : 0 < p.re := by simpa [p, Complex.add_re, Complex.mul_re] using ha
  have hq : 0 < q.re := by simpa [q, Complex.sub_re, Complex.mul_re] using ha
  have hP : IntegrableOn P (Ioi 0) := integrableOn_hopf_laplace_moment hp n
  have hQ : IntegrableOn Q (Ioi 0) := integrableOn_hopf_laplace_moment hq n
  have hr₁ (k : ℝ) :
      -p * (k : ℂ) = -a * (k : ℂ) + -((r * k : ℝ) : ℂ) * Complex.I := by
    dsimp [p]
    push_cast
    ring
  have hr₂ (k : ℝ) :
      -q * (k : ℂ) = -a * (k : ℂ) + ((r * k : ℝ) : ℂ) * Complex.I := by
    dsimp [q]
    push_cast
    ring
  have hS : S = fun k => (Complex.I / 2) * (P k - Q k) := by
    funext k
    dsimp only [S, P, Q]
    rw [Complex.ofReal_sin, Complex.sin, hr₁, hr₂, Complex.exp_add, Complex.exp_add]
    ring
  have hC : C = fun k => (1 / 2 : ℂ) * (P k + Q k) := by
    funext k
    dsimp only [C, P, Q]
    rw [Complex.ofReal_cos, Complex.cos, hr₁, hr₂, Complex.exp_add, Complex.exp_add]
    ring
  change IntegrableOn S (Ioi 0) ∧ IntegrableOn C (Ioi 0) ∧
    (∫ k in Ioi (0 : ℝ), S k) =
      (Complex.I / 2) * ((n.factorial : ℂ) / p ^ (n + 1) - (n.factorial : ℂ) / q ^ (n + 1)) ∧
    (∫ k in Ioi (0 : ℝ), C k) =
      (1 / 2 : ℂ) * ((n.factorial : ℂ) / p ^ (n + 1) + (n.factorial : ℂ) / q ^ (n + 1))
  have hPval : (∫ k in Ioi (0 : ℝ), P k) = (n.factorial : ℂ) / p ^ (n + 1) :=
    integral_hopf_laplace_moment hp n
  have hQval : (∫ k in Ioi (0 : ℝ), Q k) = (n.factorial : ℂ) / q ^ (n + 1) :=
    integral_hopf_laplace_moment hq n
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hS]
    exact (hP.sub hQ).const_mul _
  · rw [hC]
    exact (hP.add hQ).const_mul _
  · rw [hS, integral_const_mul, integral_sub hP hQ, hPval, hQval]
  · rw [hC, integral_const_mul, integral_add hP hQ, hPval, hQval]

end Qatlib.Papers.KnottedLight08.CurlEigenstate
