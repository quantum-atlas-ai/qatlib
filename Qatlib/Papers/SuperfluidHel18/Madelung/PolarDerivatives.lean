/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.Madelung.PolarCurrent
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Complex.Exponential

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-!
# Coordinate derivatives of the Gross–Pitaevskii polar wave

[Kedia2018SuperfluidHelicity], Section II,
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
The one-variable formulas apply to the time section and to every
Cartesian line section of the actual polar wavefunction.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.Madelung

open Qatlib.Papers.SuperfluidHel18.Madelung (polar_wave_derivative)

/-- The actual polar wavefunction along a time or coordinate section. -/
noncomputable def gpePolarWave (A θ : ℝ → ℝ) (s : ℝ) : ℂ :=
  (A s : ℂ) * Complex.exp ((θ s : ℂ) * Complex.I)

/-- The unit phase differentiates by multiplication with the imaginary phase rate. -/
private theorem hasDerivAt_gpePhase {θ : ℝ → ℝ} {s : ℝ} (h : DifferentiableAt ℝ θ s) :
    HasDerivAt (fun u => Complex.exp ((θ u : ℂ) * Complex.I))
      (Complex.I * ((deriv θ s : ℝ) : ℂ) * Complex.exp ((θ s : ℂ) * Complex.I)) s := by
  convert (h.hasDerivAt.ofReal_comp.mul_const Complex.I).cexp using 1
  ring

/-- The derivative along an actual section of a polar wave. -/
theorem deriv_gpePolarWave (A θ : ℝ → ℝ) (s : ℝ)
    (hA : DifferentiableAt ℝ A s) (hθ : DifferentiableAt ℝ θ s) :
    deriv (gpePolarWave A θ) s =
      (((deriv A s : ℝ) : ℂ) + Complex.I * ((A s * deriv θ s : ℝ) : ℂ)) *
        Complex.exp ((θ s : ℂ) * Complex.I) :=
  (polar_wave_derivative A _ (deriv A s) (deriv θ s) s
    hA.hasDerivAt (hasDerivAt_gpePhase hθ)).deriv

/-- The second Cartesian derivative produces the amplitude curvature, the
squared phase rate and the two imaginary transport terms. -/
theorem deriv_deriv_gpePolarWave (A θ : ℝ → ℝ) (s : ℝ)
    (hA : ContDiff ℝ 2 A) (hθ : ContDiff ℝ 2 θ) :
    deriv (deriv (gpePolarWave A θ)) s =
      (((deriv (deriv A) s - A s * (deriv θ s) ^ 2 : ℝ) : ℂ) +
        Complex.I * ((2 * deriv A s * deriv θ s + A s * deriv (deriv θ) s : ℝ) : ℂ)) *
          Complex.exp ((θ s : ℂ) * Complex.I) := by
  have hA₁ := hA.differentiable (by norm_num)
  have hθ₁ := hθ.differentiable (by norm_num)
  have hA₂ := (hA.differentiable_deriv_two s).hasDerivAt.ofReal_comp
  have hθ₂ := (hθ.differentiable_deriv_two s).hasDerivAt.ofReal_comp
  have hprod := (hA₁ s).hasDerivAt.ofReal_comp.fun_mul hθ₂
  have hs := (hA₂.fun_add (hprod.const_mul Complex.I)).fun_mul (hasDerivAt_gpePhase (hθ₁ s))
  have he : deriv (gpePolarWave A θ) = fun u =>
      (↑(deriv A u) + Complex.I * (↑(A u) * ↑(deriv θ u))) *
        Complex.exp ((θ u : ℂ) * Complex.I) := by
    funext u
    rw [deriv_gpePolarWave A θ u (hA₁ u) (hθ₁ u), Complex.ofReal_mul]
  rw [he, hs.deriv]
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

end Qatlib.Papers.SuperfluidHel18.Madelung
