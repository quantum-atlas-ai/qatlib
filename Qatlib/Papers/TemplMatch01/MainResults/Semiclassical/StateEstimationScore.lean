/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option warningAsError false

namespace Qatlib.Papers.TemplMatch01.MainResults.Semiclassical

open Qatlib.Foundations.PureStateMath
open Matrix MeasureTheory BigOperators
open scoped ComplexOrder BigOperators MatrixOrder

set_option autoImplicit false

open intervalIntegral

noncomputable def estMuAmp (N M : ℕ) (ϕ : ℝ) (m k : ℕ) : ℂ :=
  ((Real.sqrt (M : ℝ))⁻¹ : ℂ) *
    Complex.exp (-(Complex.I) * ((((N : ℝ) - 2 * (k : ℝ)) *
      (ϕ / 2 + (m : ℝ) * Real.pi / (M : ℝ)) : ℝ) : ℂ))

noncomputable def estFAmp (N : ℕ) (φ : ℝ) (k : ℕ) : ℂ :=
  ((Real.sqrt ((Nat.choose N k : ℝ) / (2 : ℝ) ^ N) : ℝ) : ℂ) *
    Complex.exp (-(Complex.I) * ((((N : ℝ) - 2 * (k : ℝ)) * (φ / 2) : ℝ) : ℂ))

noncomputable def estOverlap (N M : ℕ) (φ ϕ : ℝ) (m : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1), star (estMuAmp N M ϕ m k) * estFAmp N φ k

noncomputable def estOutcomeProb (N M j : ℕ) (φ ϕ : ℝ) : ℝ :=
  ∑ m ∈ (if j = 0 then Finset.range (M / 2) else Finset.Ico (M / 2) M),
    Complex.normSq (estOverlap N M φ ϕ m)

noncomputable def estGuessFidelity (θ φ : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then Real.cos ((φ - Real.pi / 2 + θ) / 2) ^ 2
  else Real.cos ((φ - Real.pi / 2 - θ) / 2) ^ 2

noncomputable def stateEstimationScore (N M : ℕ) (θ ϕ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 2, (1 / (2 * Real.pi)) *
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
      estOutcomeProb N M j φ ϕ * estGuessFidelity θ φ j

noncomputable def estCoefficientSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (Nat.choose N k : ℝ) *
    Real.sqrt (((N : ℝ) - (k : ℝ)) / ((k : ℝ) + 1))

noncomputable def estClosedForm (N M : ℕ) (ϕ θ : ℝ) : ℝ :=
  1 / 2 + Real.cos θ * Real.cos (ϕ - Real.pi / (M : ℝ)) /
    ((2 : ℝ) ^ N * (M : ℝ) * Real.sin (Real.pi / (M : ℝ))) * estCoefficientSum N

lemma estGuessFidelity_integral (θ : ℝ) (j : ℕ) :
    (1 / (2 * Real.pi)) * ∫ φ in (0 : ℝ)..(2 * Real.pi), estGuessFidelity θ φ j
      = 1 / 2 := by
  have hcos_shift : ∀ c : ℝ, ∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos (φ - c) = 0 := by
    intro c
    have hfun : (fun φ : ℝ => Real.cos (φ - c)) = (fun φ : ℝ => Real.cos (φ + (-c))) := by
      ext φ; rw [sub_eq_add_neg]
    rw [hfun, integral_comp_add_right (f := Real.cos) (a := (0 : ℝ)) (b := 2 * Real.pi) (d := -c)]
    rw [show (0 : ℝ) + (-c) = -c by ring, integral_cos]
    rw [show 2 * Real.pi + (-c) = (-c) + 2 * Real.pi by ring, Real.sin_add_two_pi]
    ring
  have hbase : ∀ c : ℝ,
      (1 / (2 * Real.pi)) * ∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos ((φ - c) / 2) ^ 2
        = 1 / 2 := by
    intro c
    have hpt : ∀ φ : ℝ, Real.cos ((φ - c) / 2) ^ 2 = (1 + Real.cos (φ - c)) / 2 := by
      intro φ
      have h := Real.cos_two_mul ((φ - c) / 2)
      rw [show 2 * ((φ - c) / 2) = φ - c by ring] at h
      linarith
    simp_rw [hpt]
    rw [intervalIntegral.integral_div]
    rw [intervalIntegral.integral_add (f := fun _ : ℝ => (1 : ℝ))
          (g := fun x : ℝ => Real.cos (x - c))
          (continuous_const.intervalIntegrable 0 (2 * Real.pi))
          ((Real.continuous_cos.comp (continuous_id.sub continuous_const)).intervalIntegrable
            0 (2 * Real.pi))]
    rw [hcos_shift c]
    rw [show (∫ φ in (0 : ℝ)..(2 * Real.pi), (1 : ℝ)) = 2 * Real.pi by
        rw [intervalIntegral.integral_const]; simp]
    field_simp
    ring
  unfold estGuessFidelity
  split_ifs with hj
  · have h := hbase (Real.pi / 2 - θ)
    simpa only [show ∀ φ : ℝ, φ - Real.pi / 2 + θ = φ - (Real.pi / 2 - θ) by
      intro φ; ring] using h
  · have h := hbase (Real.pi / 2 + θ)
    simpa only [show ∀ φ : ℝ, φ - Real.pi / 2 - θ = φ - (Real.pi / 2 + θ) by
      intro φ; ring] using h

theorem estClosedForm_special (N : ℕ) (θ : ℝ) :
    estClosedForm N (N + 1) (Real.pi / ((N : ℝ) + 1)) θ
      = 1 / 2 + Real.cos θ /
        ((2 : ℝ) ^ N * ((N : ℝ) + 1) * Real.sin (Real.pi / ((N : ℝ) + 1))) *
          estCoefficientSum N := by
  rw [estClosedForm]
  push_cast
  rw [show Real.pi / ((N : ℝ) + 1) - Real.pi / ((N : ℝ) + 1) = 0 by ring]
  simp [Real.cos_zero]

end Qatlib.Papers.TemplMatch01.MainResults.Semiclassical
