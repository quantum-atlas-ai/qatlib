/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfArticleSpectrum

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Convergence and time derivative of the Hopf vector potential

The dipole identity for `g(kr)/k` removes the apparent singularity
at zero frequency. The time phase has constant absolute value, so
the integrable dipole field density dominates the time derivative.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Filter MeasureTheory Set
open scoped Topology

/-- Time changes the phase of the exponential damping and preserves its norm. -/
private theorem norm_hopf_damping (t k : ℝ) :
    ‖Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ))‖ = Real.exp (-k) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.add_re]

/-- Dividing the first dipole numerator by the frequency yields a
bounded combination of sinc and cosine. -/
private theorem ckKernel_div_frequency {k : ℝ} (hk : k ≠ 0) (r : ℝ) :
    ckKernel (k * r) / k = r * (Real.sinc (k * r) - Real.cos (k * r)) := by
  by_cases hr : r = 0
  · simp [hr, ckKernel]
  · rw [ckKernel, Real.sinc_of_ne_zero (mul_ne_zero hk hr)]
    field_simp [hk, hr]

/-- The two dipole radial contributions divided by the frequency
remain absolutely integrable at zero and infinity. -/
private theorem integrableOn_hopf_potential_radial (r t : ℝ) :
    let E := fun k : ℝ => Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ))
    IntegrableOn (fun k => E k * ((ckKernel (k * r) / k : ℝ) : ℂ)) (Ioi 0) ∧
    IntegrableOn (fun k => E k *
      (((k ^ 2 * r ^ 2 * Real.sin (k * r) - 3 * ckKernel (k * r)) / k : ℝ) : ℂ)) (Ioi 0) := by
  let a : ℂ := 1 + Complex.I * (t : ℂ)
  let E := fun k : ℝ => Complex.exp (-a * (k : ℂ))
  have ha : 0 < a.re := by simp [a, Complex.add_re, Complex.mul_re]
  have hs : IntegrableOn (fun k : ℝ => E k * (Real.sinc (k * r) : ℂ)) (Ioi 0) := by
    apply (integrableOn_exp_neg_Ioi 0).mono'
    · have hE : Continuous E := by dsimp [E]; fun_prop
      have hS : Continuous (fun k : ℝ => Real.sinc (k * r)) :=
        Real.continuous_sinc.comp (continuous_id.mul_const r)
      exact (hE.mul (Complex.continuous_ofReal.comp hS)).aestronglyMeasurable
    · exact Eventually.of_forall fun k => by
        rw [norm_mul, show ‖E k‖ = Real.exp (-k) from norm_hopf_damping t k,
          Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sinc_le_one _)
  have hc : IntegrableOn (fun k : ℝ => E k * (Real.cos (k * r) : ℂ)) (Ioi 0) := by
    simpa only [pow_zero, one_mul, mul_comm r] using (hopf_laplace_trig_moments ha r 0).2.1
  let G := fun k : ℝ => E k * ((ckKernel (k * r) / k : ℝ) : ℂ)
  let H := fun k : ℝ => E k *
    (((k ^ 2 * r ^ 2 * Real.sin (k * r) - 3 * ckKernel (k * r)) / k : ℝ) : ℂ)
  have hG : IntegrableOn G (Ioi 0) := by
    refine IntegrableOn.congr_fun ((hs.sub hc).const_mul (r : ℂ)) ?_ measurableSet_Ioi
    intro k hk
    change (r : ℂ) * (E k * (Real.sinc (k * r) : ℂ) -
      E k * (Real.cos (k * r) : ℂ)) = G k
    dsimp only [G]
    rw [ckKernel_div_frequency hk.ne']
    push_cast
    ring
  have hs₁ : IntegrableOn (fun k : ℝ => (k : ℂ) * E k * (Real.sin (k * r) : ℂ)) (Ioi 0) := by
    simpa only [pow_one, mul_comm r] using (hopf_laplace_trig_moments ha r 1).1
  have hH : IntegrableOn H (Ioi 0) := by
    refine IntegrableOn.congr_fun ((hs₁.const_mul ((r : ℂ) ^ 2)).sub (hG.const_mul 3))
      ?_ measurableSet_Ioi
    intro k hk
    have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
    change (r : ℂ) ^ 2 * ((k : ℂ) * E k * (Real.sin (k * r) : ℂ)) - 3 * G k = H k
    dsimp only [G, H]
    simp only [mul_comm k r]
    push_cast
    field_simp [hkC]
  exact ⟨hG, hH⟩

/-- The positive-frequency Hopf potential density with its finite
dipole value at the spatial origin. -/
noncomputable def hopfPotentialDensity (x y z t : ℝ) (j : Fin 3) (k : ℝ) : ℂ :=
  Complex.I / (2 * (Real.pi : ℂ)) *
    (Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ)) * hopfDipoleMode k x y z j) / (k : ℂ)

/-- The potential density agrees with the article's integrand off the
spatial origin at every nonzero frequency. -/
theorem hopfPotentialDensity_eq_article {k x y z : ℝ} (hk : k ≠ 0)
    (hr : ckRadius x y z ≠ 0) (t : ℝ) (j : Fin 3) :
    hopfPotentialDensity x y z t j k = hopfArticlePotential k x y z t j :=
  (hopfArticlePotential_eq_dipole hk hr t j).symm

/-- The actual Hopf potential density is absolutely integrable in
frequency, including at the spatial origin. -/
theorem integrableOn_hopfPotentialDensity (x y z t : ℝ) (j : Fin 3) :
    IntegrableOn (hopfPotentialDensity x y z t j) (Ioi 0) := by
  let a : ℂ := 1 + Complex.I * (t : ℂ)
  let E := fun k : ℝ => Complex.exp (-a * (k : ℂ))
  let c : ℂ := Complex.I / (2 * (Real.pi : ℂ))
  let r := ckRadius x y z
  have ha : 0 < a.re := by simp [a, Complex.add_re, Complex.mul_re]
  by_cases hr : r = 0
  · refine IntegrableOn.congr_fun ((integrableOn_hopf_laplace_moment ha 2).const_mul
      (c * ckConstantCurl j / 3)) ?_ measurableSet_Ioi
    intro k hk
    have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
    change (c * ckConstantCurl j / 3) * ((k : ℂ) ^ 2 * E k) =
      c * (E k * hopfDipoleMode k x y z j) / (k : ℂ)
    rw [hopfDipoleMode, ite_eq_left hr]
    field_simp [hkC]
  · let G := fun k : ℝ => E k * (ckKernel (k * r) : ℂ)
    let P := fun k : ℝ => E k * ((ckKernel (k * r) / k : ℝ) : ℂ)
    let Q := fun k : ℝ => E k *
      (((k ^ 2 * r ^ 2 * Real.sin (k * r) - 3 * ckKernel (k * r)) / k : ℝ) : ℂ)
    have hG : IntegrableOn G (Ioi 0) := (hopf_dipole_radial_integrals ha r).1
    have hP : IntegrableOn P (Ioi 0) := (integrableOn_hopf_potential_radial r t).1
    have hQ : IntegrableOn Q (Ioi 0) := (integrableOn_hopf_potential_radial r t).2
    let A := ckAngular x y z j / (r : ℂ) ^ 3
    let B := ckCurlAngular x y z j / (r : ℂ) ^ 5
    let C := ckConstantCurl j / (r : ℂ) ^ 3
    have hcomb : IntegrableOn (fun k => c * (A * G k + B * Q k + C * P k)) (Ioi 0) :=
      (((hG.const_mul A).add (hQ.const_mul B)).add (hP.const_mul C)).const_mul c
    refine hcomb.congr_fun ?_ measurableSet_Ioi
    intro k hk
    have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
    change c * (A * G k + B * Q k + C * P k) =
      c * (E k * hopfDipoleMode k x y z j) / (k : ℂ)
    rw [hopfDipoleMode, ite_eq_right hr]
    simp only [ckBeltramiPlus, ckMultipoleField, ckCurlMultipoleField, ckRadialComb]
    dsimp only [A, B, C, G, P, Q, r]
    push_cast
    field_simp [hkC]
    ring

end Qatlib.Papers.KnottedLight08.CurlEigenstate
