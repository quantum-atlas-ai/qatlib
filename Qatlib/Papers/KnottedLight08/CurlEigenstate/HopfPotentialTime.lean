/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfPotentialIntegral

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Time differentiation of the published Hopf potential

The positive-frequency potential integral can be differentiated in
time at every spatial point. The derivative integrand is exactly the
absolutely integrable positive dipole density of the Rañada field.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Filter MeasureTheory Set
open Qatlib.Papers.KnottedLight08.HopfField (ranadaField ranadaE ranadaB_im)
open scoped Topology

/-- The positive-frequency part of the Hopf vector potential. -/
noncomputable def hopfPositivePotential (x y z t : ℝ) (j : Fin 3) : ℂ :=
  ∫ k in Ioi (0 : ℝ), hopfPotentialDensity x y z t j k

/-- The real potential includes both the positive-frequency part
and its complex conjugate, as in the article. -/
noncomputable def hopfVectorPotential (x y z t : ℝ) (j : Fin 3) : ℝ :=
  2 * (hopfPositivePotential x y z t j).re

/-- Away from the origin the positive potential is the integral of the
published TE/TM density. -/
theorem hopfPositivePotential_eq_article {x y z : ℝ} (hr : ckRadius x y z ≠ 0)
    (t : ℝ) (j : Fin 3) :
    hopfPositivePotential x y z t j =
      ∫ k in Ioi (0 : ℝ), hopfArticlePotential k x y z t j := by
  unfold hopfPositivePotential
  exact setIntegral_congr_fun measurableSet_Ioi fun _ hk =>
    hopfPotentialDensity_eq_article hk.ne' hr t j

/-- Time differentiation multiplies the density by the Fourier frequency
`-ik`. -/
theorem hasDerivAt_hopfPotentialDensity_time (x y z t : ℝ) (j : Fin 3) (k : ℝ) :
    HasDerivAt (fun s => hopfPotentialDensity x y z s j k)
      (-Complex.I * (k : ℂ) * hopfPotentialDensity x y z t j k) t := by
  have hR : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := (hasDerivAt_id t).ofReal_comp
  have hArg : HasDerivAt (fun s : ℝ => -(1 + Complex.I * (s : ℂ)) * (k : ℂ))
      (-Complex.I * (k : ℂ)) t := by
    have h := ((hasDerivAt_const t (1 : ℂ)).add (hR.const_mul Complex.I)).neg.mul_const (k : ℂ)
    simpa only [Pi.neg_apply, Pi.add_apply, mul_one, zero_add] using h
  refine HasDerivAt.congr_deriv
    (((hArg.cexp.mul_const (hopfDipoleMode k x y z j)).const_mul
      (Complex.I / (2 * (Real.pi : ℂ)))).div_const (k : ℂ)) ?_
  simp only [hopfPotentialDensity]
  ring

/-- The norm of the time derivative density is independent of time. -/
private theorem norm_hopfPotentialDerivative (x y z s t k : ℝ) (j : Fin 3) :
    ‖-Complex.I * (k : ℂ) * hopfPotentialDensity x y z s j k‖ =
      ‖-Complex.I * (k : ℂ) * hopfPotentialDensity x y z t j k‖ := by
  simp only [hopfPotentialDensity, norm_mul, norm_div, Complex.norm_exp]
  have hre (u : ℝ) : (-(1 + Complex.I * (u : ℂ)) * (k : ℂ)).re = -k := by
    simp [Complex.mul_re, Complex.add_re]
  rw [hre, hre]

/-- The density's time derivative removes the reciprocal frequency and
leaves exactly the normalized dipole field density. -/
private theorem hopfPotentialDerivative_eq_fieldDensity (x y z t : ℝ) (j : Fin 3)
    {k : ℝ} (hk : k ≠ 0) :
    -Complex.I * (k : ℂ) * hopfPotentialDensity x y z t j k =
      (1 / (2 * (Real.pi : ℂ))) *
        (Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ)) * hopfDipoleMode k x y z j) := by
  have hkC := Complex.ofReal_ne_zero.mpr hk
  have hπ := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : (-Complex.I) * Complex.I = 1 := by linear_combination -Complex.I_mul_I
  rw [hopfPotentialDensity]
  calc
    _ = ((-Complex.I) * Complex.I) * ((1 / (2 * (Real.pi : ℂ))) *
        (Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ)) * hopfDipoleMode k x y z j)) := by
      field_simp [hkC, hπ]
    _ = _ := by rw [hI, one_mul]

/-- Time differentiation of the positive-frequency potential integral
commutes with integration and gives the actual Rañada field. -/
theorem hasDerivAt_hopfPositivePotential_time (x y z t : ℝ) (j : Fin 3) :
    HasDerivAt (fun s => hopfPositivePotential x y z s j) (ranadaField x y z t j) t := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F := fun s => hopfPotentialDensity x y z s j
  let D := fun (s k : ℝ) => -Complex.I * (k : ℂ) * F s k
  obtain ⟨hi, he⟩ := ranadaField_eq_hopf_dipole_superposition x y z t j
  let U := fun k : ℝ => Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ)) * hopfDipoleMode k x y z j
  have hU : IntegrableOn U (Ioi 0) := hi
  have hDU : EqOn (D t) (fun k => (1 / (2 * (Real.pi : ℂ))) * U k) (Ioi (0 : ℝ)) :=
    fun _ hk => hopfPotentialDerivative_eq_fieldDensity x y z t j hk.ne'
  have hD : Integrable (D t) μ := IntegrableOn.congr_fun
    (hU.const_mul (1 / (2 * (Real.pi : ℂ)))) (fun k hk => (hDU hk).symm) measurableSet_Ioi
  have hr : (∫ k, D t k ∂μ) = ranadaField x y z t j := by
    change (∫ k in Ioi (0 : ℝ), D t k) = _
    rw [setIntegral_congr_fun measurableSet_Ioi hDU, integral_const_mul]
    exact he.symm
  rw [← hr]
  change HasDerivAt (fun s => ∫ k, F s k ∂μ) _ t
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := univ) (bound := fun k => ‖D t k‖) (F := F) (F' := D) univ_mem
    (Eventually.of_forall fun s => (integrableOn_hopfPotentialDensity x y z s j).aestronglyMeasurable)
    (integrableOn_hopfPotentialDensity x y z t j) hD.aestronglyMeasurable
    (Eventually.of_forall fun k s _ => (norm_hopfPotentialDerivative x y z s t k j).le)
    hD.norm (Eventually.of_forall fun k s _ => hasDerivAt_hopfPotentialDensity_time x y z s j k)).2

/-- The negative time derivative of the published real potential
recovers the physical electric field in the article's normalization. -/
theorem deriv_hopfVectorPotential_time (x y z t : ℝ) (j : Fin 3) :
    -deriv (fun s => hopfVectorPotential x y z s j) t = -2 * (ranadaE x y z t j).re := by
  have hF := hasDerivAt_hopfPositivePotential_time x y z t j
  have h := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hF).const_mul (2 : ℝ)
  have hD : HasDerivAt (fun s => hopfVectorPotential x y z s j)
      (2 * (ranadaE x y z t j).re) t := by
    simpa [hopfVectorPotential, Function.comp_apply, ranadaField, Complex.add_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, ranadaB_im] using h
  rw [hD.deriv, neg_mul]

end Qatlib.Papers.KnottedLight08.CurlEigenstate
