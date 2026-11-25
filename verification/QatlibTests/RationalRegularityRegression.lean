/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalPowerMaxwell
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanConformalCharges
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPhysicalTori
public import Qatlib.Papers.KnotLight13.TorusFamily.HelicityTransport
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanRobinson
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanZeroBands
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanOrbitClock
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanCoreLinks
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPolynomialLinks
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPolynomialFibration
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanLevelRegularity
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanSphereField
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanQuotientPeriod
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPhysicalLinearFlow

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Instances.AddCircle.Defs

/-! Regression consumers for the smoothness and decay results of the rational
Bateman field. The witness point (1, 2, 3, 4) is nondegenerate: the decay
bound is instantiated numerically and checked against the actual field value,
the smoothness theorems are instantiated, and both the energy-density identity
and its spatial integrability are specialized at positive time. -/

@[expose] public section
set_option autoImplicit false

open Qatlib.Papers.KnotLight13.TorusFamily (radialAux rationalAlpha rationalBeta
  pairDenominator pair_denominator_pos)
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3)
open Qatlib.Papers.KnotLight13.TorusFamily
open MeasureTheory

-- The field entries are smooth in all four spacetime coordinates.
example (j : Fin 3) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      rationalField p.1 p.2.1 p.2.2.1 p.2.2.2 j) :=
  contDiff_rationalField j

example :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      rationalAlpha p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  contDiff_rationalAlpha

example :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      rationalBeta p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  contDiff_rationalBeta

-- The denominator lower bound at the witness point, where the auxiliary
-- radius is -1 and the pair denominator is 65.
example : 4 * (1 + (4 : ℝ) ^ 2) ^ 2 * pairDenominator 1 2 3 4 ≥
    (1 + 1 ^ 2 + 2 ^ 2 + 3 ^ 2) ^ 2 :=
  pairDenominator_lower 1 2 3 4

-- The pair denominator evaluates explicitly to 65 at the witness point.
example : pairDenominator 1 2 3 4 = 65 := by
  norm_num [pairDenominator, radialAux]

-- The decay bound instantiated at the witness point, with the right-hand
-- side evaluated to a number.
example (j : Fin 3) :
    Complex.normSq (rationalField 1 2 3 4 j) ≤
      14745600 * (1 + (4 : ℝ) ^ 2) ^ 12 / (1 + 1 ^ 2 + 2 ^ 2 + 3 ^ 2) ^ 4 :=
  normSq_rationalField_le 1 2 3 4 j

-- The energy density identity, instantiated.
example :
    ∑ j : Fin 3, Complex.normSq (rationalField 1 2 3 4 j) =
      dot3 (fun j => (rationalField 1 2 3 4 j).re) (fun j => (rationalField 1 2 3 4 j).re) +
      dot3 (fun j => (rationalField 1 2 3 4 j).im) (fun j => (rationalField 1 2 3 4 j).im) :=
  rationalField_energy_density 1 2 3 4

example :
    Integrable (fun s : EuclideanSpace ℝ (Fin 3) =>
      ∑ j : Fin 3, Complex.normSq (rationalField (s 0) (s 1) (s 2) 4 j)) volume :=
  rationalField_energy_integrable 4

example :
    Integrable (fun s : EuclideanSpace ℝ (Fin 3) =>
      ∑ j : Fin 3, Complex.normSq (rationalPowerField 2 3 (s 0) (s 1) (s 2) 4 j)) volume :=
  rationalPowerField_energy_integrable 2 3 4

example :
    cartesianCurl (fun s => rationalPowerField 2 3 s.1 s.2.1 s.2.2.1 s.2.2.2) (1, 2, 3, 4) 0 =
      Complex.I * spaceTimePartial
        (fun s => rationalPowerField 2 3 s.1 s.2.1 s.2.2.1 s.2.2.2 0) (1, 2, 3, 4) 3 :=
  maxwell_rational_power_field 2 3 1 2 3 4 0

example :
    cartesianDivergence (fun s => rationalPowerField 2 3 s.1 s.2.1 s.2.2.1 s.2.2.2)
      (1, 2, 3, 4) = 0 :=
  rational_power_field_divergence_free 2 3 1 2 3 4

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.maxwell_rational_power_field
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.rational_power_field_divergence_free
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.rationalPowerField_energy_integrable


/-- The two real gauges give the actual curls at a nonzero time and
at a point of the nontrivial `(2,3)` family. -/
example :
    batemanRealCurl (batemanElectricPotential 2 3 4) (1, 2, 3) 0 =
        (rationalPowerField 2 3 1 2 3 4 0).re ∧
    batemanRealCurl (batemanMagneticPotential 2 3 4) (1, 2, 3) 2 =
        (rationalPowerField 2 3 1 2 3 4 2).im :=
  ⟨batemanRealCurl_electric 2 3 1 2 3 4 0, batemanRealCurl_magnetic 2 3 1 2 3 4 2⟩

/-- The true initial density is strictly positive at a point where both
sphere coordinates are nonzero. -/
example : 0 < batemanElectricHelicityDensity 2 3 0 (1 / 2, 0, 0) := by
  rw [batemanElectricHelicityDensity_zero_time]
  norm_num [rational_alpha_stereographic_zero_time, rational_beta_stereographic_zero_time,
    Complex.normSq_apply, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]

/-- A zero power produces a zero field and zero helicity density. -/
example (t x y z : ℝ) : batemanElectricHelicityDensity 0 3 t (x, y, z) = 0 := by
  simp [batemanElectricHelicityDensity, rationalPowerField_eq, rationalPowerFactor, dot3]

/-- The whole-space integral of the magnetic density at negative time
equals the electric integral at positive time. -/
example : Integrable (batemanMagneticHelicityDensity 2 3 (-2)) ∧
    (∫ s : ℝ × ℝ × ℝ, batemanMagneticHelicityDensity 2 3 (-2) s) =
      ∫ s : ℝ × ℝ × ℝ, batemanElectricHelicityDensity 2 3 4 s := by
  obtain ⟨hm, h⟩ := integrable_and_conserved_batemanMagneticHelicity 2 3 (-2)
  exact ⟨hm, h.trans (integrable_and_conserved_batemanElectricHelicity 2 3 4).2.symm⟩

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanRealCurl_electric
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanRealCurl_magnetic
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.rationalPowerField_energy_density_zero_time
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanElectricHelicityDensity_zero_time
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.integrable_and_conserved_batemanElectricHelicity
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.integrable_and_conserved_batemanMagneticHelicity

/-- Normalizing the physical `(2,3)` field by its nonzero initial energy
gives the same helicity one fifth for the actual electric and magnetic
densities at positive time. -/
example :
    (∫ s : ℝ × ℝ × ℝ, batemanElectricHelicityDensity 2 3 4 s) / batemanInitialEnergy 2 3 = 1 / 5 ∧
    (∫ s : ℝ × ℝ × ℝ, batemanMagneticHelicityDensity 2 3 4 s) / batemanInitialEnergy 2 3 = 1 / 5 := by
  have h := bateman_normalized_helicities (p := 2) (q := 3) (by norm_num) (by norm_num) 4
  norm_num at h
  exact h

/-- At the Hopf member of the family, the energy-normalized magnetic
helicity on a negative-time slice is one half. -/
example :
    (∫ s : ℝ × ℝ × ℝ, batemanMagneticHelicityDensity 1 1 (-3) s) / batemanInitialEnergy 1 1 = 1 / 2 := by
  have h := (bateman_normalized_helicities (p := 1) (q := 1) (by norm_num) (by norm_num) (-3)).2
  norm_num at h
  exact h

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanInitialEnergy_pos
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.bateman_normalized_helicities

/-- Both physical helicities normalized by the energy on their own
positive-time slice have the value one fifth for the (2,3) field. -/
example :
    (∫ s : ℝ × ℝ × ℝ, batemanElectricHelicityDensity 2 3 4 s) / batemanEnergy 2 3 4 = 1 / 5 ∧
    (∫ s : ℝ × ℝ × ℝ, batemanMagneticHelicityDensity 2 3 4 s) / batemanEnergy 2 3 4 = 1 / 5 := by
  have h := bateman_helicities_div_energy (p := 2) (q := 3) (by norm_num) (by norm_num) 4
  norm_num at h
  exact h

/-- The (2,3) field has the same total energy on opposite time slices. -/
example : batemanEnergy 2 3 (-4) = batemanEnergy 2 3 4 := by
  rw [(integrable_and_conserved_batemanEnergy 2 3 (-4)).2,
    (integrable_and_conserved_batemanEnergy 2 3 4).2]

/-- At unit time the spatial Jacobian at the ray from the origin is five. -/
example : LinearMap.det (fderiv ℝ (batemanRay 1) (0, 0, 0)).toLinearMap = 5 := by
  rw [det_batemanRay_eq_normSq_multiplier]
  norm_num [batemanRayMultiplier, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.det_batemanRay_eq_normSq_multiplier
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.rationalPowerField_batemanRay
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.integrable_and_conserved_batemanEnergy
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.bateman_helicities_div_energy

/-- The axial momentum and spatial conformal charge are negative, while
the angular momentum uses the positive sign of the published convention. -/
example :
    batemanCharge (.momentum 2) 2 3 4 / batemanEnergy 2 3 4 = -(2 / 5) ∧
    batemanCharge (.angularMomentum 2) 2 3 (-4) / batemanEnergy 2 3 (-4) = 3 / 5 ∧
    batemanCharge (.conformalSpace 2) 2 3 4 / batemanEnergy 2 3 4 = -(2 / 5) := by
  have hm := batemanCharge_div_energy (.momentum 2) (p := 2) (q := 3) (by norm_num) (by norm_num) 4
  have hl := batemanCharge_div_energy (.angularMomentum 2) (p := 2) (q := 3) (by norm_num) (by norm_num) (-4)
  have hk := batemanCharge_div_energy (.conformalSpace 2) (p := 2) (q := 3) (by norm_num) (by norm_num) 4
  norm_num [batemanNormalizedCharge] at hm hl hk
  exact ⟨hm, hl, hk⟩

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.integrable_and_conserved_batemanCharge
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanCharge_div_energy

/-- At unit time, the supplement's printed expression has zero axial
integral for the (2,3) field, whereas its true charge is nonzero. -/
example :
    (∫ s : ℝ × ℝ × ℝ, printedBatemanSpatialConformalDensity 2 2 3 1 s) = 0 ∧
    batemanCharge (.conformalSpace 2) 2 3 1 ≠ 0 := by
  have hpos : 0 < batemanEnergy 2 3 0 :=
    batemanEnergy_pos (p := 2) (q := 3) (by norm_num) (by norm_num) 0
  have hm := batemanCharge_div_energy (.momentum 2) (p := 2) (q := 3) (by norm_num) (by norm_num) 0
  have hk := batemanCharge_div_energy (.conformalSpace 2) (p := 2) (q := 3) (by norm_num) (by norm_num) 0
  norm_num [batemanNormalizedCharge] at hm hk
  have hm' := (div_eq_iff hpos.ne').mp hm
  have hk' := (div_eq_iff hpos.ne').mp hk
  constructor
  · rw [(integrable_and_integral_printedBatemanSpatialConformalDensity 2 2 3 1).2, hm', hk']
    ring
  · rw [(integrable_and_conserved_batemanCharge (.conformalSpace 2) 2 3 1).2, hk']
    exact mul_ne_zero (by norm_num) hpos.ne'

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.integrable_and_integral_printedBatemanSpatialConformalDensity

/-- The real level label of the (2,3) field has a nonzero actual
spatial derivative at this initial point. -/
example : ((poweredProductGradient 2 3 (1 / 2) 0 0 0 0).re) = -(384 / 3125) := by
  simp only [poweredProductGradient, alphaPowerGradient_eq, betaPowerGradient_eq,
    rational_alpha_stereographic_zero_time, rational_beta_stereographic_zero_time]
  norm_num [alphaGradient, betaGradient, alphaGradientNumerators, betaGradientNumerators,
    alphaXNumerator, betaXNumerator, betaReducedNumerator, alphaCommonFactor, complexDenominator,
    radialAux, Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, pow_succ]

/-- Both true field components are tangent to the corresponding level
surfaces for the nontrivial power pair at a nonzero time. -/
example :
    dot3 (fun j => (rationalPowerField 2 3 1 2 3 4 j).im)
        (fun j => (poweredProductGradient 2 3 1 2 3 4 j).re) = 0 ∧
      dot3 (fun j => (rationalPowerField 2 3 1 2 3 4 j).re)
        (fun j => (poweredProductGradient 2 3 1 2 3 4 j).im) = 0 :=
  powered_field_line_levels 2 3 1 2 3 4

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.poweredProductGradient_eq_deriv
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.powered_field_line_levels
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.poweredProductLabel_batemanRay

/-- The positive magnetic core of unequal exponents has the physical
peak label and nonzero fields at a nonzero time. -/
example : let s := poweredPhysicalCoreParam 2 3 4 1 1
    (batemanPoweredLabel 2 3 4 s).re = poweredPeakAmplitude 2 3 ∧
    Complex.normSq (rationalAlpha s.1 s.2.1 s.2.2 4) = 2 / 5 ∧
    (fun j => (rationalPowerField 2 3 s.1 s.2.1 s.2.2 4 j).im) ≠ 0 := by
  let s := poweredPhysicalCoreParam 2 3 4 1 1
  have hp : 0 < (2 : ℕ) := by decide
  have hq : 0 < (3 : ℕ) := by decide
  have hcop : Nat.Coprime 2 3 := by decide
  have hparam := (poweredPhysicalCoreParam_bijective hp hq hcop 4 1).2
  have hs : s ∈ poweredPhysicalCore 2 3 4 1 :=
    hparam ▸ Set.mem_range_self (1 : Circle)
  have hreal := (mem_poweredPhysicalCore_iff_real hp hq 4
    (phase := 1) (by simp) s).1 hs
  have hr := (poweredProductLabel_real_extreme hp hq s.1 s.2.1 s.2.2 4 (by
    change |(batemanPoweredLabel 2 3 4 s).re| = _
    rw [show (batemanPoweredLabel 2 3 4 s).re = poweredPeakAmplitude 2 3 by simpa using hreal,
      abs_of_pos (poweredPeakAmplitude_pos hp hq)])).2
  refine ⟨by simpa using hreal, ?_, (fields_nonzero_on_poweredPhysicalCore hp hq 4 hs).2⟩
  norm_num [poweredPeakRadius] at hr ⊢
  exact hr

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.magnetic_line_preserves_label
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.electric_line_preserves_label
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.poweredPhysicalCoreHomeomorph
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanSliceHomeomorph_image_poweredPhysicalCore
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.magnetic_line_mapsTo_poweredPhysicalCore

/-- For the unequally powered field, the prescribed axial angle turns
a positive magnetic-core label into the negative electric-core label. -/
example :
    let s := poweredPhysicalCoreParam 2 3 4 1 1
    let r := batemanAxialRotation (Real.pi / 6) s
    (batemanPoweredLabel 2 3 4 r).im = -poweredPeakAmplitude 2 3 := by
  let s := poweredPhysicalCoreParam 2 3 4 1 1
  let r := batemanAxialRotation (Real.pi / 6) s
  change (batemanPoweredLabel 2 3 4 r).im = _
  have hmem : s ∈ poweredPhysicalCore 2 3 4 1 :=
    (poweredPhysicalCoreParam_bijective (p := 2) (q := 3) (by decide) (by decide) (by decide) 4 1).2 ▸
      Set.mem_range_self (1 : Circle)
  have hval : batemanPoweredLabel 2 3 4 s = (poweredPeakAmplitude 2 3 : ℂ) := by
    change batemanPoweredLabel 2 3 4 s = (poweredPeakAmplitude 2 3 : ℂ) * ((1 : Circle) : ℂ) at hmem
    simpa using hmem
  have hphase : batemanAxialPhase (Real.pi / 6) ^ 3 = -Complex.I := by
    have hθ : Real.pi / (2 * ((3 : ℕ) : ℝ)) = Real.pi / 6 := by norm_num
    simpa only [hθ] using batemanAxialPhase_special (q := 3) (by decide)
  have hrot := poweredProductLabel_axialRotation 2 3 (Real.pi / 6) s.1 s.2.1 s.2.2 4
  change batemanPoweredLabel 2 3 4 r = batemanAxialPhase (Real.pi / 6) ^ 3 *
    batemanPoweredLabel 2 3 4 s at hrot
  rw [hrot, hphase, hval]
  simp [Complex.mul_im]

/-- Actual vector components obey electric–magnetic duality at the
prescribed angle and a nonzero time for the powered field. -/
example :
    let r := batemanAxialRotation (Real.pi / 6) (1, 2, 3)
    (fun j => (rationalPowerField 2 3 r.1 r.2.1 r.2.2 4 j).re) =
      axialRotateVector (Real.cos (Real.pi / 6)) (Real.sin (Real.pi / 6))
        (fun j => (rationalPowerField 2 3 1 2 3 4 j).im) := by
  have h := rationalPowerField_axialDuality 2 (q := 3) (by decide) 1 2 3 4
  have hθ : Real.pi / (2 * ((3 : ℕ) : ℝ)) = Real.pi / 6 := by norm_num
  simpa only [hθ] using h.1

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.rationalPowerField_axialDuality
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.poweredProductLabel_axialRotation

/-- At half the peak label, both physical levels of the (2,3) field are
whole tori, including at nonzero time and on the negative electric branch. -/
example :
    Nonempty ((Circle × Circle) ≃ₜ
      ↥(poweredPhysicalRealLevel 2 3 4 (poweredPeakAmplitude 2 3 / 2))) ∧
    Nonempty ((Circle × Circle) ≃ₜ
      ↥(poweredPhysicalImagLevel 2 3 (-4) (-(poweredPeakAmplitude 2 3 / 2)))) := by
  have hp : 0 < (2 : ℕ) := by decide
  have hq : 0 < (3 : ℕ) := by decide
  have hcop : Nat.Coprime 2 3 := by decide
  have ha := poweredPeakAmplitude_pos hp hq
  have hn := (half_pos ha).ne'
  have hc : |poweredPeakAmplitude 2 3 / 2| < poweredPeakAmplitude 2 3 := by
    rw [abs_of_pos (half_pos ha)]
    exact half_lt_self ha
  exact ⟨⟨poweredPhysicalRealLevelHomeomorph hp hq hcop 4 hn hc⟩,
    ⟨poweredPhysicalImagLevelHomeomorph hp hq hcop (-4) (neg_ne_zero.mpr hn) (by rwa [abs_neg])⟩⟩

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.poweredPhysicalRealLevelHomeomorph
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.poweredPhysicalImagLevelHomeomorph
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.poweredReal_superlevel_iff_radialDisk

/-- At a nonzero time the spatial ray derivative transports a nonzero
magnetic vector on the physical (2,3) core, with positive scale. -/
example :
    let s := poweredPhysicalCoreParam 2 3 0 1 1
    let y := batemanRay 4 s
    let D := fderiv ℝ (batemanRay 4) s
    D (batemanMagneticVector 2 3 0 s) = LinearMap.det D.toLinearMap • batemanMagneticVector 2 3 4 y ∧
    D (batemanMagneticVector 2 3 0 s) ≠ 0 := by
  let s := poweredPhysicalCoreParam 2 3 0 1 1
  let y := batemanRay 4 s
  let D := fderiv ℝ (batemanRay 4) s
  have hs : s ∈ poweredPhysicalCore 2 3 0 1 :=
    (poweredPhysicalCoreParam_bijective (p := 2) (q := 3) (by decide) (by decide) (by decide) 0 1).2 ▸
      Set.mem_range_self (1 : Circle)
  have hy : y ∈ poweredPhysicalCore 2 3 4 1 := by
    rw [← batemanSliceHomeomorph_image_poweredPhysicalCore]
    exact Set.mem_image_of_mem _ hs
  have hB : batemanMagneticVector 2 3 4 y ≠ 0 := by
    unfold batemanMagneticVector
    exact fun h => (fields_nonzero_on_poweredPhysicalCore (by decide) (by decide) 4 hy).2
      (batemanCartesianCoordinates.symm.injective (h.trans (map_zero _).symm))
  have hD := (batemanRay_transports_vectors 2 3 4 s).2
  exact ⟨hD, hD.symm ▸ smul_ne_zero (det_bateman_ray_pos 4 s).ne' hB⟩

/-- A whole magnetic field-line parametrization has the same orientation
after transport to a negative physical time. -/
example (γ : ℝ → ℝ × ℝ × ℝ) (hγ : IsOrientedFieldLine (batemanMagneticVector 2 3 0) γ Set.univ) :
    IsOrientedFieldLine (batemanMagneticVector 2 3 (-4)) (batemanRay (-4) ∘ γ) Set.univ :=
  (batemanRay_orientedFieldLines_iff 2 3 (-4) γ Set.univ).2.mpr hγ

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanRay_transports_vectors
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanRay_orientedFieldLines_iff

/-- The shear identity gives a nonzero scalar expansion in a genuine
transverse direction at an off-axis point and nonzero physical time. -/
example :
    let u : ℝ × ℝ × ℝ := (1, -1, 0)
    let s : ℝ × ℝ × ℝ := (1, 0, 2)
    2 * dot3 (batemanCartesianCoordinates u)
        (batemanCartesianCoordinates (fderiv ℝ (batemanRayDirection 1) s u)) = -(8 / 3) := by
  let u : ℝ × ℝ × ℝ := (1, -1, 0)
  let s : ℝ × ℝ × ℝ := (1, 0, 2)
  have horth : dot3 (batemanCartesianCoordinates u) (batemanCartesianCoordinates (batemanRayDirection 1 s)) = 0 := by
    rw [batemanRayDirection, LinearEquiv.apply_symm_apply, poyntingFlow_eq_spinorVelocity]
    norm_num [u, s, dot3, batemanCartesianCoordinates, spinorVelocity, spinorAxis, alphaCommonFactor,
      betaReducedNumerator, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  have h := batemanRayDirection_shearFree 1 s u u horth horth
  rw [← two_mul] at h
  refine h.trans ?_
  norm_num [s, u, dot3, batemanCartesianCoordinates]

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanRayDirection_shearFree

/-- At nonzero time the shared zero locus contains the expanded
equatorial circle and the axis, and excludes points off both. -/
example :
    let Z := poweredPhysicalRealLevel 2 3 (3 / 4) 0 ∩ poweredPhysicalImagLevel 2 3 (3 / 4) 0
    (5 / 4, 0, 0) ∈ Z ∧ (0, 0, 7) ∈ Z ∧ (1, 0, 1) ∉ Z := by
  have hp : 0 < (2 : ℕ) := by decide
  have hq : 0 < (3 : ℕ) := by decide
  dsimp only
  rw [mem_poweredPhysicalZeroLevels_iff hp hq, mem_poweredPhysicalZeroLevels_iff hp hq,
    mem_poweredPhysicalZeroLevels_iff hp hq]
  norm_num

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.mem_poweredPhysicalZeroLevels_iff
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.poweredPhysicalZeroLevels_closed_noncompact

/-- At the same equatorial point, increasing the first exponent from
one to two creates an actual field zero, even when the second is one. -/
example :
    (fun j => (rationalPowerField 2 1 (5 / 4) 0 0 (3 / 4) j).re) = 0 ∧
      (fun j => (rationalPowerField 1 2 (5 / 4) 0 0 (3 / 4) j).im) ≠ 0 := by
  constructor
  · apply (poweredFields_zero_iff (p := 2) (q := 1) (by decide) (by decide) (5 / 4) 0 0 (3 / 4)).1.mpr
    norm_num
  · intro h
    have hz := (poweredFields_zero_iff (p := 1) (q := 2) (by decide) (by decide) (5 / 4) 0 0 (3 / 4)).2.mp h
    norm_num at hz

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.poweredFields_zero_iff

/-- The global clock has a non-unit derivative at the origin of a
nonconstant reference curve, at a nonzero physical time. -/
example : HasDerivAt (batemanOrbitClock 2 (fun u => (u, 0, 0))) 17 0 := by
  have h := hasDerivAt_batemanOrbitClock 2 (γ := fun u => (u, 0, 0)) (by fun_prop) 0
  apply h.congr_deriv
  rw [det_batemanRay_eq_normSq_multiplier]
  norm_num [batemanRayMultiplier, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

/-- Positive global reparametrization transports the entire magnetic
orbit of the (2,3) field to a negative physical time. -/
example {γ : ℝ → ℝ × ℝ × ℝ} (hγ : IsIntegralCurve γ (fun _ => batemanMagneticVector 2 3 0)) :
    ∃ e : ℝ ≃o ℝ, IsIntegralCurve (batemanRay (-4) ∘ γ ∘ e) (fun _ => batemanMagneticVector 2 3 (-4)) ∧
      Set.range (batemanRay (-4) ∘ γ ∘ e) = batemanRay (-4) '' Set.range γ :=
  batemanRay_magneticIntegralCurve 2 3 (-4) hγ

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.det_batemanRay_uniform_bounds
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanRay_electricIntegralCurve
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanRay_magneticIntegralCurve

/-- At physical time two, transport of the equatorial unit circle
lengthens its parameter period by exactly five. -/
example :
    let γ : ℝ → ℝ × ℝ × ℝ := fun u => (Real.cos u, Real.sin u, 0)
    let hγ : Continuous γ := by fun_prop
    Function.Periodic (batemanRay 2 ∘ γ ∘ (batemanOrbitClockOrderIso 2 hγ).symm)
      (10 * Real.pi) := by
  let γ : ℝ → ℝ × ℝ × ℝ := fun u => (Real.cos u, Real.sin u, 0)
  have hγ : Continuous γ := by fun_prop
  have hper : Function.Periodic γ (2 * Real.pi) := fun u =>
    Prod.ext (Real.cos_periodic u) (Prod.ext (Real.sin_periodic u) rfl)
  have hDet (u : ℝ) : LinearMap.det (fderiv ℝ (batemanRay 2) (γ u)).toLinearMap = 5 := by
    rw [det_batemanRay_eq_normSq_multiplier]
    simp only [γ, batemanRayMultiplier, Real.cos_sq_add_sin_sq]
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  have hC : batemanOrbitClock 2 γ (2 * Real.pi) = 10 * Real.pi := by
    simp only [batemanOrbitClock, hDet, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  have h := (batemanRay_reparametrized_periodic 2 hγ (by positivity : 0 < 2 * Real.pi) hper).2
  rwa [hC] at h

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanRay_periodicMagneticIntegralCurve
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanRay_periodicElectricIntegralCurve

/-- The signed magnetic cores for the (4,6) field contain two embedded
circle components for each sign at a nonzero physical time. -/
example :
    Nonempty (((Fin 2 × Circle) ⊕ (Fin 2 × Circle)) ≃ₜ
      ↥(poweredPhysicalCore 4 6 3 1 ∪ poweredPhysicalCore 4 6 3 (-1))) := by
  have h : (1 : Circle) ≠ -1 := fun h =>
    Circle.coe_ne_zero (1 : Circle) (neg_eq_self.mp (congrArg (fun c : Circle => (c : ℂ)) h.symm))
  exact ⟨poweredPhysicalCorePairComponents (p := 4) (q := 6) (by decide) (by decide) 3 h⟩

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.poweredPhysicalCoreGcdComponents
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.poweredPhysicalCorePairComponents

/-- The (4,6) polynomial has two spatial link components at a nonzero
time, and the actual Bateman chart identifies both with its sphere locus. -/
example :
    Nonempty ((Fin 2 × Circle) ≃ₜ ↥(spatialKnotAt 4 6 (-3))) ∧
      Nonempty (↥(spatialKnotAt 4 6 (-3)) ≃ₜ ↥(unitTorusKnotLocus 4 6)) :=
  ⟨⟨spatialKnotAt_gcd_components (p := 4) (q := 6) (by decide) (by decide) (-3)⟩,
    ⟨spatialKnotAt_sphere_homeomorph (p := 4) (q := 6) (by decide) (by decide) (-3)⟩⟩

/-- The two components are disjoint twists of the (2,3) knot,
with distinct unit phases. -/
example : Disjoint (twistedSpatialKnotAt 2 3 (-3) 1) (twistedSpatialKnotAt 2 3 (-3) (-1)) := by
  have h : (1 : Circle) ≠ -1 := fun h =>
    Circle.coe_ne_zero (1 : Circle) (neg_eq_self.mp (congrArg (fun c : Circle => (c : ℂ)) h.symm))
  exact twistedSpatialKnotAt_disjoint (by decide) (by decide) (-3) h

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.spatialKnotAt_gcd_components
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.spatialKnotAt_sphere_homeomorph
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.unitTorusKnotLocus_gcd_components

/-- For the two-component (4,6) polynomial, the phase map is onto and
locally a product over the negative real phase. -/
example :
    Function.Surjective (torusPolynomialPhase 4 6) ∧
      ∃ U : Set Circle, IsOpen U ∧ (-1 : Circle) ∈ U ∧
        ∃ h : ↥(torusPolynomialPhase 4 6 ⁻¹' U) ≃ₜ
            (↥U × {z : ↥(torusPolynomialExterior 4 6) // torusPolynomialPhase 4 6 z = 1}),
          ∀ z, (h z).1.val = torusPolynomialPhase 4 6 z.val :=
  ⟨torusPolynomialPhase_surjective (by decide) (by decide),
    torusPolynomialPhase_locally_product (by decide) (by decide) (-1)⟩

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.torusPolynomialPhase_surjective
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.torusPolynomialPhase_locally_product

/-- At an interior real level of the (2,3) field where the axial
derivative vanishes, the radial derivative still gives regularity. -/
example :
    let s : ℝ × ℝ × ℝ := (1 / 2, 0, 0)
    let f := fun x => (batemanPoweredLabel 2 3 0 x).re
    let K := (fderiv ℝ f s).ker
    (batemanPoweredLabel 2 3 0 s).im = 0 ∧
      fderiv ℝ f s ≠ 0 ∧
      ∃ e : OpenPartialHomeomorph (ℝ × ℝ × ℝ) (ℝ × K),
        s ∈ e.source ∧ (e s).1 = 576 / 3125 := by
  let s : ℝ × ℝ × ℝ := (1 / 2, 0, 0)
  have hz : batemanPoweredLabel 2 3 0 s = ((576 / 3125 : ℝ) : ℂ) := by
    change rationalAlpha (1 / 2) 0 0 0 ^ 2 * rationalBeta (1 / 2) 0 0 0 ^ 3 = _
    rw [rational_alpha_stereographic_zero_time, rational_beta_stereographic_zero_time]
    apply Complex.ext <;>
      norm_num [Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, pow_succ]
  have hR : (batemanPoweredLabel 2 3 0 s).re = 576 / 3125 := by rw [hz, Complex.ofReal_re]
  have hp : 0 < (2 : ℕ) := by decide
  have hq : 0 < (3 : ℕ) := by decide
  have hn : (batemanPoweredLabel 2 3 0 s).re ≠ 0 := by
    rw [hR]
    norm_num
  have hc : |(batemanPoweredLabel 2 3 0 s).re| < poweredPeakAmplitude 2 3 := by
    have hsq : |(batemanPoweredLabel 2 3 0 s).re| ^ 2 < poweredPeakAmplitude 2 3 ^ 2 := by
      rw [hR, poweredPeakAmplitude_sq hp hq, sq_abs]
      norm_num [poweredRadiusProfile, poweredPeakRadius]
    by_contra! h
    exact (not_le_of_gt hsq) (pow_le_pow_left₀ (poweredPeakAmplitude_pos hp hq).le h 2)
  obtain ⟨e, he, heF, _, _⟩ := batemanRealLabel_localCoordinates hp hq 0 s hn hc
  exact ⟨by rw [hz, Complex.ofReal_im], fderiv_batemanRealLabel_ne_zero hp hq 0 s hn hc,
    e, he, (heF s).trans hR⟩

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.fderiv_batemanRealLabel_ne_zero
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.fderiv_batemanImagLabel_ne_zero
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanRealLabel_localCoordinates
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanImagLabel_localCoordinates

/-- The (2,3) magnetic field at a nonzero time reaches the same
normalized sphere field as on the initial slice. Its first component
at this point has nonzero imaginary part. -/
example :
    let x : ℝ × ℝ × ℝ := (1 / 2, 0, 0)
    let y := batemanRay (-2) x
    let J := LinearMap.det (fderiv ℝ (batemanRay (-2)) x).toLinearMap
    (fderiv ℝ (batemanPairAt (-2)) y (batemanMagneticVector 2 3 (-2) y)).1 =
      (batemanStereoScale x ^ 3 / J : ℝ) • (Complex.I * (1152 / 625 : ℂ)) := by
  let x : ℝ × ℝ × ℝ := (1 / 2, 0, 0)
  have h₁ : (initialBatemanPair x).1 = ((-3 / 5 : ℝ) : ℂ) := by
    change rationalAlpha (1 / 2) 0 0 0 = _
    rw [rational_alpha_stereographic_zero_time]
    apply Complex.ext <;> norm_num [Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h₂ : (initialBatemanPair x).2 = ((4 / 5 : ℝ) : ℂ) := by
    change rationalBeta (1 / 2) 0 0 0 = _
    rw [rational_beta_stereographic_zero_time]
    apply Complex.ext <;> norm_num [Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im]
  have hw : batemanPairAt (-2) (batemanRay (-2) x) = (((-3 / 5 : ℝ) : ℂ), ((4 / 5 : ℝ) : ℂ)) :=
    (batemanPairAt_batemanRay (-2) x).trans (Prod.ext h₁ h₂)
  have h := congrArg Prod.fst (fderiv_batemanPairAt_transported_fields 2 3 (-2) x).2
  dsimp only at h ⊢
  rw [h, hw]
  unfold batemanSphereMagnetic batemanSphereElectric batemanSphereFactor
  push_cast
  norm_num [map_ofNat, x]

/-- At the (2,3) turning point the squared radial velocity vanishes,
while the imaginary product decreases at the explicitly computed rate. -/
example :
    let w₀ : ℂ × ℂ := (((-3 / 5 : ℝ) : ℂ), ((4 / 5 : ℝ) : ℂ))
    let V := batemanSphereMagnetic 2 3 w₀
    let w := fun u : ℝ => w₀ + u • V
    deriv (fun u => (Complex.normSq (w u).1, ((w u).1 ^ 2 * (w u).2 ^ 3).im)) 0 =
      (0, -13824 / 78125) := by
  let w₀ : ℂ × ℂ := (((-3 / 5 : ℝ) : ℂ), ((4 / 5 : ℝ) : ℂ))
  let V := batemanSphereMagnetic 2 3 w₀
  let w := fun u : ℝ => w₀ + u • V
  have hw₀ : w 0 = w₀ := by simp [w]
  have hw : HasDerivAt w (batemanSphereMagnetic 2 3 (w 0)) 0 := by
    rw [hw₀]
    have hd := (hasDerivAt_const (0 : ℝ) w₀).add ((hasDerivAt_id (0 : ℝ)).smul_const V)
    change HasDerivAt w (0 + (1 : ℝ) • V) 0 at hd
    simpa only [zero_add, one_smul] using hd
  have hr := hasDerivAt_batemanSphereMagnetic_radius (p := 2) (q := 3) (by decide) (by decide) hw
  have hi := hasDerivAt_batemanSphereMagnetic_imaginary (p := 2) (q := 3) (by decide) (by decide) hw
  change deriv (fun u => (Complex.normSq (w u).1, ((w u).1 ^ 2 * (w u).2 ^ 3).im)) 0 = _
  rw [(HasDerivAt.prodMk hr hi).deriv, hw₀]
  norm_num [w₀, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_succ]

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.fderiv_batemanPairAt_transported_fields
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanSphereMagnetic_phase
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanSphereMagnetic_quotient_deriv_ne_zero

/-- The Hopfion parameters make the quotient rotate at speed two.
At the real level 1/4, its lap therefore takes time π in the
normalized sphere clock. -/
example :
    ∃ (h₀ : (1 / 4 : ℝ) ≠ 0) (hc : |(1 / 4 : ℝ)| < poweredPeakAmplitude 1 1),
      batemanMagneticQuotientPeriod (by decide) (by decide) h₀ hc = Real.pi := by
  have h₀ : (1 / 4 : ℝ) ≠ 0 := by norm_num
  have hpeak : poweredPeakAmplitude 1 1 = 1 / 2 := by
    unfold poweredPeakAmplitude
    rw [show poweredRadiusProfile 1 1 (poweredPeakRadius 1 1) = (1 / 2 : ℝ) ^ 2 by
      norm_num [poweredRadiusProfile, poweredPeakRadius]]
    exact Real.sqrt_sq (by norm_num)
  have hc : |(1 / 4 : ℝ)| < poweredPeakAmplitude 1 1 := by rw [hpeak]; norm_num
  refine ⟨h₀, hc, ?_⟩
  let e := batemanMagneticOvalHomeomorph (p := 1) (q := 1) (by decide) (by decide) h₀ hc
  open scoped Interval ComplexConjugate in
  change (∫ v in (0 : ℝ)..(2 * Real.pi),
    (batemanMagneticOvalSpeed 1 1 (e.symm (Circle.exp v)).val)⁻¹) = Real.pi
  have hSpeed (z : ↥(batemanMagneticOval 1 1 (1 / 4))) :
      batemanMagneticOvalSpeed 1 1 z.val = 2 := by
    have hV : batemanMagneticOvalVector 1 1 z.val = 2 * Complex.I * z.val := by
      apply Complex.ext <;>
        norm_num [batemanMagneticOvalVector, Complex.mul_re, Complex.mul_im,
          Complex.add_re, Complex.add_im]
    have hN : Complex.normSq z.val ≠ 0 := (Complex.normSq_pos.mpr
      (batemanMagneticOval_ne_zero (by decide) (by decide) hc z.property)).ne'
    unfold batemanMagneticOvalSpeed
    rw [hV]
    open scoped ComplexConjugate in
    have he : (conj z.val * (2 * Complex.I * z.val)).im = 2 * Complex.normSq z.val := by
      simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
      ring
    rw [he, mul_div_cancel_right₀ _ hN]
  simp_rw [hSpeed]
  rw [intervalIntegral.integral_const]
  simp [smul_eq_mul]
  ring

/-- At the peak itself the centered quotient contains zero. -/
example : (0 : ℂ) ∈ batemanMagneticOval 1 1 (poweredPeakAmplitude 1 1) := by
  have hk := poweredPeakRadius_mem (p := 1) (q := 1) (by decide) (by decide)
  refine ⟨by simpa only [Complex.zero_re, zero_add] using ⟨hk.1.le, hk.2.le⟩, ?_⟩
  simpa only [Complex.zero_re, Complex.zero_im, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using
    poweredPeakAmplitude_sq (p := 1) (q := 1) (by decide) (by decide)

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanMagneticOvalHomeomorph
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.hasDerivAt_batemanMagneticOvalPhase
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanMagneticQuotient_periodic

/-- A concrete Hopfion orbit stays on the nondegenerate real level
`-12/25` and consumes the periodic-or-dense theorem on a full trajectory. -/
private theorem exists_hopfionSphereOrbit :
    let c : ℝ := -12 / 25
    ∃ w : ℝ → ℂ × ℂ,
      w 0 = (((-3 / 5 : ℝ) : ℂ), ((4 / 5 : ℝ) : ℂ)) ∧
      (∀ t, HasDerivAt w (batemanSphereMagnetic 1 1 (w t)) t) ∧
      (∀ t, w t ∈ poweredSphereRealLevel 1 1 c) ∧
      ((∃ T : ℝ, 0 < T ∧ Function.Periodic w T) ∨
        closure (Set.range w) = poweredSphereRealLevel 1 1 c) := by
  let a : ℝ := -3 / 5
  let b : ℝ := 4 / 5
  let c : ℝ := -12 / 25
  let w : ℝ → ℂ × ℂ := fun t =>
    (⟨a * Real.cos t, -b * Real.sin t⟩, ⟨b * Real.cos t, a * Real.sin t⟩)
  have hw (t : ℝ) : HasDerivAt w (batemanSphereMagnetic 1 1 (w t)) t := by
    have hRe₁ := (Real.hasDerivAt_cos t).const_mul a
    have hIm₁ := (Real.hasDerivAt_sin t).const_mul (-b)
    have hRe₂ := (Real.hasDerivAt_cos t).const_mul b
    have hIm₂ := (Real.hasDerivAt_sin t).const_mul a
    have h₁ := Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt t
      (HasDerivAt.prodMk hRe₁ hIm₁)
    have h₂ := Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt t
      (HasDerivAt.prodMk hRe₂ hIm₂)
    have hd := HasDerivAt.prodMk h₁ h₂
    change HasDerivAt w (⟨a * -Real.sin t, -b * Real.cos t⟩, ⟨b * -Real.sin t, a * Real.cos t⟩) t at hd
    convert hd using 1
    apply Prod.ext <;> apply Complex.ext <;>
      simp [w, batemanSphereMagnetic, batemanSphereElectric, batemanSphereFactor,
        Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  have hl (t : ℝ) : w t ∈ poweredSphereRealLevel 1 1 c := by
    change Complex.normSq (w t).1 + Complex.normSq (w t).2 = 1 ∧
      ((w t).1 ^ 1 * (w t).2 ^ 1).re = c
    constructor
    · norm_num [w, Complex.normSq_apply, a, b]
      linear_combination Real.sin_sq_add_cos_sq t
    · norm_num [w, Complex.mul_re, a, b, c]
      linear_combination (-12 / 25 : ℝ) * Real.sin_sq_add_cos_sq t
  have h₀ : c ≠ 0 := by norm_num [c]
  have hpeak : poweredPeakAmplitude 1 1 = 1 / 2 := by
    unfold poweredPeakAmplitude
    rw [show poweredRadiusProfile 1 1 (poweredPeakRadius 1 1) = (1 / 2 : ℝ) ^ 2 by
      norm_num [poweredRadiusProfile, poweredPeakRadius]]
    exact Real.sqrt_sq (by norm_num)
  have hc : |c| < poweredPeakAmplitude 1 1 := by rw [hpeak]; norm_num [c]
  refine ⟨w, ?_, hw, hl,
    batemanSphereMagnetic_periodic_or_dense (by decide) (by decide) (by decide) h₀ hc hw hl⟩
  apply Prod.ext <;> apply Complex.ext <;>
    norm_num [w, a, b, Complex.div_ofReal_re, Complex.div_ofReal_im]

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanMagneticQuotient_fiber_return
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanSphereMagnetic_periodic_or_dense

/-- A normalized Hopfion orbit gives a complete magnetic field line
at physical time -2, through the image of a point on a strict
nonzero intermediate torus. -/
example :
    ∃ γ : ℝ → ℝ × ℝ × ℝ,
      IsIntegralCurve γ (fun _ => batemanMagneticVector 1 1 (-2)) ∧
      γ 0 = batemanRay (-2) ((1 / 2 : ℝ), 0, 0) ∧
      ((∃ T : ℝ, 0 < T ∧ Function.Periodic γ T) ∨
        closure (Set.range γ) = poweredPhysicalRealLevel 1 1 (-2) (-12 / 25)) := by
  obtain ⟨w, hw₀, hw, hlevel, _⟩ := exists_hopfionSphereOrbit
  have h₀ : (-12 / 25 : ℝ) ≠ 0 := by norm_num
  have hpeak : poweredPeakAmplitude 1 1 = 1 / 2 := by
    unfold poweredPeakAmplitude
    rw [show poweredRadiusProfile 1 1 (poweredPeakRadius 1 1) = (1 / 2 : ℝ) ^ 2 by
      norm_num [poweredRadiusProfile, poweredPeakRadius]]
    exact Real.sqrt_sq (by norm_num)
  have hc : |(-12 / 25 : ℝ)| < poweredPeakAmplitude 1 1 := by rw [hpeak]; norm_num
  obtain ⟨e, hγ, hγ₀, hγlev⟩ := batemanSphereMagneticIntegralCurve_physical
    (by decide) (by decide) (by decide) (-2) h₀ hc hw hlevel
  refine ⟨_, hγ, ?_, batemanMagneticIntegralCurve_periodic_or_dense
    (by decide) (by decide) (by decide) (-2) h₀ hc hγ (hγlev 0)⟩
  rw [hγ₀, hw₀]
  congr 1
  norm_num [initialCartesianPoint, Complex.div_ofReal_re, Complex.div_ofReal_im]

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanMagneticIntegralCurve_normalized
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanSphereMagneticIntegralCurve_physical
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanMagneticIntegralCurve_periodic_or_dense
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanElectricIntegralCurve_periodic_or_dense

open scoped Real in
/-- The physical (2,3) magnetic and electric torus coordinates supply
complete orbits at explicit points on a nonzero time slice. -/
example :
    let x := batemanRay (-3) ((1 / 2 : ℝ), 0, 0)
    let y := batemanAxialRotation (π / 6) x
    (∃ γ : ℝ → ℝ × ℝ × ℝ, γ 0 = x ∧
      IsIntegralCurve γ (fun _ => batemanMagneticVector 2 3 (-3))) ∧
    (∃ γ : ℝ → ℝ × ℝ × ℝ, γ 0 = y ∧
      IsIntegralCurve γ (fun _ => batemanElectricVector 2 3 (-3))) := by
  let s : ℝ × ℝ × ℝ := (1 / 2, 0, 0)
  let x := batemanRay (-3) s
  let c : ℝ := 576 / 3125
  have hz : batemanPoweredLabel 2 3 0 s = (c : ℂ) := by
    change rationalAlpha (1 / 2) 0 0 0 ^ 2 * rationalBeta (1 / 2) 0 0 0 ^ 3 = _
    rw [rational_alpha_stereographic_zero_time, rational_beta_stereographic_zero_time]
    apply Complex.ext <;> norm_num [c, Complex.div_ofReal_re, Complex.div_ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, pow_succ]
  have hx : x ∈ poweredPhysicalRealLevel 2 3 (-3) c :=
    (batemanSliceHomeomorph_realLevel_iff 2 3 (-3) c s).1
      (by change (batemanPoweredLabel 2 3 0 s).re = c; rw [hz, Complex.ofReal_re])
  have h₀ : c ≠ 0 := by norm_num [c]
  have hc : |c| < poweredPeakAmplitude 2 3 := by
    have hsq : |c| ^ 2 < poweredPeakAmplitude 2 3 ^ 2 := by
      rw [poweredPeakAmplitude_sq (by decide) (by decide), sq_abs]
      norm_num [c, poweredRadiusProfile, poweredPeakRadius]
    by_contra! h
    exact hsq.not_ge (pow_le_pow_left₀ (poweredPeakAmplitude_pos (by decide) (by decide)).le h 2)
  have hy : batemanAxialRotation (π / 6) x ∈ poweredPhysicalImagLevel 2 3 (-3) (-c) := by
    have h := (poweredPhysicalLevel_axial_iff (p := 2) (q := 3) (by decide) (-3) (-c) x).1
    simpa only [neg_neg, Nat.cast_ofNat, show (2 : ℝ) * 3 = 6 by norm_num] using
      h (by rwa [neg_neg])
  obtain ⟨_, _, e, he, hflow⟩ := exists_batemanMagnetic_linearOrbits
    (by decide) (by decide) (by decide) (-3) h₀ hc hx
  obtain ⟨_, _, f, hf, hflow'⟩ := exists_batemanElectric_linearOrbits
    (by decide) (by decide) (by decide) (-3) (neg_ne_zero.mpr h₀) (by rwa [abs_neg]) hy
  obtain ⟨_, hγ, hγ₀⟩ := hflow (0, 1)
  obtain ⟨_, hη, hη₀⟩ := hflow' (0, 1)
  exact ⟨⟨_, hγ₀.trans (congrArg Subtype.val he), hγ⟩,
    ⟨_, hη₀.trans (congrArg Subtype.val hf), hη⟩⟩

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.exists_batemanMagneticIntegralCurve_on_level
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.exists_batemanElectricIntegralCurve_on_level

/-- The explicit nonzero strict intermediate `(2,3)` level supports linear
magnetic coordinates through the point with squared radii `9/25` and `16/25`. -/
example :
    let c : ℝ := 576 / 3125
    ∃ (T ω : ℝ) (e : (AddCircle T × Circle) ≃ₜ ↥(poweredSphereRealLevel 2 3 c)),
      0 < T ∧ (e (0, 1)).val = ((3 / 5 : ℂ), (4 / 5 : ℂ)) ∧
        ∀ x : AddCircle T × Circle,
          IsIntegralCurve
            (fun t => (e (x.1 + (t : AddCircle T), x.2 * Circle.exp (ω * t))).val)
            (fun _ => batemanSphereMagnetic 2 3) := by
  let c : ℝ := 576 / 3125
  have h₀ : c ≠ 0 := by norm_num [c]
  have hc : |c| < poweredPeakAmplitude 2 3 := by
    have hsq : |c| ^ 2 < poweredPeakAmplitude 2 3 ^ 2 := by
      rw [poweredPeakAmplitude_sq (by decide) (by decide), sq_abs]
      norm_num [c, poweredRadiusProfile, poweredPeakRadius]
    by_contra! h
    exact hsq.not_ge (pow_le_pow_left₀ (poweredPeakAmplitude_pos (by decide) (by decide)).le h 2)
  have hlev : ((3 / 5 : ℂ), (4 / 5 : ℂ)) ∈ poweredSphereRealLevel 2 3 c := by
    constructor <;> norm_num [c, Complex.normSq_apply,
      Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.mul_re, Complex.mul_im, pow_succ]
  obtain ⟨hT, ω, e, he, hflow⟩ := exists_batemanSphereMagnetic_linearFlow
    (by decide) (by decide) (by decide) h₀ hc hlev
  exact ⟨_, ω, e, hT, congrArg Subtype.val he, hflow⟩

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.exists_batemanSphereMagnetic_linearFlow

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.exists_batemanMagnetic_linearOrbits
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.exists_batemanElectric_linearOrbits

/-- At time `-3` the physical `(2,3)` magnetic zero level has explicit
points on both cylindrical branches away from the common zero set. -/
example :
    batemanRay (-3) (0, (1 / 2 : ℝ), 0) ∈ poweredPhysicalZeroBand 2 3 (-3) batemanImaginaryUnit ∧
    batemanRay (-3) (0, (-1 / 2 : ℝ), 0) ∈ poweredPhysicalZeroBand 2 3 (-3) (-batemanImaginaryUnit) := by
  have htransport (y : ℝ) := poweredProductLabel_batemanRay 2 3 (-3) (0, y, 0)
  have hlabel (y : ℝ) :
      batemanPoweredLabel 2 3 (-3) (batemanRay (-3) (0, y, 0)) =
        rationalAlpha 0 y 0 0 ^ 2 * rationalBeta 0 y 0 0 ^ 3 := htransport y
  constructor
  · change (batemanPoweredLabel 2 3 (-3) (batemanRay (-3) (0, 1 / 2, 0))).re = 0 ∧
      0 < Complex.I.im * (batemanPoweredLabel 2 3 (-3) (batemanRay (-3) (0, 1 / 2, 0))).im
    rw [hlabel, rational_alpha_stereographic_zero_time, rational_beta_stereographic_zero_time]
    norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, pow_succ]
  · change (batemanPoweredLabel 2 3 (-3) (batemanRay (-3) (0, -1 / 2, 0))).re = 0 ∧
      0 < (-Complex.I).im * (batemanPoweredLabel 2 3 (-3) (batemanRay (-3) (0, -1 / 2, 0))).im
    rw [hlabel, rational_alpha_stereographic_zero_time, rational_beta_stereographic_zero_time]
    norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, pow_succ]

/-- The positive branch on that time slice has cylinder coordinates. -/
noncomputable example : (↥(Set.Ioo (0 : ℝ) 1) × Circle) ≃ₜ ↥(poweredPhysicalZeroBand 2 3 (-3) batemanImaginaryUnit) :=
  poweredPhysicalZeroBandHomeomorph (by decide) (by decide) (by decide) (-3) Complex.I_re

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.poweredPhysicalZeroBandHomeomorph
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.poweredPhysicalRealZero_diff_eq_bands
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.disjoint_poweredPhysicalZeroBands

/-- The negative electric branch on the same time slice has cylinder coordinates. -/
noncomputable example : (↥(Set.Ioo (0 : ℝ) 1) × Circle) ≃ₜ
    ↥(poweredPhysicalElectricZeroBand 2 3 (-3) (-batemanImaginaryUnit)) :=
  poweredPhysicalElectricZeroBandHomeomorph (by decide) (by decide) (by decide) (-3) (by
    change (-Complex.I).re = 0
    rw [Complex.neg_re, Complex.I_re, neg_zero])

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.poweredPhysicalElectricZeroBandHomeomorph
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.poweredPhysicalImagZero_diff_eq_bands
