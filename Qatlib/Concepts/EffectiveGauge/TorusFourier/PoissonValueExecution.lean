/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.AutomaticCoefficientPreparation
import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonBetaExecution

set_option backward.isDefEq.respectTransparency false

/-!
# Poisson Value Execution

Torus Fourier constructions for Effective Gauge.
Defines `rationalPoissonValueTerm`, `rationalPoissonValuePair`, `rationalPoissonValue`.
Proves `rationalCircleCast_div`, `rationalPoissonValuePair_cast`, `rationalPoissonValue_eq_re`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of rational Poisson Value Term in the Torus Fourier construction. -/
def rationalPoissonValueTerm (length d : ℚ) (address : Fin 3 → ℚ)
    (record : SpatialFrequency × RationalCircleSample) : RationalCircleSample :=
  cisPairMul record.2 (rationalFourierMode length record.1 (rationalUnitWrap address) d).value

/-- Definition of rational Poisson Value Pair in the Torus Fourier construction. -/
def rationalPoissonValuePair (beta : List (SpatialFrequency × RationalCircleSample))
    (length d : ℚ) (address : Fin 3 → ℚ) : RationalCircleSample :=
  let value := (beta.map (rationalPoissonValueTerm length d address)).sum
  (value.1/length,value.2/length)

/-- Definition of rational Poisson Value in the Torus Fourier construction. -/
def rationalPoissonValue (beta : List (SpatialFrequency × RationalCircleSample))
    (length d : ℚ) (address : Fin 3 → ℚ) : ℚ := (rationalPoissonValuePair beta length d address).1

/-- Data and hypotheses for General Poisson Value State in the Torus Fourier construction. -/
structure GeneralPoissonValueState where
  preparation : PoissonCoefficientPreparation
  beta : List (SpatialFrequency × RationalCircleSample)

/-- Definition of materialize General Poisson Value State in the Torus Fourier construction. -/
def materializeGeneralPoissonValueState (r : PoissonCoefficientPreparation) : GeneralPoissonValueState :=
  ⟨r,rationalPoissonBetaList r.coefficients⟩

/-- Definition of automatic General Poisson From Gap in the Torus Fourier construction. -/
def automaticGeneralPoissonFromGap (source : RationalJetSource) (bounds : ℕ → ℚ)
    (gap tolerance : ℚ) : Option GeneralPoissonValueState :=
  (automaticPoissonCoefficientsFromGap source bounds gap tolerance).map materializeGeneralPoissonValueState

/-- Point evaluation reads only saved rational beta/period/accuracy data.
It has no original-source callback or Poisson-solution oracle argument. -/
def generalPoissonStateValue (r : GeneralPoissonValueState) (address : Fin 3 → ℚ) : ℚ :=
  rationalPoissonValue r.beta r.preparation.period r.preparation.modeAccuracy address

noncomputable section

/-- Original `rationalCircleCast_div` guarantee for the `PoissonValueExecution` construction; the complete source hypotheses are retained. -/
theorem rationalCircleCast_div (a : RationalCircleSample) (r : ℚ) :
    rationalCircleCast (a.1/r,a.2/r)=rationalCircleCast a/((r : ℝ) : ℂ) := by
  rw [Complex.div_ofReal]
  apply Complex.ext <;> simp [rationalCircleCast]

/-- Original `rationalPoissonValuePair_cast` guarantee for the `PoissonValueExecution` construction; the complete source hypotheses are retained. -/
theorem rationalPoissonValuePair_cast (beta : List (SpatialFrequency × RationalCircleSample))
    (length d : ℚ) (address : Fin 3 → ℚ) :
    rationalCircleCast (rationalPoissonValuePair beta length d address)=
      ((beta.map (fun record => rationalCircleCast record.2*
        rationalCircleCast (rationalFourierMode length record.1 (rationalUnitWrap address) d).value)).sum)/
          ((length : ℝ) : ℂ) := by
  rw [rationalPoissonValuePair,rationalCircleCast_div,rationalCircleCast_list_sum]
  simp only [List.map_map,Function.comp_def,rationalPoissonValueTerm,cisPairMul_cast]

/-- Original `rationalPoissonValue_eq_re` guarantee for the `PoissonValueExecution` construction; the complete source hypotheses are retained. -/
theorem rationalPoissonValue_eq_re (beta : List (SpatialFrequency × RationalCircleSample))
    (length d : ℚ) (address : Fin 3 → ℚ) :
    (rationalPoissonValue beta length d address : ℝ)=
      (rationalCircleCast (rationalPoissonValuePair beta length d address)).re := rfl

/-- Original `rationalPoissonBetaList_keys` guarantee for the `PoissonValueExecution` construction; the complete source hypotheses are retained. -/
theorem rationalPoissonBetaList_keys (coefficients : RationalFourierCoefficientList) :
    (rationalPoissonBetaList coefficients).map Prod.fst=coefficients.map Prod.fst := by
  simp only [rationalPoissonBetaList,List.map_map,Function.comp_def]

end
end Qatlib.Concepts.EffectiveGauge.TorusFourier
