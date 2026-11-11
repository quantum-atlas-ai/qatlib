/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonRegularity

set_option backward.isDefEq.respectTransparency false

/-!
# Poisson Equation

Torus Fourier constructions for Effective Gauge.
Proves `unitFourierSeries_reconstruction`, `unitFourierSeries_neg`, `unitComplexPoisson_equation`.
-/


set_option autoImplicit false
noncomputable section
open Finset
open scoped ContDiff Topology
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `unitFourierSeries_reconstruction` guarantee for the `PoissonEquation` construction; the complete source hypotheses are retained. -/
theorem unitFourierSeries_reconstruction (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) :
    unitFourierSeries (unitFourierCoefficient f hf.continuous hp)=f := by
  have ha := unitFourierCoefficient_rapidlySummable f hf hp
  have hnorm : Summable (fun k => ‖unitFourierCoefficient f hf.continuous hp k‖) := by
    simpa only [pow_zero,one_mul] using ha 0
  funext x
  have h := unitFourier_hasSum_of_summable f hf.continuous hp hnorm.of_norm x
  simpa only [unitFourierSeries,mul_comm] using h.tsum_eq

/-- Original `unitFourierSeries_neg` guarantee for the `PoissonEquation` construction; the complete source hypotheses are retained. -/
theorem unitFourierSeries_neg (a : SpatialFrequency → ℂ) (x : SpatialPoint) :
    unitFourierSeries (fun k => -a k) x= -unitFourierSeries a x := by
  simp only [unitFourierSeries,neg_mul,tsum_neg]

/-- The spectral construction solves the actual pointwise PDE on all of
 real space, after justified differentiation and inversion of the input. -/
theorem unitComplexPoisson_equation (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) (x : SpatialPoint) :
    (∑ j : Fin 3, spatialWordPartial (unitComplexPoisson f hf hp) [j,j] x)=
      -∑ j : Fin 3, spatialWordPartial (f j) [j] x := by
  let a : Fin 3 → SpatialFrequency → ℂ :=
    fun j => unitFourierCoefficient (f j) (hf j).continuous (hp j)
  have ha (j : Fin 3) : FourierRapidlySummable (a j) :=
    unitFourierCoefficient_rapidlySummable (f j) (hf j) (hp j)
  let b := unitPoissonCoefficient a
  have hb : FourierRapidlySummable b := unitPoissonCoefficient_rapidlySummable a ha
  let d := fun (j : Fin 3) (k : SpatialFrequency) => ((physicalPeriod : ℂ)*Complex.I*(k j : ℂ))*a j k
  have hd (j : Fin 3) : FourierRapidlySummable (d j) := (ha j).partial j
  have hinv (j : Fin 3) : unitFourierSeries (a j)=f j :=
    unitFourierSeries_reconstruction (f j) (hf j) (hp j)
  have hleft (j : Fin 3) : spatialWordPartial (unitComplexPoisson f hf hp) [j,j] x=
      unitFourierSeries (fun k => unitModeWordFactor k [j,j]*b k) x :=
    congrFun (unitFourierSeries_word b hb [j,j]) x
  have hright (j : Fin 3) : spatialWordPartial (f j) [j] x=unitFourierSeries (d j) x := by
    rw [← hinv j]
    exact congrFun (unitFourierSeries_partial (a j) (ha j) j) x
  simp_rw [hleft,hright]
  calc
    _ = unitFourierSeries (fun k => ∑ j : Fin 3, unitModeWordFactor k [j,j]*b k) x :=
      (unitFourierSeries_finsetSum _ (fun j => hb.word [j,j]) Finset.univ x).symm
    _ = unitFourierSeries (fun k => -(∑ j : Fin 3, d j k)) x := by
      apply congrArg (fun c : SpatialFrequency → ℂ => unitFourierSeries c x)
      funext k
      exact unitPoissonCoefficient_word_sum a k
    _ = -(unitFourierSeries (fun k => ∑ j : Fin 3, d j k) x) := unitFourierSeries_neg _ x
    _ = _ := by rw [unitFourierSeries_finsetSum d hd Finset.univ x]

/-- Original `unitRealPoisson_equation` guarantee for the `PoissonEquation` construction; the complete source hypotheses are retained. -/
theorem unitRealPoisson_equation (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) (x : SpatialPoint) :
    (∑ j : Fin 3, spatialWordPartial (unitRealPoisson f hf hp) [j,j] x)=
      -∑ j : Fin 3, spatialWordPartial (fun y => Complex.reCLM (f j y)) [j] x := by
  have h := congrArg Complex.reCLM (unitComplexPoisson_equation f hf hp x)
  have hleft (j : Fin 3) : spatialWordPartial (unitRealPoisson f hf hp) [j,j] x=
      Complex.reCLM (spatialWordPartial (unitComplexPoisson f hf hp) [j,j] x) :=
    congrFun (spatialWordPartial_clm Complex.reCLM (unitComplexPoisson f hf hp)
      (unitComplexPoisson_contDiff f hf hp) [j,j]) x
  have hright (j : Fin 3) : spatialWordPartial (fun y => Complex.reCLM (f j y)) [j] x=
      Complex.reCLM (spatialWordPartial (f j) [j] x) :=
    congrFun (spatialWordPartial_clm Complex.reCLM (f j) (hf j) [j]) x
  simp_rw [hleft,hright]
  simpa only [map_sum,map_neg] using h

end Qatlib.Concepts.EffectiveGauge.TorusFourier
