/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonFiniteValueError
import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonValueBudget
import Qatlib.Concepts.EffectiveGauge.TorusFourier.ConnectionPoisson

set_option backward.isDefEq.respectTransparency false

/-!
# Poisson Prepared Value Error

Torus Fourier constructions for Effective Gauge.
Proves `poissonPreparedValue_error`.
-/

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- A finite value theorem for the same saved coefficient preparation.
The source theorem below discharges these analytic bounds from its cache. -/
theorem poissonPreparedValue_error (r : PoissonCoefficientPreparation) (eta tolerance : ℚ)
    (ht : 0<tolerance) (ht1 : tolerance ≤ 1/64)
    (hparameters : r.HasParameters eta tolerance) (hcertificate : r.NumericalCertificate tolerance)
    (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hp : IsPeriodicField q)
    (hC0 : ∀ j x, InUnitCube x → ‖normalizedConnectionComplex q j x‖ ≤ (r.referenceCache.connectionBounds[0] : ℝ))
    (hC6 : ∀ j i x, InUnitCube x →
      ‖spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) x‖ ≤
        (r.referenceCache.connectionBounds[6] : ℝ))
    (hcoefficients : ∀ k∈Finset.Icc (-r.cutoff : SpatialFrequency) r.cutoff,
      ∃ out, (k,out)∈r.coefficients ∧ ∀ j,
        ‖normalizedConnectionFourierCoefficient q hq hp j k-rationalCircleCast (out j)‖ ≤
          (tolerance : ℝ)/(24*(finitePoissonFrequencyCount r.cutoff : ℝ)))
    (address : Fin 3 → ℚ) :
    |(generalPoissonStateValue (materializeGeneralPoissonValueState r) address : ℝ)-
      normalizedConnectionPoisson q hq hp (rationalSpatialPoint address)| ≤ (tolerance : ℝ)/2 := by
  rcases hparameters with ⟨hcache,hcutoff,hmesh,hs,hd,hell,hlambda⟩
  rcases hcertificate with ⟨hN,hM,hspec,hdSpec,hellSpec,hperiod,hlength,hbalance,hcutoffBudget,htailBudget,hdata,hkeys⟩
  let C0 : ℝ := r.referenceCache.connectionBounds[0]
  let E : ℝ := (tolerance : ℝ)/(24*(finitePoissonFrequencyCount r.cutoff : ℝ))
  let J : ℝ := finitePoissonFrequencyCount r.cutoff
  let F : ℝ := 3*E/5+3*(C0+E)*(r.modeAccuracy : ℝ)/5+3*C0*(r.periodAccuracy : ℝ)/30
  let a := normalizedConnectionFourierCoefficient q hq hp
  let x := rationalSpatialPoint address
  let trunc := unitFourierTruncation (unitPoissonCoefficient a) r.cutoff x
  let value := rationalPoissonValuePair (rationalPoissonBetaList r.coefficients) r.period r.modeAccuracy address
  have hC0pos : 0 ≤ C0 := (norm_nonneg _).trans (hC0 0 0 (by intro j; norm_num))
  have hC0Q : 0 ≤ r.referenceCache.connectionBounds[0] := by
    have h : (0 : ℝ) ≤ (r.referenceCache.connectionBounds[0] : ℝ) := hC0pos
    exact_mod_cast h
  have hcoefNorm (k : SpatialFrequency) (_hk : k∈sourceFrequencyGrid r.cutoff) (j : Fin 3) :
      ‖a j k‖ ≤ C0 :=
    unitFourierCoefficient_norm_le _ (contDiff_normalizedConnectionComplex q hq j).continuous
      (unitPeriodic_normalizedConnectionComplex q hq hp j) k C0 (hC0 j)
  have hrows := rationalCoefficientList_row_error r.coefficients r.cutoff hkeys a E hcoefficients
  have hbalanceR : 3*(r.cutoff : ℝ)*(r.periodAccuracy : ℝ) ≤ (r.modeAccuracy : ℝ)/2 := by exact_mod_cast hbalance
  have hfinite : ‖rationalCircleCast value-trunc‖ ≤ J*F :=
    rationalPoissonValuePair_error r.coefficients r.cutoff hkeys a C0 E hC0pos (by dsimp only [E]; positivity)
      hcoefNorm hrows r.period r.modeAccuracy hdSpec.1 hdSpec.2 (r.periodAccuracy : ℝ) hlength hperiod hbalanceR address
  have hre : |(rationalPoissonValue (rationalPoissonBetaList r.coefficients) r.period r.modeAccuracy address : ℝ)-trunc.re| ≤ J*F := by
    have h := (Complex.abs_re_le_norm (rationalCircleCast value-trunc)).trans hfinite
    simpa only [value,Complex.sub_re,← rationalPoissonValue_eq_re] using h
  have htail := normalizedConnectionPoisson_truncation_bound q hq hp
    (r.referenceCache.connectionBounds[6] : ℝ) hC6 r.cutoff hN x
  have htailBudgetR : 156*(r.referenceCache.connectionBounds[6] : ℝ)/(r.cutoff : ℝ)^3 ≤
      39*(tolerance : ℝ)/100 := by exact_mod_cast htailBudget
  have htail' : |trunc.re-normalizedConnectionPoisson q hq hp x| ≤ 39*(tolerance : ℝ)/100 := by
    rw [abs_sub_comm]
    have htailReal : |normalizedConnectionPoisson q hq hp x-trunc.re| ≤
        156*(r.referenceCache.connectionBounds[6] : ℝ)/(r.cutoff : ℝ)^3 := by
      simpa only [trunc,a,Real.norm_eq_abs,Complex.reCLM_apply,Nat.cast_ofNat,Rat.cast_ofNat] using htail
    exact htailReal.trans htailBudgetR
  have hbudgetQ := finitePoissonValue_budget r.referenceCache.connectionBounds[0] hC0Q r.cutoff hN tolerance ht ht1
  dsimp only at hbudgetQ
  rw [← hd,← hell] at hbudgetQ
  have hbudgetR : J*F+39*(tolerance : ℝ)/100 ≤ (tolerance : ℝ)/2 := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr hbudgetQ
    push_cast at hcast
    dsimp only [J,F,E,C0]
    exact hcast
  change |(rationalPoissonValue (rationalPoissonBetaList r.coefficients) r.period r.modeAccuracy address : ℝ)-
    normalizedConnectionPoisson q hq hp x| ≤ _
  exact ((abs_sub_le _ _ _).trans (add_le_add hre htail')).trans hbudgetR

end Qatlib.Concepts.EffectiveGauge.TorusFourier
