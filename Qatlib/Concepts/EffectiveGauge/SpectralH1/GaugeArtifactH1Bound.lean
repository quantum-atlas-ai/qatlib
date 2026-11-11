/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.SpectralH1.QuaternionH1Energy
import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierResidualEnergy
import Qatlib.Concepts.EffectiveGauge.SpectralH1.GaugeArtifactPolynomial

set_option backward.isDefEq.respectTransparency false

/-!
# Gauge Artifact H1 Bound

Spectral H1 constructions for Effective Gauge.
Proves `gaugeArtifact_normalized_H1_bound`.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original `gaugeArtifact_normalized_H1_bound` guarantee for the `GaugeArtifactH1Bound` construction; the complete source hypotheses are retained. -/
theorem gaugeArtifact_normalized_H1_bound (G : QuaternionField) (hG : ContDiff ℝ ∞ G)
    (hp : IsUnitPeriodicField G) (artifact : RationalGaugeFourierArtifact)
    (N M : ℕ) (length d : ℚ) (data : RationalGaugeGridData)
    (hrows : artifact.coefficients=(sourceFrequencyGrid N).map (fun k =>
      (Vector.ofFn k,Vector.ofFn (rationalGaugeFourierCoefficientsOfData M length k d data))))
    (delta M3 : ℝ) (hd : 0 ≤ delta) (hM : 0 ≤ M3)
    (hcoef : ∀ j : Fin 4,
      let f := fun u => quaternionComplexCoordinateCLM j (G u)
      let hf := (quaternionComplexCoordinateCLM j).contDiff.comp hG
      let hp' : IsUnitPeriodicField f := fun u n => by dsimp only [f]; rw [hp u n]
      ∀ k∈Finset.Icc (-N : SpatialFrequency) N,
        ‖unitFourierCoefficient f hf.continuous hp' k-rationalCircleCast
          (rationalGaugeFourierCoefficientsOfData M length k d data j)‖ ≤ delta)
    (hthird : ∀ i u, ‖spatialWordPartial G [i,i,i] u‖ ≤ M3) :
    unitFieldH1Energy (fun u => G u-gaugeFourierArtifactField artifact (physicalPeriod • u)) ≤
      4*(((2*N+1)^3 : ℕ)*(1+3*(N : ℝ)^2)*delta^2+
        12*M3^2/(physicalPeriod^6*((N : ℝ)+1)^4)) := by
  let H := fun u => G u-gaugeFourierArtifactField artifact (physicalPeriod • u)
  have hH : ContDiff ℝ ∞ H := hG.sub ((gaugeFourierArtifactField_contDiff artifact).comp
    (contDiff_id.const_smul physicalPeriod))
  let f := fun j : Fin 4 => fun u => quaternionComplexCoordinateCLM j (G u)
  let a := fun j : Fin 4 => fun k => rationalCircleCast (rationalGaugeFourierCoefficientsOfData M length k d data j)
  let R := fun j : Fin 4 => unitFourierResidual (f j) (a j) N
  have hf (j : Fin 4) : ContDiff ℝ ∞ (f j) := (quaternionComplexCoordinateCLM j).contDiff.comp hG
  have hfp (j : Fin 4) : IsUnitPeriodicField (f j) := fun u n => by dsimp only [f]; rw [hp u n]
  have hR (j : Fin 4) : ContDiff ℝ ∞ (R j) := contDiff_unitFourierResidual (f j) (hf j) (a j) N
  have hcoord (j : Fin 4) : (fun u => quaternionCoordinateCLM j (H u))=fun u => (R j u).re := by
    funext u
    dsimp only [H]
    rw [map_sub,gaugeArtifactField_coordinate_truncation artifact N M length d data hrows]
    change quaternionCoordinateCLM j (G u)-(unitFourierTruncation (a j) N u).re=
      ((f j u)-unitFourierTruncation (a j) N u).re
    rw [Complex.sub_re]
    rfl
  have hb (j : Fin 4) : unitFieldH1Energy (R j) ≤
      ((2*N+1)^3 : ℕ)*(1+3*(N : ℝ)^2)*delta^2+
        12*M3^2/(physicalPeriod^6*((N : ℝ)+1)^4) := by
    apply unitFourierResidual_H1_le (f j) (hf j) (hfp j) (a j) N delta M3 hd hM (hcoef j)
    intro i u _
    exact quaternionComplexCoordinate_word_bound G hG j [i,i,i] M3 (hthird i) u
  rw [unitFieldH1Energy_coordinates H hH]
  have hsum := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 4))) =>
    (unitFieldH1Energy_re_le (R j) (hR j)).trans (hb j))
  simpa only [← hcoord,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat] using hsum

end Qatlib.Concepts.EffectiveGauge.SpectralH1
