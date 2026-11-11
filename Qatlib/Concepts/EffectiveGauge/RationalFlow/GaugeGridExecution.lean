/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.GaugeCoordinates

set_option backward.isDefEq.respectTransparency false

/-!
# Gauge Grid Execution

Rational Flow constructions for Effective Gauge.
Defines `gaugeGridNode`.
Proves `gaugeGridExecution_eq_map`, `rationalGaugeCoefficientTerm_cast`, `rationalGaugeFourierCoefficientsOfData_cast`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of gauge Grid Node in the Rational Flow construction. -/
def gaugeGridNode (sample : SourceMeanIndex → Option (Quaternion ℚ))
    (index : SourceMeanIndex) : Quaternion ℚ := (sample index).getD 0

/-- Original `gaugeGridExecution_eq_map` guarantee for the `GaugeGridExecution` construction; the complete source hypotheses are retained. -/
theorem gaugeGridExecution_eq_map (sample : SourceMeanIndex → Option (Quaternion ℚ))
    (indices : List SourceMeanIndex) (hs : ∀ index∈indices, ∃ value, sample index=some value) :
    gaugeGridExecution sample indices=some (indices.map (fun index => (index,gaugeGridNode sample index))) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    obtain ⟨value,hvalue⟩ := hs index (by simp)
    have hrest : ∀ i∈rest, ∃ value, sample i=some value := by
      intro i hi
      exact hs i (by simp only [List.mem_cons]; exact Or.inr hi)
    simp only [gaugeGridExecution,hvalue,Option.bind_some,ih hrest,Option.map_some,List.map_cons]
    congr 2
    simp only [gaugeGridNode,hvalue,Option.getD_some]

noncomputable section

/-- Original `rationalGaugeCoefficientTerm_cast` guarantee for the `GaugeGridExecution` construction; the complete source hypotheses are retained. -/
theorem rationalGaugeCoefficientTerm_cast (M : ℕ) (length : ℚ) (k : SpatialFrequency) (d : ℚ)
    (index : SourceMeanIndex) (value : Quaternion ℚ) (j : Fin 4) :
    rationalCircleCast (rationalGaugeCoefficientTerm M length k d (index,value) j)=
      rationalCircleCast (rationalFourierMode length (-k) (sourceMeanUnitPoint M index) d).value*
        ((rationalQuaternionCoordinate value j : ℚ) : ℂ) := by
  apply Complex.ext <;> simp [rationalGaugeCoefficientTerm,rationalCircleCast]

/-- Original `rationalGaugeFourierCoefficientsOfData_cast` guarantee for the `GaugeGridExecution` construction; the complete source hypotheses are retained. -/
theorem rationalGaugeFourierCoefficientsOfData_cast (M : ℕ) (length : ℚ) (k : SpatialFrequency) (d : ℚ)
    (values : SourceMeanIndex → Quaternion ℚ) (j : Fin 4) :
    rationalCircleCast (rationalGaugeFourierCoefficientsOfData M length k d
      ((sourceMeanGrid M).map (fun index => (index,values index))) j)=
      sampledFourierCoefficientGrid M (fun a b c => ((rationalQuaternionCoordinate (values (a,b,c)) j : ℚ) : ℂ))
        (fun a b c => rationalCircleCast
          (rationalFourierMode length (-k) (sourceMeanUnitPoint M (a,b,c)) d).value) := by
  rw [rationalGaugeFourierCoefficientsOfData,rationalPairAverage_cast]
  simp only [List.map_map,Function.comp_def,rationalGaugeCoefficientTerm_cast]
  rw [sourceMeanGrid_sum]
  rfl

/-- Original `gaugeArtifactFrequency_ofFn` guarantee for the `GaugeGridExecution` construction; the complete source hypotheses are retained. -/
theorem gaugeArtifactFrequency_ofFn (k : SpatialFrequency) :
    gaugeArtifactFrequency (Vector.ofFn k)=k := by
  funext j
  simp [gaugeArtifactFrequency]

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
