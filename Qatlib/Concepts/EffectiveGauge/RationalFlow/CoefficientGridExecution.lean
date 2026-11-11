/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.SourceConnectionSampling
import Qatlib.Concepts.EffectiveGauge.RationalFlow.CoefficientSampling
import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierModeApproximation
import Qatlib.Concepts.EffectiveGauge.RationalFlow.SourceMeanSum

set_option backward.isDefEq.respectTransparency false

/-!
# Coefficient Grid Execution

Rational Flow constructions for Effective Gauge.
Defines `RationalConnectionGridData`, `connectionGridExecution`, `connectionGridNode`.
Proves `connectionGridExecution_eq_map`, `rationalCircleCast_add`, `rationalCircleCast_smul`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Abbreviation for Rational Connection Grid Data in the Rational Flow construction. -/
abbrev RationalConnectionGridData := List (SourceMeanIndex × (Fin 3 → ℚ))

/-- Materialize each vector sample once, preserving its executed address. -/
def connectionGridExecution (sample : SourceMeanIndex → Option (Fin 3 → ℚ)) :
    List SourceMeanIndex → Option RationalConnectionGridData
  | [] => some []
  | index::rest => (sample index).bind (fun value =>
      (connectionGridExecution sample rest).map (fun data => (index,value)::data))

/-- Definition of connection Grid Node in the Rational Flow construction. -/
def connectionGridNode (sample : SourceMeanIndex → Option (Fin 3 → ℚ))
    (index : SourceMeanIndex) : Fin 3 → ℚ := (sample index).getD (fun _ => 0)

/-- Definition of rational Pair Average in the Rational Flow construction. -/
def rationalPairAverage (M : ℕ) (values : List RationalCircleSample) : RationalCircleSample :=
  ((values.sum).1/(M : ℚ)^3,(values.sum).2/(M : ℚ)^3)

/-- Definition of rational Coefficient Term in the Rational Flow construction. -/
def rationalCoefficientTerm (M : ℕ) (length : ℚ) (k : SpatialFrequency) (d : ℚ)
    (record : SourceMeanIndex × (Fin 3 → ℚ)) (j : Fin 3) : RationalCircleSample :=
  let e := (rationalFourierMode length (-k) (sourceMeanUnitPoint M record.1) d).value
  (e.1*record.2 j,e.2*record.2 j)

/-- Definition of rational Fourier Coefficients Of Data in the Rational Flow construction. -/
def rationalFourierCoefficientsOfData (M : ℕ) (length : ℚ) (k : SpatialFrequency) (d : ℚ)
    (data : RationalConnectionGridData) : Fin 3 → RationalCircleSample :=
  fun j => rationalPairAverage M (data.map (fun record => rationalCoefficientTerm M length k d record j))

/-- Definition of source Fourier Coefficient Execution in the Rational Flow construction. -/
def sourceFourierCoefficientExecution (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (eta : ℚ) (M : ℕ) (s length : ℚ) (k : SpatialFrequency) (d : ℚ) :
    Option (RationalConnectionGridData × (Fin 3 → RationalCircleSample)) :=
  (connectionGridExecution
    (fun index => sourceConnectionSampling source prepared eta (sourceMeanUnitPoint M index) s)
    (sourceMeanGrid M)).map (fun data => (data,rationalFourierCoefficientsOfData M length k d data))

/-- This equation is for analysis; evaluating its RHS is not the fee model.
The actual producer above retains the samples in its returned data. -/
theorem connectionGridExecution_eq_map (sample : SourceMeanIndex → Option (Fin 3 → ℚ))
    (indices : List SourceMeanIndex) (hs : ∀ index∈indices, ∃ value, sample index=some value) :
    connectionGridExecution sample indices=some (indices.map (fun index => (index,connectionGridNode sample index))) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    obtain ⟨value,hvalue⟩ := hs index (by simp)
    have hrest : ∀ i∈rest, ∃ value, sample i=some value := by
      intro i hi
      exact hs i (by simp only [List.mem_cons]; exact Or.inr hi)
    simp only [connectionGridExecution,hvalue,Option.bind_some,ih hrest,Option.map_some,List.map_cons]
    congr 2
    simp only [connectionGridNode,hvalue,Option.getD_some]

noncomputable section
open scoped BigOperators

/-- Original `rationalCircleCast_add` guarantee for the `CoefficientGridExecution` construction; the complete source hypotheses are retained. -/
theorem rationalCircleCast_add (a b : RationalCircleSample) :
    rationalCircleCast (a+b)=rationalCircleCast a+rationalCircleCast b := by
  apply Complex.ext <;> simp [rationalCircleCast]

/-- Original `rationalCircleCast_smul` guarantee for the `CoefficientGridExecution` construction; the complete source hypotheses are retained. -/
theorem rationalCircleCast_smul (r : ℚ) (a : RationalCircleSample) :
    rationalCircleCast (r • a)=(r : ℝ) • rationalCircleCast a := by
  apply Complex.ext <;> simp [rationalCircleCast,smul_eq_mul]

/-- Original `rationalCircleCast_list_sum` guarantee for the `CoefficientGridExecution` construction; the complete source hypotheses are retained. -/
theorem rationalCircleCast_list_sum (values : List RationalCircleSample) :
    rationalCircleCast values.sum=(values.map rationalCircleCast).sum := by
  induction values with
  | nil => apply Complex.ext <;> simp [rationalCircleCast]
  | cons a values ih => simp only [List.sum_cons,List.map_cons,rationalCircleCast_add,ih]

/-- Original `rationalPairAverage_cast` guarantee for the `CoefficientGridExecution` construction; the complete source hypotheses are retained. -/
theorem rationalPairAverage_cast (M : ℕ) (values : List RationalCircleSample) :
    rationalCircleCast (rationalPairAverage M values)=
      ((M : ℝ)^3)⁻¹ • (values.map rationalCircleCast).sum := by
  have hid : rationalPairAverage M values=((M : ℚ)^3)⁻¹ • values.sum := by
    apply Prod.ext <;> simp [rationalPairAverage,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [hid,rationalCircleCast_smul,rationalCircleCast_list_sum]
  simp only [Rat.cast_inv,Rat.cast_pow,Rat.cast_natCast]

/-- Original `rationalCoefficientTerm_cast` guarantee for the `CoefficientGridExecution` construction; the complete source hypotheses are retained. -/
theorem rationalCoefficientTerm_cast (M : ℕ) (length : ℚ) (k : SpatialFrequency) (d : ℚ)
    (index : SourceMeanIndex) (value : Fin 3 → ℚ) (j : Fin 3) :
    rationalCircleCast (rationalCoefficientTerm M length k d (index,value) j)=
      rationalCircleCast (rationalFourierMode length (-k) (sourceMeanUnitPoint M index) d).value*
        ((value j : ℚ) : ℂ) := by
  apply Complex.ext <;> simp [rationalCoefficientTerm,rationalCircleCast]

/-- The returned rational accumulator is exactly the triple finite grid
used by the complex error bound, including its DC entry. -/
theorem rationalFourierCoefficientsOfData_cast (M : ℕ) (length : ℚ) (k : SpatialFrequency) (d : ℚ)
    (values : SourceMeanIndex → Fin 3 → ℚ) (j : Fin 3) :
    rationalCircleCast (rationalFourierCoefficientsOfData M length k d
      ((sourceMeanGrid M).map (fun index => (index,values index))) j)=
      sampledFourierCoefficientGrid M (fun a b c => ((values (a,b,c) j : ℚ) : ℂ))
        (fun a b c => rationalCircleCast
          (rationalFourierMode length (-k) (sourceMeanUnitPoint M (a,b,c)) d).value) := by
  rw [rationalFourierCoefficientsOfData,rationalPairAverage_cast]
  simp only [List.map_map,Function.comp_def,rationalCoefficientTerm_cast]
  rw [sourceMeanGrid_sum]
  rfl

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
