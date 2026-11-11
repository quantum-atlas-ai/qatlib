/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonEquation
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordPeriodic
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceCurvature

set_option backward.isDefEq.respectTransparency false

/-!
# Harmonic Connection

Hopf Atlas constructions for Effective Gauge.
Proves `closed_divFree_frequency_zero`, `unitFourierCoefficient_fin3Sum`, `unitClosed_divFree_coefficients`.
-/


set_option autoImplicit false
noncomputable section
open Finset
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original `closed_divFree_frequency_zero` guarantee for the `HarmonicConnection` construction; the complete source hypotheses are retained. -/
theorem closed_divFree_frequency_zero (k : SpatialFrequency) (hk : k≠0) (a : Fin 3 → ℂ)
    (hc : ∀ i j, (k i : ℂ)*a j=(k j : ℂ)*a i)
    (hd : (∑ i : Fin 3, (k i : ℂ)*a i)=0) (j : Fin 3) : a j=0 := by
  have hE : (frequencyEnergy k : ℂ)≠0 := by exact_mod_cast (frequencyEnergy_pos k hk).ne'
  have heq : (frequencyEnergy k : ℂ)=∑ i : Fin 3, (k i : ℂ)^2 := by simp [frequencyEnergy]
  have hzero : (frequencyEnergy k : ℂ)*a j=0 := by
    calc
      _ = ∑ i : Fin 3, (k i : ℂ)*((k i : ℂ)*a j) := by
        rw [heq,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i : Fin 3, (k i : ℂ)*((k j : ℂ)*a i) := by simp_rw [hc]
      _ = (k j : ℂ)*(∑ i : Fin 3, (k i : ℂ)*a i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hd,mul_zero]
  exact (mul_eq_zero.mp hzero).resolve_left hE

/-- Original `unitFourierCoefficient_fin3Sum` guarantee for the `HarmonicConnection` construction; the complete source hypotheses are retained. -/
theorem unitFourierCoefficient_fin3Sum (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, Continuous (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) (k : SpatialFrequency) :
    unitFourierCoefficient (fun x => ∑ j : Fin 3, f j x) (continuous_finsetSum _ (fun j _ => hf j))
      (by intro x n; apply Finset.sum_congr rfl; intro j _; exact hp j x n) k=
      ∑ j : Fin 3, unitFourierCoefficient (f j) (hf j) (hp j) k := by
  simp_rw [unitFourierCoefficient_eq_cubeIntegral,Finset.mul_sum]
  have hcont (j : Fin 3) : Continuous (fun x => unitFourierMode (-k) x*f j x) :=
    (contDiff_unitFourierMode (-k)).continuous.mul (hf j)
  simp only [Fin.sum_univ_three]
  rw [unitComplexCubeIntegral_add
    (fun x => unitFourierMode (-k) x*f 0 x+unitFourierMode (-k) x*f 1 x)
    (fun x => unitFourierMode (-k) x*f 2 x) ((hcont 0).add (hcont 1)) (hcont 2),
    unitComplexCubeIntegral_add _ _ (hcont 0) (hcont 1)]

/-- Original `unitClosed_divFree_coefficients` guarantee for the `HarmonicConnection` construction; the complete source hypotheses are retained. -/
theorem unitClosed_divFree_coefficients (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j))
    (hc : ∀ x i j, spatialWordPartial (f j) [i] x=spatialWordPartial (f i) [j] x)
    (hd : ∀ x, (∑ j : Fin 3, spatialWordPartial (f j) [j] x)=0)
    (k : SpatialFrequency) (hk : k≠0) (j : Fin 3) :
    unitFourierCoefficient (f j) (hf j).continuous (hp j) k=0 := by
  let a := fun j => unitFourierCoefficient (f j) (hf j).continuous (hp j) k
  let c : ℂ := (physicalPeriod : ℂ)*Complex.I
  have hc0 : c≠0 := mul_ne_zero (by exact_mod_cast physicalPeriod_pos.ne') Complex.I_ne_zero
  have hclosed (i j : Fin 3) : (k i : ℂ)*a j=(k j : ℂ)*a i := by
    apply mul_left_cancel₀ hc0
    have heq : spatialWordPartial (f j) [i]=spatialWordPartial (f i) [j] := funext (fun x => hc x i j)
    have hcoeff := unitFourierCoefficient_partial (f j) (hf j) (hp j) k i
    have hother := unitFourierCoefficient_partial (f i) (hf i) (hp i) k j
    rw [unitFourierCoefficient_eq_cubeIntegral] at hcoeff hother
    rw [heq,hother] at hcoeff
    simpa only [a,c,mul_assoc] using hcoeff.symm
  have hsum := unitFourierCoefficient_fin3Sum (fun j => spatialWordPartial (f j) [j])
    (fun j => (contDiff_spatialWordPartial (f j) (hf j) [j]).continuous)
    (fun j => unitPeriodicField_spatialWordPartial (f j) (hf j) (hp j) [j]) k
  have hsum0 : (∑ i : Fin 3, (k i : ℂ)*a i)=0 := by
    apply (mul_eq_zero.mp (show c*(∑ i : Fin 3, (k i : ℂ)*a i)=0 from ?_)).resolve_left hc0
    have hi : (∑ i : Fin 3, c*((k i : ℂ)*a i))=0 := by
      calc
        _ = ∑ i : Fin 3, unitFourierCoefficient (spatialWordPartial (f i) [i])
            (contDiff_spatialWordPartial (f i) (hf i) [i]).continuous
            (unitPeriodicField_spatialWordPartial (f i) (hf i) (hp i) [i]) k := by
          apply Finset.sum_congr rfl
          intro i _
          simpa only [c,a,mul_assoc] using (unitFourierCoefficient_partial (f i) (hf i) (hp i) k i).symm
        _ = unitFourierCoefficient (fun x => ∑ i : Fin 3, spatialWordPartial (f i) [i] x) _ _ k := hsum.symm
        _ = 0 := by
          rw [unitFourierCoefficient_eq_cubeIntegral]
          simp only [hd,mul_zero,unitComplexCubeIntegral,MeasureTheory.integral_zero]
    simpa only [Finset.mul_sum] using hi

  exact closed_divFree_frequency_zero k hk a hclosed hsum0 j

/-- Original `unitClosed_divFree_constant` guarantee for the `HarmonicConnection` construction; the complete source hypotheses are retained. -/
theorem unitClosed_divFree_constant (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j))
    (hc : ∀ x i j, spatialWordPartial (f j) [i] x=spatialWordPartial (f i) [j] x)
    (hd : ∀ x, (∑ j : Fin 3, spatialWordPartial (f j) [j] x)=0) (j : Fin 3) (x : SpatialPoint) :
    f j x=unitFourierCoefficient (f j) (hf j).continuous (hp j) 0 := by
  rw [← congrFun (unitFourierSeries_reconstruction (f j) (hf j) (hp j)) x]
  unfold unitFourierSeries
  rw [tsum_eq_single 0]
  · simp [unitFourierMode_zero]
  · intro k hk
    rw [unitClosed_divFree_coefficients f hf hp hc hd k hk j,zero_mul]

/-- Original `physicalClosed_divFree_constant` guarantee for the `HarmonicConnection` construction; the complete source hypotheses are retained. -/
theorem physicalClosed_divFree_constant (f : Fin 3 → SpatialPoint → ℝ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsPeriodicField (f j))
    (hc : ∀ x i j, spatialWordPartial (f j) [i] x=spatialWordPartial (f i) [j] x)
    (hd : ∀ x, (∑ j : Fin 3, spatialWordPartial (f j) [j] x)=0) (j : Fin 3) (x : SpatialPoint) :
    f j x=f j 0 := by
  let g : Fin 3 → SpatialPoint → ℂ := fun j u => Complex.ofRealCLM (f j (physicalPeriod • u))
  have hg (j : Fin 3) : ContDiff ℝ ∞ (g j) :=
    Complex.ofRealCLM.contDiff.comp ((hf j).comp (contDiff_id.const_smul physicalPeriod))
  have hgp (j : Fin 3) : IsUnitPeriodicField (g j) := by
    intro u n
    have h := periodicField_rescale_unit (f j) (hp j) u n
    exact congrArg Complex.ofRealCLM h
  have hw (j i : Fin 3) (u : SpatialPoint) :
      spatialWordPartial (g j) [i] u=
        Complex.ofRealCLM (physicalPeriod*spatialWordPartial (f j) [i] (physicalPeriod • u)) := by
    have h := congrFun (spatialWordPartial_clm Complex.ofRealCLM
      (fun u => f j (physicalPeriod • u)) ((hf j).comp (contDiff_id.const_smul physicalPeriod)) [i]) u
    change spatialWordPartial (g j) [i] u=_ at h
    rw [spatialWordPartial_scale (f j) (hf j) physicalPeriod] at h
    simpa only [List.length_singleton,pow_one,smul_eq_mul] using h
  have hgc (u : SpatialPoint) (i j : Fin 3) :
      spatialWordPartial (g j) [i] u=spatialWordPartial (g i) [j] u := by
    rw [hw,hw,hc]
  have hgd (u : SpatialPoint) : (∑ j : Fin 3, spatialWordPartial (g j) [j] u)=0 := by
    simp_rw [hw]
    rw [← map_sum,← Finset.mul_sum,hd,mul_zero,map_zero]
  have h1 := unitClosed_divFree_constant g hg hgp hgc hgd j (physicalPeriod⁻¹ • x)
  have h0 := unitClosed_divFree_constant g hg hgp hgc hgd j 0
  have h := congrArg Complex.reCLM (h1.trans h0.symm)
  simpa only [g,smul_smul,mul_inv_cancel₀ physicalPeriod_pos.ne',one_smul,smul_zero,
    Complex.ofRealCLM_apply,Complex.reCLM_apply,Complex.ofReal_re] using h

/-- Original `sameSource_solenoidal_connection_difference_constant` guarantee for the `HarmonicConnection` construction; the complete source hypotheses are retained. -/
theorem sameSource_solenoidal_connection_difference_constant
    (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q r : QuaternionField) (hq : ContDiff ℝ ∞ q) (hr : ContDiff ℝ ∞ r)
    (huq : ∀ x, ‖q x‖=1) (hur : ∀ x, ‖r x‖=1)
    (hpq : IsPeriodicField q) (hpr : IsPeriodicField r)
    (hhq : ∀ x, hopf (q x)=spinOfVector (v x))
    (hhr : ∀ x, hopf (r x)=spinOfVector (v x))
    (hsq : IsSolenoidal q) (hsr : IsSolenoidal r) (j : Fin 3) (x : SpatialPoint) :
    connection r x j-connection q x j=connection r 0 j-connection q 0 j := by
  let f : Fin 3 → SpatialPoint → ℝ := fun j x => connection r x j-connection q x j
  have hf (j : Fin 3) : ContDiff ℝ ∞ (f j) :=
    (contDiff_connection r hr j).sub (contDiff_connection q hq j)
  have hp (j : Fin 3) : IsPeriodicField (f j) := by
    intro x n
    dsimp only [f]
    exact congrArg₂ (fun a b : ℝ => a-b)
      (periodicField_connection r hr hpr j x n) (periodicField_connection q hq hpq j x n)
  have hw (j i : Fin 3) (x : SpatialPoint) : spatialWordPartial (f j) [i] x=
      fderiv ℝ (fun y => connection r y j) x (EuclideanSpace.single i 1)-
        fderiv ℝ (fun y => connection q y j) x (EuclideanSpace.single i 1) := by
    have hd := ((contDiff_connection r hr j).differentiable (by simp) x).hasFDerivAt.sub
      ((contDiff_connection q hq j).differentiable (by simp) x).hasFDerivAt
    change HasFDerivAt (f j) _ x at hd
    change fderiv ℝ (f j) x (EuclideanSpace.single i 1)=_
    rw [hd.fderiv]
    rfl
  have hc (x : SpatialPoint) (i j : Fin 3) :
      spatialWordPartial (f j) [i] x=spatialWordPartial (f i) [j] x := by
    have hqC := connectionCurvature_eq_source v hv q hq huq hhq x i j
    have hrC := connectionCurvature_eq_source v hv r hr hur hhr x i j
    unfold connectionCurvature at hqC hrC
    rw [hw,hw]
    linarith
  have hd (x : SpatialPoint) : (∑ j : Fin 3, spatialWordPartial (f j) [j] x)=0 := by
    have hqD := hsq x
    have hrD := hsr x
    change (∑ j : Fin 3, fderiv ℝ (fun y => (1 : ℝ)*connection q y j) x
      (EuclideanSpace.single j 1))=0 at hqD
    change (∑ j : Fin 3, fderiv ℝ (fun y => (1 : ℝ)*connection r y j) x
      (EuclideanSpace.single j 1))=0 at hrD
    simp only [one_mul] at hqD hrD
    simp_rw [hw]
    rw [Finset.sum_sub_distrib,hrD,hqD,sub_self]
  exact physicalClosed_divFree_constant f hf hp hc hd j x

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
