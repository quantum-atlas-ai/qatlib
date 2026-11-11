/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.IntegerGauge
import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonThirdBound

set_option backward.isDefEq.respectTransparency false

/-!
# Gauge Positive Phase

Hopf Atlas constructions for Effective Gauge.
Defines `normalizedGaugePhase`, `gaugeWindingSize`, `gaugePositivePhaseModulus`.
Proves `spatialWordPartial_linear_real`, `selectedPoissonGauge_normalized`, `normalizedConnectionPoisson_word_bound_third`.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original `spatialWordPartial_linear_real` guarantee for the `GaugePositivePhase` construction; the complete source hypotheses are retained. -/
theorem spatialWordPartial_linear_real (A : SpatialPoint →L[ℝ] ℝ) (w : List (Fin 3)) :
    spatialWordPartial (fun x => A x) w=
      match w with
      | [] => fun x => A x
      | [i] => fun _ => A (EuclideanSpace.single i 1)
      | _ => fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    cases w with
    | nil =>
      funext x
      change fderiv ℝ (fun y => A y) x (EuclideanSpace.single i 1)=A (EuclideanSpace.single i 1)
      rw [A.hasFDerivAt.fderiv]
    | cons j rest =>
      change (fun x => fderiv ℝ (spatialWordPartial (fun y => A y) (j::rest)) x
        (EuclideanSpace.single i 1))=_
      rw [ih]
      cases rest with
      | nil => funext x; simp
      | cons k rest => funext x; simp

/-- Definition of normalized Gauge Phase in the Hopf Atlas construction. -/
def normalizedGaugePhase (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hp : IsPeriodicField q)
    (n : SpatialFrequency) (u : SpatialPoint) : ℝ :=
  physicalPeriod*windingLinear n u+normalizedConnectionPoisson q hq hp u-normalizedConnectionPoisson q hq hp 0

/-- Original `selectedPoissonGauge_normalized` guarantee for the `GaugePositivePhase` construction; the complete source hypotheses are retained. -/
theorem selectedPoissonGauge_normalized (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hp : IsPeriodicField q)
    (result : SourceMeanSectorResult) :
    (fun u => selectedPoissonGauge q hq hp result (physicalPeriod • u))=
      fun u => phase (normalizedGaugePhase q hq hp (selectedSectorWinding result) u)*q (physicalPeriod • u) := by
  funext u
  dsimp only [selectedPoissonGauge,integerGauge,poissonCorrectedLift,physicalPoissonPhase,normalizedGaugePhase]
  rw [smul_smul,inv_mul_cancel₀ physicalPeriod_pos.ne',one_smul,← mul_assoc,← phase_add]
  congr 2
  simp only [map_smul,smul_eq_mul]
  ring

/-- Original `normalizedConnectionPoisson_word_bound_third` guarantee for the `GaugePositivePhase` construction; the complete source hypotheses are retained. -/
theorem normalizedConnectionPoisson_word_bound_third (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (M : ℝ)
    (hb : ∀ j i x, InUnitCube x →
      ‖spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) x‖ ≤ M)
    (w : List (Fin 3)) (hw : w.length≤3) (x : SpatialPoint) :
    ‖spatialWordPartial (normalizedConnectionPoisson q hq hp) w x‖ ≤ 156*M := by
  apply unitRealPoisson_word_bound_third (normalizedConnectionComplex q)
    (contDiff_normalizedConnectionComplex q hq) (unitPeriodic_normalizedConnectionComplex q hq hp) M _ w hw x
  intro j i y hy
  change ‖spatialWordPartial (fun z => Complex.ofRealCLM (normalizedConnectionReal q j z))
    (List.replicate 6 i) y‖ ≤ M
  rw [spatialWordPartial_clm Complex.ofRealCLM (normalizedConnectionReal q j)
    (contDiff_normalizedConnectionReal q hq j)]
  change ‖((spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) y : ℝ) : ℂ)‖ ≤ M
  rw [Complex.norm_real]
  exact hb j i y hy

/-- Definition of gauge Winding Size in the Hopf Atlas construction. -/
def gaugeWindingSize (n : SpatialFrequency) : ℚ := ∑ j : Fin 3, |(n j : ℚ)|

/-- Definition of gauge Positive Phase Modulus in the Hopf Atlas construction. -/
def gaugePositivePhaseModulus (C6 : ℚ) (n : SpatialFrequency) (r : ℕ) : ℚ :=
  if r=1 then 7*gaugeWindingSize n+156*C6 else 156*C6

/-- Original `gaugeWindingSize_bound` guarantee for the `GaugePositivePhase` construction; the complete source hypotheses are retained. -/
theorem gaugeWindingSize_bound (n : SpatialFrequency) (j : Fin 3) :
    |(n j : ℝ)| ≤ (gaugeWindingSize n : ℝ) := by
  have h : |(n j : ℚ)| ≤ ∑ i : Fin 3, |(n i : ℚ)| :=
    Finset.single_le_sum (fun (i : Fin 3) _ => abs_nonneg (n i : ℚ)) (Finset.mem_univ j)
  have hcast := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hcast
  simpa only [gaugeWindingSize,Rat.cast_sum,Rat.cast_abs,Rat.cast_intCast] using hcast

/-- Original `normalizedGaugePhase_positive_bound` guarantee for the `GaugePositivePhase` construction; the complete source hypotheses are retained. -/
theorem normalizedGaugePhase_positive_bound (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hp : IsPeriodicField q)
    (C6 : ℚ)
    (hC6 : ∀ j i x, InUnitCube x →
      ‖spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) x‖ ≤ (C6 : ℝ))
    (n : SpatialFrequency) (w : List (Fin 3)) (hw0 : 0<w.length) (hw : w.length ≤ 3) (x : SpatialPoint) :
    ‖spatialWordPartial (normalizedGaugePhase q hq hp n) w x‖ ≤
      (gaugePositivePhaseModulus C6 n w.length : ℝ) := by
  let chi := normalizedConnectionPoisson q hq hp
  let A : SpatialPoint →L[ℝ] ℝ := physicalPeriod • windingLinear n
  have hc : ContDiff ℝ ∞ chi := (normalizedConnectionPoisson_spec q hq hp).1
  have hne : w≠[] := by intro h; simp only [h,List.length_nil] at hw0; omega
  have heq : normalizedGaugePhase q hq hp n=(fun y => (A y+chi y)+(-chi 0)) := by
    funext y
    simp only [normalizedGaugePhase,A,chi,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  have hword : spatialWordPartial (normalizedGaugePhase q hq hp n) w x=
      spatialWordPartial (fun y => A y) w x+spatialWordPartial chi w x := by
    rw [heq,spatialWordPartial_add _ _ (A.contDiff.add hc) contDiff_const,
      spatialWordPartial_add _ _ A.contDiff hc,spatialWordPartial_const]
    simp only [hne,if_false,add_zero]
  have hlin : ‖spatialWordPartial (fun y => A y) w x‖ ≤
      if w.length=1 then 7*(gaugeWindingSize n : ℝ) else 0 := by
    cases w with
    | nil => simp only [List.length_nil] at hw0; omega
    | cons i rest =>
      cases rest with
      | nil =>
        simp only [spatialWordPartial_linear_real,List.length_cons,List.length_nil,zero_add,ite_true]
        simp only [A,ContinuousLinearMap.smul_apply,smul_eq_mul,windingLinear_basis,Real.norm_eq_abs]
        rw [abs_mul,abs_of_pos physicalPeriod_pos]
        have hL : physicalPeriod ≤ 7 := by dsimp only [physicalPeriod]; linarith [Real.pi_lt_d2]
        exact mul_le_mul hL (gaugeWindingSize_bound n i) (abs_nonneg _) (by norm_num)
      | cons j rest =>
        have hn : (i::j::rest).length≠1 := by simp only [List.length_cons]; omega
        simpa only [spatialWordPartial_linear_real,if_neg hn,norm_zero] using (le_refl (0 : ℝ))
  have hchi := normalizedConnectionPoisson_word_bound_third q hq hp (C6 : ℝ) hC6 w hw x
  rw [hword]
  have hsum := (norm_add_le _ _).trans (add_le_add hlin hchi)
  dsimp only [gaugePositivePhaseModulus]
  split_ifs with h
  · simpa only [h,ite_true,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat] using hsum
  · simpa only [h,ite_false,zero_add,Rat.cast_mul,Rat.cast_ofNat] using hsum

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
