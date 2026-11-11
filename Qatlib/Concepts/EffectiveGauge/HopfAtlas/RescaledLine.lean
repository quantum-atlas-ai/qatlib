/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceRescaling
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SeededPhysical

/-! # Unit-coordinate line values target the fixed original physical raw field -/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of rescaled Line Value in the Hopf Atlas construction. -/
def rescaledLineValue (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) : Quaternion ℚ :=
  let samples := rescaledSpinSamples source m1 m2
  if m1=0 then originSeedApproximation samples (tolerance/8)
  else seededPhysicalValue samples (a 1) (a 2) (a 0) (7*m1) (49*m2) tolerance

/-- Definition of rescaled Line Charged Value in the Hopf Atlas construction. -/
def rescaledLineChargedValue (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample × ℕ)
    (m1 m2 : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) : SeededPhysicalResult :=
  let samples := rescaledChargedSamples source m1 m2
  if m1=0 then
    let coarse := samples (0,4)
    let chart := chooseSeedChart coarse.1.1
    let b := seedValuePrecision (tolerance/8)
    let fine := samples (0,b)
    ⟨rationalChartSeed chart fine.1.1 b,coarse.2+fine.2,chart⟩
  else seededPhysicalChargedValue samples (a 1) (a 2) (a 0) (7*m1) (49*m2) tolerance

/-- Original `rescaledLineChargedValue_value` guarantee for the `RescaledLine` construction; the complete source hypotheses are retained. -/
theorem rescaledLineChargedValue_value (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample × ℕ)
    (m1 m2 : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) :
    (rescaledLineChargedValue source m1 m2 a tolerance).value=
      rescaledLineValue (fun q => (source q).1) m1 m2 a tolerance := by
  have he : (fun q => (rescaledChargedSamples source m1 m2 q).1)=
      rescaledSpinSamples (fun q => (source q).1) m1 m2 := funext (rescaledChargedSamples_value source m1 m2)
  dsimp only [rescaledLineChargedValue,rescaledLineValue]
  split_ifs
  · simp only [originSeedApproximation,originSeedOnChart,chosenOriginChart,originSpinSamples,
      rescaledChargedSamples,rescaledSpinSamples]
  · rw [seededPhysicalChargedValue_value,he]

/-- Definition of rescaled Line Logical Schedule in the Hopf Atlas construction. -/
def rescaledLineLogicalSchedule (m1 m2 : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) : List ((Fin 3 → ℚ) × ℕ) :=
  if m1=0 then [(0,4),(0,seedValuePrecision (tolerance/8))]
  else seededPhysicalSourceSchedule (a 1) (a 2) (a 0) (7*m1) (49*m2) tolerance

/-- Definition of rescaled Line Source Schedule in the Hopf Atlas construction. -/
def rescaledLineSourceSchedule (m1 m2 : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) : List ((Fin 3 → ℚ) × ℕ) :=
  (rescaledLineLogicalSchedule m1 m2 a tolerance).map (rescaleSourceQuery m1 m2)

/-- Original `rescaledLineSourceSchedule_length` guarantee for the `RescaledLine` construction; the complete source hypotheses are retained. -/
@[simp] theorem rescaledLineSourceSchedule_length (m1 m2 : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) :
    (rescaledLineSourceSchedule m1 m2 a tolerance).length=
      if m1=0 then 2 else 2+cayleySteps ((a 0)*(7*m1)/2) ((a 0)^2*((7*m1)^2+49*m2)/2) (tolerance/4) := by
  simp only [rescaledLineSourceSchedule,List.length_map,rescaledLineLogicalSchedule]
  split_ifs <;> simp only [List.length_cons,List.length_nil,seededPhysicalSourceSchedule_length]

noncomputable section
open scoped Quaternion ContDiff
open Set

/-- Definition of rescaled Origin Seed in the Hopf Atlas construction. -/
def rescaledOriginSeed (v : SpatialPoint → SpatialPoint)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (m1 m2 : ℚ) : ℍ :=
  exactChartSeed (chosenOriginChart (rescaledSpinSamples source m1 m2)) (sourceQuaternion v 0)

/-- Original `rescaledOriginSamples_error` guarantee for the `RescaledLine` construction; the complete source hypotheses are retained. -/
theorem rescaledOriginSamples_error (v : SpatialPoint → SpatialPoint)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (b : ℕ) :
    ∀ j, |(originSpinSamples (rescaledSpinSamples source m1 m2) b j : ℝ)-v 0 j| ≤ (2^b : ℝ)⁻¹ := by
  have he := originSpinSamples_error v source hs (b+rescaleSourceOverhead m1 m2)
  have hp : (2^b : ℝ) ≤ 2^(b+rescaleSourceOverhead m1 m2) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_add_right b _)
  have hi : (2^(b+rescaleSourceOverhead m1 m2) : ℝ)⁻¹ ≤ (2^b : ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ)<2^b) hp
  intro j
  simpa [originSpinSamples,rescaledSpinSamples,Pi.zero_def] using (he j).trans hi

/-- Original `rescaledOriginChart_valid` guarantee for the `RescaledLine` construction; the complete source hypotheses are retained. -/
theorem rescaledOriginChart_valid (v : SpatialPoint → SpatialPoint)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source) (m1 m2 : ℚ) :
    match chosenOriginChart (rescaledSpinSamples source m1 m2) with
    | .north => -(1/2 : ℝ)<(sourceQuaternion v 0).imI
    | .south => (sourceQuaternion v 0).imI<(1/2 : ℝ) := by
  apply chooseSeedChart_valid
  simpa only [sourceQuaternion,spinOfVector,show (2^4 : ℝ)⁻¹=(1/16 : ℝ) by norm_num] using rescaledOriginSamples_error v source hs m1 m2 4 0

/-- Original `rescaledOriginSeed_spec` guarantee for the `RescaledLine` construction; the complete source hypotheses are retained. -/
theorem rescaledOriginSeed_spec (v : SpatialPoint → SpatialPoint) (hu : ∀ w, ‖v w‖=1)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source) (m1 m2 : ℚ) :
    ‖rescaledOriginSeed v source m1 m2‖=1 ∧ hopf (rescaledOriginSeed v source m1 m2)=sourceQuaternion v 0 ∧
      (match chosenOriginChart (rescaledSpinSamples source m1 m2) with
      | .north => (1/2 : ℝ)<(rescaledOriginSeed v source m1 m2).re
      | .south => (1/2 : ℝ)<(rescaledOriginSeed v source m1 m2).imJ) := by
  have hn : ‖sourceQuaternion v 0‖=1 := (spinOfVector_norm _).trans (hu 0)
  have hc := rescaledOriginChart_valid v source hs m1 m2
  cases hchart : chosenOriginChart (rescaledSpinSamples source m1 m2) with
  | north =>
    simp only [hchart] at hc
    simpa only [rescaledOriginSeed,hchart] using exactChartSeed_spec .north (sourceQuaternion v 0) rfl hn hc
  | south =>
    simp only [hchart] at hc
    simpa only [rescaledOriginSeed,hchart] using exactChartSeed_spec .south (sourceQuaternion v 0) rfl hn hc

/-- Original `rescaledOriginSeed_error` guarantee for the `RescaledLine` construction; the complete source hypotheses are retained. -/
theorem rescaledOriginSeed_error (v : SpatialPoint → SpatialPoint) (hu : ∀ w, ‖v w‖=1)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 tolerance : ℚ) (ht : 0<tolerance) :
    ‖rationalQuaternionCast (originSeedApproximation (rescaledSpinSamples source m1 m2) tolerance)-
      rescaledOriginSeed v source m1 m2‖ ≤ (tolerance : ℝ) := by
  have he := rescaledOriginSamples_error v source hs m1 m2 (seedValuePrecision tolerance)
  have h := rationalChartSeed_error (chosenOriginChart (rescaledSpinSamples source m1 m2))
    (originSpinSamples (rescaledSpinSamples source m1 m2) (seedValuePrecision tolerance)) (sourceQuaternion v 0)
    ((spinOfVector_norm _).trans (hu 0)) (rescaledOriginChart_valid v source hs m1 m2)
    _ (seedValuePrecision_eight tolerance)
    (by intro j; fin_cases j <;> simpa [sourceQuaternion,spinOfVector] using he _)
  have hb : ((32*(2^seedValuePrecision tolerance : ℚ)⁻¹ : ℚ) : ℝ) ≤ (tolerance : ℝ) :=
    Rat.cast_le.mpr (seedValuePrecision_budget tolerance ht)
  push_cast at hb
  exact h.trans hb

/-- Original `scaledLine_cube` guarantee for the `RescaledLine` construction; the complete source hypotheses are retained. -/
private theorem scaledLine_cube (x y z : ℚ)
    (hx : (x : ℝ) ∈ Icc 0 1) (hy : (y : ℝ) ∈ Icc 0 1) (hz : (z : ℝ) ∈ Icc 0 1)
    (r : ℝ) (hr : r ∈ Icc 0 (physicalPeriod*(x : ℝ))) :
    InFundamentalCube (sourcePosition (physicalPeriod • rationalTransversePoint y z,r)) := by
  intro i
  fin_cases i
  · change 0 ≤ r ∧ r ≤ physicalPeriod
    exact ⟨hr.1,hr.2.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hx.2 physicalPeriod_pos.le)⟩
  · change 0 ≤ physicalPeriod*(y : ℝ) ∧ physicalPeriod*(y : ℝ) ≤ physicalPeriod
    exact ⟨mul_nonneg physicalPeriod_pos.le hy.1,by simpa only [mul_one] using mul_le_mul_of_nonneg_left hy.2 physicalPeriod_pos.le⟩
  · change 0 ≤ physicalPeriod*(z : ℝ) ∧ physicalPeriod*(z : ℝ) ≤ physicalPeriod
    exact ⟨mul_nonneg physicalPeriod_pos.le hz.1,by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.2 physicalPeriod_pos.le⟩

/-- Original `scaledLine_derivative_bounds` guarantee for the `RescaledLine` construction; the complete source hypotheses are retained. -/
private theorem scaledLine_derivative_bounds (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (m1 m2 : ℚ) (hb : SourceRescalingBounds v (m1 : ℝ) (m2 : ℝ)) (x y z : ℚ)
    (hx : (x : ℝ) ∈ Icc 0 1) (hy : (y : ℝ) ∈ Icc 0 1) (hz : (z : ℝ) ∈ Icc 0 1) :
    (∀ r ∈ Icc 0 (physicalPeriod*(x : ℝ)),
      ‖sourceXDerivative v (sourcePosition (physicalPeriod • rationalTransversePoint y z,r))‖ ≤ (m1 : ℝ)) ∧
    (∀ r ∈ Icc 0 (physicalPeriod*(x : ℝ)),
      ‖sourceXXDerivative v (sourcePosition (physicalPeriod • rationalTransversePoint y z,r))‖ ≤ (m2 : ℝ)) := by
  constructor
  · intro r hr
    rw [sourceXDerivative_eq_spin v hv,spinOfVector_norm]
    exact hb.1 _ (scaledLine_cube x y z hx hy hz r hr) 0
  · intro r hr
    rw [sourceXXDerivative_eq_spin v hv,spinOfVector_norm]
    exact hb.2 _ (scaledLine_cube x y z hx hy hz r hr) 0

/-- Original `scaledPoint_position` guarantee for the `RescaledLine` construction; the complete source hypotheses are retained. -/
private theorem scaledPoint_position (x y z t : ℚ) :
    physicalPeriod • rationalSpatialPoint (physicalLinePoint y z x t)=
      sourcePosition (physicalPeriod • rationalTransversePoint y z,(physicalPeriod*(x : ℝ))*(t : ℝ)) := by
  ext i
  fin_cases i
  · change physicalPeriod*((x*t : ℚ) : ℝ)=(physicalPeriod*(x : ℝ))*(t : ℝ)
    rw [Rat.cast_mul,mul_assoc]
  · rfl
  · rfl

/-- Original `rescaledCoefficientOracle_error` guarantee for the `RescaledLine` construction; the complete source hypotheses are retained. -/
theorem rescaledCoefficientOracle_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hb : SourceRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (x y z t : ℚ) (hx : (x : ℝ) ∈ Icc 0 1) (hy : (y : ℝ) ∈ Icc 0 1)
    (hz : (z : ℝ) ∈ Icc 0 1) (ht : (t : ℝ) ∈ Icc 0 1) (b : ℕ) :
    ‖dyadicCoefficient b (physicalCoefficientOracle (rescaledSpinSamples source m1 m2) y z x (7*m1) (t,b))-
      normalizedSourceGenerator v (physicalPeriod • rationalTransversePoint y z) (physicalPeriod*(x : ℝ)) (t : ℝ)‖ ≤
        (2^b : ℝ)⁻¹ := by
  let samples := rescaledSpinSamples source m1 m2
  let c := b+spinCoefficientOverhead (x*(7*m1))
  let p := sourcePosition (physicalPeriod • rationalTransversePoint y z,(physicalPeriod*(x : ℝ))*(t : ℝ))
  let s := sourceQuaternion v p
  let d := (physicalPeriod*(x : ℝ)) • sourceXDerivative v p
  have hxQ : 0 ≤ x := by exact_mod_cast hx.1
  have hM : 0 ≤ x*(7*m1) := by positivity
  have hline : physicalLineOverhead x=0 := by
    have hxQ : x ≤ 1 := by exact_mod_cast hx.2
    simp [physicalLineOverhead,max_eq_left hxQ]
  have hunit : ∀ i, ((physicalLinePoint y z x t) i : ℝ) ∈ Icc 0 1 := by
    intro i
    fin_cases i
    · change 0 ≤ ((x*t : ℚ) : ℝ) ∧ ((x*t : ℚ) : ℝ) ≤ 1
      rw [Rat.cast_mul]
      exact ⟨mul_nonneg hx.1 ht.1,(mul_le_mul_of_nonneg_left ht.2 hx.1).trans (by simpa only [mul_one] using hx.2)⟩
    · exact hy
    · exact hz
  have hdta := rescaledSpinSamples_error v hv source hs m1 m2 hm1 hm2 hb (physicalLinePoint y z x t) hunit c
  rw [scaledPoint_position] at hdta
  have hmem : (physicalPeriod*(x : ℝ))*(t : ℝ) ∈ Icc 0 (physicalPeriod*(x : ℝ)) :=
    ⟨mul_nonneg (mul_nonneg physicalPeriod_pos.le hx.1) ht.1,
      by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 (mul_nonneg physicalPeriod_pos.le hx.1)⟩
  have hDX : ‖sourceXDerivative v p‖ ≤ (m1 : ℝ) := (scaledLine_derivative_bounds v hv m1 m2 hb x y z hx hy hz).1 _ hmem
  have hd : ‖d‖ ≤ ((x*(7*m1) : ℚ) : ℝ) := by
    have hmR : (0 : ℝ) ≤ m1 := by exact_mod_cast hm1
    have hL : physicalPeriod ≤ (7 : ℝ) := by dsimp [physicalPeriod]; linarith [Real.pi_lt_d2]
    change ‖(physicalPeriod*(x : ℝ)) • sourceXDerivative v p‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg physicalPeriod_pos.le hx.1)]
    push_cast
    have h := mul_le_mul_of_nonneg_left hDX (mul_nonneg physicalPeriod_pos.le hx.1)
    nlinarith [mul_le_mul_of_nonneg_right hL (mul_nonneg hx.1 hmR)]
  have he : horizontalCoefficient s d=
      normalizedSourceGenerator v (physicalPeriod • rationalTransversePoint y z) (physicalPeriod*(x : ℝ)) (t : ℝ) := by
    simp only [s,d,normalizedSourceGenerator,sourceHorizontalQuaternion,horizontalCoefficient,mul_smul_comm,smul_smul]
    congr 1
    ring
  have hsc : ∀ j, (![s.imI,s.imJ,s.imK] j)=v p j := by intro j; fin_cases j <;> rfl
  have hdc : ∀ j, (![d.imI,d.imJ,d.imK] j)=(physicalPeriod*(x : ℝ))*sourcePhysicalDx v p j := by
    intro j
    fin_cases j <;> simp [d,sourceXDerivative_eq_spin v hv,spinOfVector,sourcePhysicalDx]
  have h := spinCoefficientOracle_error (x*(7*m1)) hM
    (physicalLineSamples samples y z x) t b s d rfl
    (by simp [d,sourceXDerivative_eq_spin v hv,spinOfVector])
    ((spinOfVector_norm _).trans (hu _)) hd (by rw [he]; exact normalizedSourceGenerator_re v hv hu _ _ _)
    (by
      intro j
      rw [hsc j]
      simpa only [coefficientSourceQuery,physicalLineSamples,physicalLineSourceQuery,scaledPhysicalSample,hline,Nat.add_zero]
        using hdta.1 j)
    (by
      intro j
      rw [hdc j]
      have hj := hdta.2 j
      change |((samples (physicalLinePoint y z x t,c)).2 j : ℝ)-physicalPeriod*sourcePhysicalDx v p j| ≤ (2^c : ℝ)⁻¹ at hj
      have hmul : |(x : ℝ)*((samples (physicalLinePoint y z x t,c)).2 j : ℝ)-
          (physicalPeriod*(x : ℝ))*sourcePhysicalDx v p j| ≤ (2^c : ℝ)⁻¹ := by
        rw [show (x : ℝ)*((samples (physicalLinePoint y z x t,c)).2 j : ℝ)-
          (physicalPeriod*(x : ℝ))*sourcePhysicalDx v p j=
          (x : ℝ)*(((samples (physicalLinePoint y z x t,c)).2 j : ℝ)-physicalPeriod*sourcePhysicalDx v p j) by ring,
          abs_mul,abs_of_nonneg hx.1]
        exact (mul_le_mul_of_nonneg_left hj hx.1).trans (by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hx.2 (by positivity : (0 : ℝ) ≤ (2^c : ℝ)⁻¹))
      simpa [coefficientSourceQuery,physicalLineSamples,physicalLineSourceQuery,scaledPhysicalSample,hline,c] using hmul)
  rw [he] at h
  exact h

/-- Original `sourceLine_zero` guarantee for the `RescaledLine` construction; the complete source hypotheses are retained. -/
private theorem sourceLine_zero (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (p : TransversePoint) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ physicalPeriod)
    (hz : ∀ t ∈ Icc 0 1, normalizedSourceGenerator v p x t=0) :
    sourceLiftExtension v hv q₀ h₀ (p,x)=q₀ := by
  have hd : ∀ t ∈ Icc 0 1, HasDerivWithinAt (normalizedSourceLine v hv q₀ h₀ p x) 0 (Icc 0 1) t := by
    intro t ht
    simpa only [hz t ht,mul_zero] using normalizedSourceLine_hasDerivWithinAt v hv hu q₀ h₀ p x hx t ht
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hd (fun _ _ => by simp)
    (convex_Icc (0 : ℝ) 1) (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  rw [normalizedSourceLine_initial v hv hu q₀ h₀ p x] at h
  simp only [zero_mul] at h
  have he := sub_eq_zero.mp (norm_le_zero_iff.mp h)
  simpa only [normalizedSourceLine,mul_one] using he

/-- The exact zero-generator branch is reusable by the full reference
program. It is a consequence of the ODE, not a finite-sample equality test. -/
theorem sourceLiftExtension_eq_initial_of_generator_zero (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (p : TransversePoint) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ physicalPeriod)
    (hz : ∀ t ∈ Icc 0 1, normalizedSourceGenerator v p x t=0) :
    sourceLiftExtension v hv q₀ h₀ (p,x)=q₀ := sourceLine_zero v hv hu q₀ h₀ p x hx hz

/-- The line program's unit coordinates name the exact physical point 2π*a.
The only source queries are those performed by the actual rational period
adapter. The generated seed and the target field are independent of tolerance. -/
theorem rescaledLineValue_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hb : SourceRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (a : Fin 3 → ℚ) (ha : ∀ i, (a i : ℝ) ∈ Icc 0 1) (tolerance : ℚ) (ht : 0<tolerance) (ht1 : tolerance ≤ 1) :
    ‖rationalQuaternionCast (rescaledLineValue source m1 m2 a tolerance)-
      sourceLiftSpatialExtension v hv (rescaledOriginSeed v source m1 m2)
        (rescaledOriginSeed_spec v hu source hs m1 m2).1 (physicalPeriod • rationalSpatialPoint a)‖ ≤ (tolerance : ℝ) := by
  let samples := rescaledSpinSamples source m1 m2
  let q₀ := rescaledOriginSeed v source m1 m2
  have h₀ : ‖q₀‖=1 := (rescaledOriginSeed_spec v hu source hs m1 m2).1
  let p := physicalPeriod • rationalTransversePoint (a 1) (a 2)
  let x : ℝ := physicalPeriod*(a 0 : ℝ)
  have hx : 0 ≤ x ∧ x ≤ physicalPeriod :=
    ⟨mul_nonneg physicalPeriod_pos.le (ha 0).1,by simpa only [mul_one] using mul_le_mul_of_nonneg_left (ha 0).2 physicalPeriod_pos.le⟩
  have hm1R : (0 : ℝ) ≤ m1 := by exact_mod_cast hm1
  have hm2R : (0 : ℝ) ≤ m2 := by exact_mod_cast hm2
  have hder := scaledLine_derivative_bounds v hv m1 m2 hb (a 0) (a 1) (a 2) (ha 0) (ha 1) (ha 2)
  have hreg := normalizedSourceGenerator_bounds v hv hu p x hx.1 (m1 : ℝ) (m2 : ℝ) hm1R hder.1 hder.2
  have hseed : ‖rationalQuaternionCast (originSeedApproximation samples (tolerance/8))-q₀‖ ≤ (tolerance : ℝ)/8 := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using rescaledOriginSeed_error v hu source hs m1 m2 (tolerance/8) (by positivity)
  have hpos : sourcePositionInverse (physicalPeriod • rationalSpatialPoint a)=(p,x) := by
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · rfl
  change ‖rationalQuaternionCast (rescaledLineValue source m1 m2 a tolerance)-
    sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • rationalSpatialPoint a)‖ ≤ _
  rw [sourceLiftSpatialExtension,hpos]
  by_cases hz : m1=0
  · have hk : ∀ t ∈ Icc 0 1, normalizedSourceGenerator v p x t=0 := by
      intro t htu
      have h := hreg.1 t htu
      rw [hz] at h
      simp only [Rat.cast_zero,mul_zero,zero_div] at h
      exact norm_le_zero_iff.mp h
    rw [rescaledLineValue,if_pos hz,sourceLine_zero v hv hu q₀ h₀ p x hx hk]
    exact hseed.trans (by
      have hp : (0 : ℝ)<tolerance := by exact_mod_cast ht
      linarith)
  · let K : ℚ := (a 0)*(7*m1)/2
    let M : ℚ := (a 0)^2*((7*m1)^2+49*m2)/2
    have hL : physicalPeriod ≤ (7 : ℝ) := by dsimp [physicalPeriod]; linarith [Real.pi_lt_d2]
    have hL2 : physicalPeriod^2 ≤ (49 : ℝ) := by
      simpa only [show (7 : ℝ)^2=49 by norm_num] using (sq_le_sq₀ physicalPeriod_pos.le (by norm_num : (0 : ℝ) ≤ 7)).mpr hL
    have hK : 0 ≤ K := by
      have hq : 0 ≤ a 0 := by exact_mod_cast (ha 0).1
      dsimp [K]
      positivity
    have hnorm : ∀ t ∈ Icc 0 1, ‖normalizedSourceGenerator v p x t‖ ≤ (K : ℝ) := by
      intro t htu
      apply (hreg.1 t htu).trans
      dsimp [x,K]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hL (mul_nonneg (ha 0).1 hm1R)]
    have hfactor : x^2*((m1 : ℝ)^2+(m2 : ℝ))/2 ≤ (M : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hL2
        (show 0 ≤ (a 0 : ℝ)^2*((m1 : ℝ)^2+(m2 : ℝ))/2 by positivity)
      dsimp [x,M]
      push_cast
      nlinarith only [h]
    have hlip : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
        ‖normalizedSourceGenerator v p x t-normalizedSourceGenerator v p x s‖ ≤ (M : ℝ)*|t-s| := by
      intro s hsu t htu
      exact (hreg.2 s hsu t htu).trans (mul_le_mul_of_nonneg_right hfactor (abs_nonneg _))
    have horacle : ∀ j<cayleySteps K M (tolerance/4),
        ‖dyadicCoefficient (cayleyPrecision (tolerance/4))
          (physicalCoefficientOracle samples (a 1) (a 2) (a 0) (7*m1)
            ((j : ℚ)/(cayleySteps K M (tolerance/4) : ℚ),cayleyPrecision (tolerance/4)))-
          normalizedSourceGenerator v p x ((j : ℝ)/(cayleySteps K M (tolerance/4) : ℝ))‖ ≤
            (2^cayleyPrecision (tolerance/4) : ℝ)⁻¹ := by
      intro j hj
      have hD : (0 : ℝ)<cayleySteps K M (tolerance/4) := by exact_mod_cast (cayleySteps_spec K M (tolerance/4)).1
      have h := rescaledCoefficientOracle_error v hv hu source hs m1 m2 hm1 hm2 hb
        (a 0) (a 1) (a 2) ((j : ℚ)/(cayleySteps K M (tolerance/4) : ℚ))
        (ha 0) (ha 1) (ha 2) (by
          push_cast
          exact ⟨div_nonneg (Nat.cast_nonneg j) hD.le,(div_le_one hD).mpr (by exact_mod_cast Nat.le_of_lt hj)⟩)
        (cayleyPrecision (tolerance/4))
      push_cast at h
      exact h
    have h := cayleyPlannedSource_error v hv hu q₀ h₀ p x hx K M (tolerance/4) hK (by positivity) (by linarith)
      (physicalCoefficientOracle samples (a 1) (a 2) (a 0) (7*m1)) hnorm hlip horacle
      (rationalQuaternionCast (originSeedApproximation samples (tolerance/8))) ((tolerance : ℝ)/8) hseed
    rw [rescaledLineValue,if_neg hz,seededPhysicalValue,map_mul,rationalCayleyValue_cast,physicalCayleyExecution]
    push_cast at h
    have hp : (0 : ℝ)<tolerance := by exact_mod_cast ht
    linarith

/-- Original `rescaledOriginRaw_from_support` guarantee for the `RescaledLine` construction; the complete source hypotheses are retained. -/
theorem rescaledOriginRaw_from_support (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (B : Set SpatialPoint) (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ t, OnCubeBoundary t → mu ≤ ‖w-t‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b) :
    IsSmoothUnitLift (sourceQuaternion v)
      (sourceLiftSpatialExtension v hv (rescaledOriginSeed v source m1 m2) (rescaledOriginSeed_spec v hu source hs m1 m2).1) :=
  sourceLiftSpatialExtension_isSmoothUnitLift v hv hu _ _ (spin_field_periodic hp) (mu/2) (by positivity)
    (sourceQuaternion v 0) (support_background_collar v B hB mu hm hg hoff) (rescaledOriginSeed_spec v hu source hs m1 m2).2.1

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
