/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.SeedApproximation
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SupportGeometry

/-!
# Original source to seeded rational physical values

No initial quaternion or lift is supplied. A standalone value call selects
the chart with one coarse query, then makes one fine seed query and the
transport queries. A persistent Reference may cache that coarse chart.
This constructs raw lift values; periodic phase correction is separate.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of rational Cayley Value in the Hopf Atlas construction. -/
def rationalCayleyValue (s : CayleyIntegerState) : Quaternion ℚ :=
  ((s.denominator : ℚ)⁻¹) •
    (⟨(s.numerator.re : ℚ),(s.numerator.imI : ℚ),(s.numerator.imJ : ℚ),(s.numerator.imK : ℚ)⟩ : Quaternion ℚ)

/-- Definition of seeded Physical Value in the Hopf Atlas construction. -/
def seededPhysicalValue (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (y z x m1 m2 tolerance : ℚ) : Quaternion ℚ :=
  originSeedApproximation source (tolerance/8)*
    rationalCayleyValue (physicalCayleyExecution source y z x m1 m2 (tolerance/4))

/-- Data and hypotheses for Seeded Physical Result in the Hopf Atlas construction. -/
structure SeededPhysicalResult where
  value : Quaternion ℚ
  sourceFee : ℕ
  chart : SeedChart

/-- Definition of seeded Physical Charged Value in the Hopf Atlas construction. -/
def seededPhysicalChargedValue (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample × ℕ)
    (y z x m1 m2 tolerance : ℚ) : SeededPhysicalResult :=
  let coarse := source (0,4)
  let chart := chooseSeedChart coarse.1.1
  let b := seedValuePrecision (tolerance/8)
  let fine := source (0,b)
  let seed := rationalChartSeed chart fine.1.1 b
  let transported := physicalCayleyChargedExecution source y z x m1 m2 (tolerance/4)
  ⟨seed*rationalCayleyValue transported.state,coarse.2+fine.2+transported.sourceFee,chart⟩

/-- Original `seededPhysicalChargedValue_value` guarantee for the `SeededPhysical` construction; the complete source hypotheses are retained. -/
theorem seededPhysicalChargedValue_value (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample × ℕ)
    (y z x m1 m2 tolerance : ℚ) :
    (seededPhysicalChargedValue source y z x m1 m2 tolerance).value=
      seededPhysicalValue (fun label => (source label).1) y z x m1 m2 tolerance := by
  simp only [seededPhysicalChargedValue,physicalCayleyChargedExecution_state,seededPhysicalValue,
    originSeedApproximation,originSeedOnChart,chosenOriginChart,originSpinSamples]

/-- Definition of seeded Physical Source Schedule in the Hopf Atlas construction. -/
def seededPhysicalSourceSchedule (y z x m1 m2 tolerance : ℚ) : List ((Fin 3 → ℚ) × ℕ) :=
  [(0,4),(0,seedValuePrecision (tolerance/8))]++physicalCayleySourceSchedule y z x m1 m2 (tolerance/4)

/-- Original `seededPhysicalSourceSchedule_length` guarantee for the `SeededPhysical` construction; the complete source hypotheses are retained. -/
@[simp] theorem seededPhysicalSourceSchedule_length (y z x m1 m2 tolerance : ℚ) :
    (seededPhysicalSourceSchedule y z x m1 m2 tolerance).length=
      2+cayleySteps (x*m1/2) (x^2*(m1^2+m2)/2) (tolerance/4) := by
  simp only [seededPhysicalSourceSchedule,List.length_append,List.length_cons,List.length_nil,
    physicalCayleySourceSchedule_length]

/-- Original `seededPhysicalChargedValue_fee_le` guarantee for the `SeededPhysical` construction; the complete source hypotheses are retained. -/
theorem seededPhysicalChargedValue_fee_le (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample × ℕ)
    (y z x m1 m2 tolerance : ℚ) (T : ℕ)
    (hcoarse : (source (0,4)).2 ≤ T)
    (hfine : (source (0,seedValuePrecision (tolerance/8))).2 ≤ T)
    (hword : ∀ j < cayleySteps (x*m1/2) (x^2*(m1^2+m2)/2) (tolerance/4),
      (source (physicalCoefficientSourceQuery y z x m1
        ((j : ℚ)/(cayleySteps (x*m1/2) (x^2*(m1^2+m2)/2) (tolerance/4) : ℚ),
          cayleyPrecision (tolerance/4)))).2 ≤ T) :
    (seededPhysicalChargedValue source y z x m1 m2 tolerance).sourceFee ≤
      (2+cayleySteps (x*m1/2) (x^2*(m1^2+m2)/2) (tolerance/4))*T := by
  have hw := physicalCayleyChargedExecution_fee_le source y z x m1 m2 (tolerance/4) T hword
  change (source (0,4)).2+(source (0,seedValuePrecision (tolerance/8))).2+_ ≤ _
  calc
    _ ≤ T+T+cayleySteps (x*m1/2) (x^2*(m1^2+m2)/2) (tolerance/4)*T :=
      Nat.add_le_add (Nat.add_le_add hcoarse hfine) hw
    _ = _ := by ring

noncomputable section
open scoped Quaternion ContDiff
open Set

/-- Original `seededPhysicalSourceSchedule_legal` guarantee for the `SeededPhysical` construction; the complete source hypotheses are retained. -/
theorem seededPhysicalSourceSchedule_legal (y z x m1 m2 tolerance : ℚ)
    (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ physicalPeriod)
    (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ physicalPeriod)
    (hz : 0 ≤ (z : ℝ) ∧ (z : ℝ) ≤ physicalPeriod) :
    ∀ query ∈ seededPhysicalSourceSchedule y z x m1 m2 tolerance,
      ∀ i, 0 ≤ (query.1 i : ℝ) ∧ (query.1 i : ℝ) ≤ physicalPeriod := by
  intro query hq
  simp only [seededPhysicalSourceSchedule,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with (rfl | rfl) | hq
  · intro i
    simpa using (show (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ physicalPeriod from ⟨le_rfl,physicalPeriod_pos.le⟩)
  · intro i
    simpa using (show (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ physicalPeriod from ⟨le_rfl,physicalPeriod_pos.le⟩)
  · exact physicalCayleySourceSchedule_legal y z x m1 m2 (tolerance/4) hx hy hz query hq

/-- Original `rationalCayleyValue_cast` guarantee for the `SeededPhysical` construction; the complete source hypotheses are retained. -/
theorem rationalCayleyValue_cast (s : CayleyIntegerState) :
    rationalQuaternionCast (rationalCayleyValue s)=decodeCayleyState s := by
  ext <;> simp [rationalCayleyValue,rationalQuaternionCast,decodeCayleyState,integerQuaternionCast]

/-- Original source accuracy and regularity are the only approximation inputs.
The target seed is fixed by the same coarse callback query at every tolerance. -/
theorem seededPhysicalValue_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (hs : OriginalSpinSourceAccurate v source) (y z x m1 m2 tolerance : ℚ)
    (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ physicalPeriod)
    (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ physicalPeriod)
    (hz : 0 ≤ (z : ℝ) ∧ (z : ℝ) ≤ physicalPeriod) (hm1 : 0 ≤ m1)
    (ht : 0<tolerance) (ht1 : tolerance ≤ 1)
    (h1 : ∀ u ∈ Icc 0 (x : ℝ), ‖sourceXDerivative v (sourcePosition (rationalTransversePoint y z,u))‖ ≤ (m1 : ℝ))
    (h2 : ∀ u ∈ Icc 0 (x : ℝ), ‖sourceXXDerivative v (sourcePosition (rationalTransversePoint y z,u))‖ ≤ (m2 : ℝ)) :
    ‖rationalQuaternionCast (seededPhysicalValue source y z x m1 m2 tolerance)-
      sourceLiftSpatialExtension v hv (chosenOriginSeed v source) (chosenOriginSeed_spec v hu source hs).1
        (rationalSpatialPoint ![x,y,z])‖ ≤ (tolerance : ℝ) := by
  have hseed : ‖rationalQuaternionCast (originSeedApproximation source (tolerance/8))-chosenOriginSeed v source‖ ≤
      (tolerance : ℝ)/8 := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using originSeedApproximation_error v hu source hs (tolerance/8) (by positivity)
  have h := physicalCayleyExecution_error v hv hu source hs y z x m1 m2 (tolerance/4) hx hy hz hm1
    (by positivity) (by linarith) h1 h2 (chosenOriginSeed v source) (chosenOriginSeed_spec v hu source hs).1
    (rationalQuaternionCast (originSeedApproximation source (tolerance/8))) ((tolerance : ℝ)/8) hseed
  have hpos : sourcePositionInverse (rationalSpatialPoint ![x,y,z])=(rationalTransversePoint y z,(x : ℝ)) := by
    apply Prod.ext
    · ext j; fin_cases j <;> rfl
    · rfl
  rw [seededPhysicalValue,map_mul,rationalCayleyValue_cast,sourceLiftSpatialExtension,hpos]
  push_cast at h
  have hp : (0 : ℝ)<tolerance := by exact_mod_cast ht
  linarith

/-- Source support geometry supplies the initial face compatibility. The
generated exact raw field has unit norm and the right Hopf image globally;
this theorem does not assert periodicity of that raw field. -/
theorem chosenOriginRaw_from_support (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (B : Set SpatialPoint) (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ t, OnCubeBoundary t → mu ≤ ‖w-t‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b) :
    IsSmoothUnitLift (sourceQuaternion v)
      (sourceLiftSpatialExtension v hv (chosenOriginSeed v source) (chosenOriginSeed_spec v hu source hs).1) :=
  sourceLiftSpatialExtension_isSmoothUnitLift v hv hu _ _ (spin_field_periodic hp) (mu/2) (by positivity)
    (sourceQuaternion v 0) (support_background_collar v B hB mu hm hg hoff) (chosenOriginSeed_spec v hu source hs).2.1

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
