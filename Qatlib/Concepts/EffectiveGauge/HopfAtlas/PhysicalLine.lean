/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SpinCoefficient
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceRegularity

/-!
# Rational physical source access for the Cayley line kernel

All calls below use physical rational points (x*t,y,z). For x>1 a finite
extra precision compensates the derivative multiplication by x. No irrational
point or lift oracle is queried. The initial chart approximation and its error
remain separate; this is not the full periodic-reference backend.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of physical Line Point in the Hopf Atlas construction. -/
def physicalLinePoint (y z x t : ℚ) : Fin 3 → ℚ := ![x*t,y,z]

/-- Definition of physical Line Overhead in the Hopf Atlas construction. -/
def physicalLineOverhead (x : ℚ) : ℕ := Nat.clog 2 (Nat.ceil (max 1 x))

/-- Definition of physical Line Source Query in the Hopf Atlas construction. -/
def physicalLineSourceQuery (y z x : ℚ) (label : ℚ × ℕ) : (Fin 3 → ℚ) × ℕ :=
  (physicalLinePoint y z x label.1,label.2+physicalLineOverhead x)

/-- Definition of scaled Physical Sample in the Hopf Atlas construction. -/
def scaledPhysicalSample (x : ℚ) (a : RationalSpinSample) : RationalSpinSample :=
  (a.1,fun j => x*a.2 j)

/-- Definition of physical Line Samples in the Hopf Atlas construction. -/
def physicalLineSamples (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (y z x : ℚ) (label : ℚ × ℕ) : RationalSpinSample :=
  scaledPhysicalSample x (source (physicalLineSourceQuery y z x label))

/-- Definition of physical Coefficient Oracle in the Hopf Atlas construction. -/
def physicalCoefficientOracle (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (y z x m1 : ℚ) : ℚ × ℕ → Fin 3 → ℤ :=
  spinCoefficientOracle (x*m1) (physicalLineSamples source y z x)

/-- Definition of physical Coefficient Source Query in the Hopf Atlas construction. -/
def physicalCoefficientSourceQuery (y z x m1 : ℚ) (label : ℚ × ℕ) : (Fin 3 → ℚ) × ℕ :=
  physicalLineSourceQuery y z x (coefficientSourceQuery (x*m1) label)

/-- Original `physicalCoefficientSourceQuery_eq` guarantee for the `PhysicalLine` construction; the complete source hypotheses are retained. -/
theorem physicalCoefficientSourceQuery_eq (y z x m1 : ℚ) (label : ℚ × ℕ) :
    physicalCoefficientSourceQuery y z x m1 label=
      (physicalLinePoint y z x label.1,label.2+spinCoefficientOverhead (x*m1)+physicalLineOverhead x) := rfl

/-- Definition of physical Cayley Execution in the Hopf Atlas construction. -/
def physicalCayleyExecution (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (y z x m1 m2 tolerance : ℚ) : CayleyIntegerState :=
  cayleyPlannedExecution (x*m1/2) (x^2*(m1^2+m2)/2) tolerance (physicalCoefficientOracle source y z x m1)

/-- Definition of physical Cayley Source Schedule in the Hopf Atlas construction. -/
def physicalCayleySourceSchedule (y z x m1 m2 tolerance : ℚ) : List ((Fin 3 → ℚ) × ℕ) :=
  (cayleyQuerySchedule (cayleySteps (x*m1/2) (x^2*(m1^2+m2)/2) tolerance) (cayleyPrecision tolerance)).map
    (physicalCoefficientSourceQuery y z x m1)

/-- A single source answer supplies both its spin/derivative sample and its
reported evaluation fee. Arithmetic work is not included in this fee. -/
def physicalCayleyChargedExecution (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample × ℕ)
    (y z x m1 m2 tolerance : ℚ) : CayleyChargedResult :=
  cayleyChargedExecution (cayleySteps (x*m1/2) (x^2*(m1^2+m2)/2) tolerance) (cayleyPrecision tolerance)
    (fun label =>
      let answer := source (physicalCoefficientSourceQuery y z x m1 label)
      (roundedHorizontalSample (scaledPhysicalSample x answer.1) label.2,answer.2))

/-- Original `physicalCayleyChargedExecution_state` guarantee for the `PhysicalLine` construction; the complete source hypotheses are retained. -/
theorem physicalCayleyChargedExecution_state (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample × ℕ)
    (y z x m1 m2 tolerance : ℚ) :
    (physicalCayleyChargedExecution source y z x m1 m2 tolerance).state=
      physicalCayleyExecution (fun label => (source label).1) y z x m1 m2 tolerance := by
  simp only [physicalCayleyChargedExecution,cayleyChargedExecution_state,physicalCayleyExecution,
    cayleyPlannedExecution,physicalCoefficientOracle,physicalCoefficientSourceQuery]
  rfl

/-- Original `physicalCayleyChargedExecution_fee_le` guarantee for the `PhysicalLine` construction; the complete source hypotheses are retained. -/
theorem physicalCayleyChargedExecution_fee_le (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample × ℕ)
    (y z x m1 m2 tolerance : ℚ) (T : ℕ)
    (hfee : ∀ j < cayleySteps (x*m1/2) (x^2*(m1^2+m2)/2) tolerance,
      (source (physicalCoefficientSourceQuery y z x m1
        ((j : ℚ)/(cayleySteps (x*m1/2) (x^2*(m1^2+m2)/2) tolerance : ℚ),cayleyPrecision tolerance))).2 ≤ T) :
    (physicalCayleyChargedExecution source y z x m1 m2 tolerance).sourceFee ≤
      cayleySteps (x*m1/2) (x^2*(m1^2+m2)/2) tolerance*T :=
  cayleyChargedExecution_fee_le _ _ T _ hfee

/-- Original `physicalLineOverhead_bound` guarantee for the `PhysicalLine` construction; the complete source hypotheses are retained. -/
theorem physicalLineOverhead_bound (x : ℚ) :
    1 ≤ (2^physicalLineOverhead x : ℚ) ∧ x ≤ (2^physicalLineOverhead x : ℚ) := by
  have hpow : Nat.ceil (max 1 x) ≤ 2^physicalLineOverhead x := Nat.le_pow_clog (by decide) _
  have h : max 1 x ≤ (2^physicalLineOverhead x : ℚ) := (Nat.le_ceil _).trans (by exact_mod_cast hpow)
  exact ⟨(le_max_left _ _).trans h,(le_max_right _ _).trans h⟩

/-- Original `physicalLineOverhead_error` guarantee for the `PhysicalLine` construction; the complete source hypotheses are retained. -/
theorem physicalLineOverhead_error (x : ℚ) (b : ℕ) :
    (2^(b+physicalLineOverhead x) : ℚ)⁻¹ ≤ (2^b : ℚ)⁻¹ ∧
      x*(2^(b+physicalLineOverhead x) : ℚ)⁻¹ ≤ (2^b : ℚ)⁻¹ := by
  obtain ⟨h1,hx⟩ := physicalLineOverhead_bound x
  have hp : (0 : ℚ)<2^b := by positivity
  have ho : (0 : ℚ)<2^physicalLineOverhead x := by positivity
  have hi : (2^physicalLineOverhead x : ℚ)⁻¹ ≤ 1 := (inv_le_one₀ ho).mpr h1
  have hxi : x*(2^physicalLineOverhead x : ℚ)⁻¹ ≤ 1 := by
    simpa only [div_eq_mul_inv] using (div_le_one ho).mpr hx
  constructor
  · rw [pow_add,mul_inv_rev]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hi (inv_nonneg.mpr hp.le)
  · calc
      _ = (x*(2^physicalLineOverhead x : ℚ)⁻¹)*(2^b : ℚ)⁻¹ := by rw [pow_add,mul_inv_rev,mul_assoc]
      _ ≤ 1*(2^b : ℚ)⁻¹ := mul_le_mul_of_nonneg_right hxi (inv_nonneg.mpr hp.le)
      _ = _ := one_mul _

/-- Original `physicalCayleySourceSchedule_length` guarantee for the `PhysicalLine` construction; the complete source hypotheses are retained. -/
@[simp] theorem physicalCayleySourceSchedule_length (y z x m1 m2 tolerance : ℚ) :
    (physicalCayleySourceSchedule y z x m1 m2 tolerance).length=
      cayleySteps (x*m1/2) (x^2*(m1^2+m2)/2) tolerance := by simp [physicalCayleySourceSchedule]

noncomputable section
open scoped Quaternion RealInnerProductSpace ContDiff
open Set

/-- Definition of rational Spatial Point in the Hopf Atlas construction. -/
def rationalSpatialPoint (a : Fin 3 → ℚ) : SpatialPoint := WithLp.toLp 2 (fun j => (a j : ℝ))

/-- Definition of rational Transverse Point in the Hopf Atlas construction. -/
def rationalTransversePoint (y z : ℚ) : TransversePoint := WithLp.toLp 2 ![(y : ℝ),(z : ℝ)]

/-- Original `physicalLinePoint_cast` guarantee for the `PhysicalLine` construction; the complete source hypotheses are retained. -/
theorem physicalLinePoint_cast (y z x t : ℚ) : rationalSpatialPoint (physicalLinePoint y z x t)=
    sourcePosition (rationalTransversePoint y z,(x : ℝ)*(t : ℝ)) := by
  ext j
  fin_cases j
  · change ((x*t : ℚ) : ℝ)=(x : ℝ)*(t : ℝ)
    exact Rat.cast_mul x t
  · rfl
  · rfl

/-- The original source contract concerns only the spin and its physical
x derivative, at legal rational points. No coefficient or lift accuracy is
assumed here. Higher input derivatives are used separately as regularity data. -/
def OriginalSpinSourceAccurate (v : SpatialPoint → SpatialPoint)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) : Prop :=
  ∀ (a : Fin 3 → ℚ) (b : ℕ), (∀ j, 0 ≤ (a j : ℝ) ∧ (a j : ℝ) ≤ physicalPeriod) →
    (∀ j, |((source (a,b)).1 j : ℝ)-v (rationalSpatialPoint a) j| ≤ (2^b : ℝ)⁻¹) ∧
    (∀ j, |((source (a,b)).2 j : ℝ)-fderiv ℝ v (rationalSpatialPoint a) (EuclideanSpace.single 0 1) j| ≤
      (2^b : ℝ)⁻¹)

/-- Original `physicalLinePoint_in_cube` guarantee for the `PhysicalLine` construction; the complete source hypotheses are retained. -/
theorem physicalLinePoint_in_cube (y z x t : ℚ)
    (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ physicalPeriod)
    (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ physicalPeriod)
    (hz : 0 ≤ (z : ℝ) ∧ (z : ℝ) ≤ physicalPeriod)
    (ht : (t : ℝ) ∈ Icc 0 1) :
    ∀ j, 0 ≤ ((physicalLinePoint y z x t) j : ℝ) ∧ ((physicalLinePoint y z x t) j : ℝ) ≤ physicalPeriod := by
  intro j
  fin_cases j
  · change 0 ≤ ((x*t : ℚ) : ℝ) ∧ ((x*t : ℚ) : ℝ) ≤ physicalPeriod
    rw [Rat.cast_mul]
    exact ⟨mul_nonneg hx.1 ht.1,(mul_le_mul_of_nonneg_left ht.2 hx.1).trans (by simpa using hx.2)⟩
  · exact hy
  · exact hz

/-- Original `physicalGrid_mem` guarantee for the `PhysicalLine` construction; the complete source hypotheses are retained. -/
private theorem physicalGrid_mem (D : ℕ) (hD : 0<D) (j : ℕ) (hj : j<D) :
    (((j : ℚ)/(D : ℚ) : ℚ) : ℝ) ∈ Icc 0 1 := by
  have hDr : (0 : ℝ)<D := by exact_mod_cast hD
  push_cast
  exact ⟨div_nonneg (Nat.cast_nonneg j) hDr.le,(div_le_one hDr).mpr (by exact_mod_cast Nat.le_of_lt hj)⟩

/-- Every entry in the actual finite source-query schedule is legal, including
queries on a face. No nonrational endpoint is passed to the source. -/
theorem physicalCayleySourceSchedule_legal (y z x m1 m2 tolerance : ℚ)
    (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ physicalPeriod)
    (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ physicalPeriod)
    (hz : 0 ≤ (z : ℝ) ∧ (z : ℝ) ≤ physicalPeriod) :
    ∀ entry ∈ physicalCayleySourceSchedule y z x m1 m2 tolerance,
      ∀ i, 0 ≤ (entry.1 i : ℝ) ∧ (entry.1 i : ℝ) ≤ physicalPeriod := by
  intro entry he
  simp only [physicalCayleySourceSchedule,cayleyQuerySchedule,List.map_map,Function.comp_def,
    List.mem_map,List.mem_range] at he
  obtain ⟨j,hj,rfl⟩ := he
  exact physicalLinePoint_in_cube y z x _ hx hy hz
    (physicalGrid_mem _ (cayleySteps_spec _ _ _).1 j hj)

/-- Original `physicalLineSamples_accuracy` guarantee for the `PhysicalLine` construction; the complete source hypotheses are retained. -/
theorem physicalLineSamples_accuracy (v : SpatialPoint → SpatialPoint)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hsource : OriginalSpinSourceAccurate v source)
    (y z x t : ℚ) (b : ℕ)
    (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ physicalPeriod)
    (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ physicalPeriod)
    (hz : 0 ≤ (z : ℝ) ∧ (z : ℝ) ≤ physicalPeriod) (ht : (t : ℝ) ∈ Icc 0 1) :
    (∀ j, |((physicalLineSamples source y z x (t,b)).1 j : ℝ)-
      v (sourcePosition (rationalTransversePoint y z,(x : ℝ)*(t : ℝ))) j| ≤ (2^b : ℝ)⁻¹) ∧
    (∀ j, |((physicalLineSamples source y z x (t,b)).2 j : ℝ)-
      (x : ℝ)*fderiv ℝ v (sourcePosition (rationalTransversePoint y z,(x : ℝ)*(t : ℝ)))
        (EuclideanSpace.single 0 1) j| ≤ (2^b : ℝ)⁻¹) := by
  have ha := hsource (physicalLinePoint y z x t) (b+physicalLineOverhead x)
    (physicalLinePoint_in_cube y z x t hx hy hz ht)
  rw [physicalLinePoint_cast] at ha
  have he1 : (2^(b+physicalLineOverhead x) : ℝ)⁻¹ ≤ (2^b : ℝ)⁻¹ := by
    have h : (((2^(b+physicalLineOverhead x) : ℚ)⁻¹ : ℚ) : ℝ) ≤ (((2^b : ℚ)⁻¹ : ℚ) : ℝ) :=
      Rat.cast_le.mpr (physicalLineOverhead_error x b).1
    push_cast at h
    exact h
  have he2 : (x : ℝ)*(2^(b+physicalLineOverhead x) : ℝ)⁻¹ ≤ (2^b : ℝ)⁻¹ := by
    have h : ((x*(2^(b+physicalLineOverhead x) : ℚ)⁻¹ : ℚ) : ℝ) ≤ (((2^b : ℚ)⁻¹ : ℚ) : ℝ) :=
      Rat.cast_le.mpr (physicalLineOverhead_error x b).2
    push_cast at h
    exact h
  constructor
  · intro j
    exact (ha.1 j).trans he1
  · intro j
    change |((x*(source (physicalLinePoint y z x t,b+physicalLineOverhead x)).2 j : ℚ) : ℝ)-
      (x : ℝ)*fderiv ℝ v (sourcePosition (rationalTransversePoint y z,(x : ℝ)*(t : ℝ)))
        (EuclideanSpace.single 0 1) j| ≤ (2^b : ℝ)⁻¹
    rw [Rat.cast_mul,← mul_sub,abs_mul,abs_of_nonneg hx.1]
    exact (mul_le_mul_of_nonneg_left (ha.2 j) hx.1).trans he2

/-- The coefficient accuracy is now derived from the original source accuracy
and its actual derivative bound, rather than supplied as an oracle premise. -/
theorem physicalCoefficientOracle_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (hsource : OriginalSpinSourceAccurate v source) (y z x m1 t : ℚ) (p : ℕ)
    (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ physicalPeriod)
    (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ physicalPeriod)
    (hz : 0 ≤ (z : ℝ) ∧ (z : ℝ) ≤ physicalPeriod) (ht : (t : ℝ) ∈ Icc 0 1)
    (hm1 : 0 ≤ m1)
    (h1 : ∀ u ∈ Icc 0 (x : ℝ), ‖sourceXDerivative v (sourcePosition (rationalTransversePoint y z,u))‖ ≤ (m1 : ℝ)) :
    ‖dyadicCoefficient p (physicalCoefficientOracle source y z x m1 (t,p))-
      normalizedSourceGenerator v (rationalTransversePoint y z) (x : ℝ) (t : ℝ)‖ ≤ (2^p : ℝ)⁻¹ := by
  let w := sourcePosition (rationalTransversePoint y z,(x : ℝ)*(t : ℝ))
  have hmem : (x : ℝ)*(t : ℝ) ∈ Icc 0 (x : ℝ) :=
    ⟨mul_nonneg hx.1 ht.1,by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 hx.1⟩
  have ha := physicalLineSamples_accuracy v source hsource y z x t
    (p+spinCoefficientOverhead (x*m1)) hx hy hz ht
  have he : horizontalCoefficient (sourceQuaternion v w) ((x : ℝ) • sourceXDerivative v w)=
      normalizedSourceGenerator v (rationalTransversePoint y z) (x : ℝ) (t : ℝ) := by
    simp only [normalizedSourceGenerator,sourceHorizontalQuaternion,horizontalCoefficient,mul_smul_comm,smul_smul]
    congr 1
    ring
  have hd : ‖(x : ℝ) • sourceXDerivative v w‖ ≤ ((x*m1 : ℚ) : ℝ) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hx.1,Rat.cast_mul]
    exact mul_le_mul_of_nonneg_left (h1 _ hmem) hx.1
  have h := spinCoefficientOracle_error (x*m1) (mul_nonneg (by exact_mod_cast hx.1) hm1)
    (physicalLineSamples source y z x) t p (sourceQuaternion v w) ((x : ℝ) • sourceXDerivative v w)
    rfl (by simp [sourceXDerivative_eq_spin v hv,spinOfVector])
    ((spinOfVector_norm _).trans (hu _)) hd
    (by rw [he]; exact normalizedSourceGenerator_re v hv hu _ _ _)
    (by intro j; fin_cases j <;> simpa [coefficientSourceQuery,sourceQuaternion,spinOfVector,w] using ha.1 _)
    (by intro j; fin_cases j <;> simpa [coefficientSourceQuery,sourceXDerivative_eq_spin v hv,spinOfVector,w] using ha.2 _)
  rw [he] at h
  exact h

/-- All queried points and precisions are computed from rational physical
data; source accuracy and source first/second derivative bounds suffice.
The exact target has fixed physical parameters, independent of tolerance. -/
theorem physicalCayleyExecution_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (hsource : OriginalSpinSourceAccurate v source) (y z x m1 m2 tolerance : ℚ)
    (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ physicalPeriod)
    (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ physicalPeriod)
    (hz : 0 ≤ (z : ℝ) ∧ (z : ℝ) ≤ physicalPeriod) (hm1 : 0 ≤ m1)
    (ht : 0<tolerance) (ht1 : tolerance ≤ 1)
    (h1 : ∀ u ∈ Icc 0 (x : ℝ), ‖sourceXDerivative v (sourcePosition (rationalTransversePoint y z,u))‖ ≤ (m1 : ℝ))
    (h2 : ∀ u ∈ Icc 0 (x : ℝ), ‖sourceXXDerivative v (sourcePosition (rationalTransversePoint y z,u))‖ ≤ (m2 : ℝ))
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (initial : ℍ) (delta0 : ℝ) (hi : ‖initial-q₀‖ ≤ delta0) :
    ‖initial*decodeCayleyState (physicalCayleyExecution source y z x m1 m2 tolerance)-
      sourceLiftExtension v hv q₀ h₀ (rationalTransversePoint y z,(x : ℝ))‖ ≤ delta0+(tolerance : ℝ) := by
  have hreg := normalizedSourceGenerator_bounds v hv hu (rationalTransversePoint y z) (x : ℝ) hx.1
    (m1 : ℝ) (m2 : ℝ) (by exact_mod_cast hm1) h1 h2
  have hxq : 0 ≤ x := by exact_mod_cast hx.1
  have hK : (0 : ℚ) ≤ x*m1/2 := div_nonneg (mul_nonneg hxq hm1) (by norm_num)
  apply cayleyPlannedSource_error v hv hu q₀ h₀ (rationalTransversePoint y z) (x : ℝ) hx
    (x*m1/2) (x^2*(m1^2+m2)/2) tolerance hK ht ht1
    (physicalCoefficientOracle source y z x m1)
  · simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat] using hreg.1
  · simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_add,Rat.cast_ofNat] using hreg.2
  · intro j hj
    have hD := (cayleySteps_spec (x*m1/2) (x^2*(m1^2+m2)/2) tolerance).1
    have h := physicalCoefficientOracle_error v hv hu source hsource y z x m1
      ((j : ℚ)/(cayleySteps (x*m1/2) (x^2*(m1^2+m2)/2) tolerance : ℚ)) (cayleyPrecision tolerance)
      hx hy hz (physicalGrid_mem _ hD j hj) hm1 h1
    push_cast at h
    exact h
  · exact hi

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
