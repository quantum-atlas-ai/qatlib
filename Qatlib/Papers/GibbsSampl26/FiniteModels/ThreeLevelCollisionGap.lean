/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClockRayleighGap
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelPopulationMetricBound
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionPopulationBounds
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClockRayleighAttainment
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelPermutations
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionFace
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelHighCollisionFace
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.CompleteLattice
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Filter
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OuterMeasure
public import Mathlib.MeasureTheory.Measure.Sum

@[expose] public section


/-!
# Exact full-complex probability-clock gaps on the two collision faces

The normalized energies and the Gibbs-orthogonal Rayleigh infima are the
actual ones. Both finite stack certificates are discharged internally.
The physical thermal interpretation of nonzero dimensionless spacings uses
beta different from zero; the spectral clock definition itself permits zero.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix MeasureTheory
open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionGap
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelClockRayleighGap
open ThreeLevelCollisionRelabeling
open ThreeLevelPopulationMetricBound ThreeLevelPopulationRayleigh
open ThreeLevelCollisionPopulationBounds ThreeLevelClockRayleighAttainment
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
noncomputable section

/-- Low face gap comparison for the stated finite source data. -/
theorem low_face_gap_comparison (β s : ℝ) (hs : 0 ≤ s)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < plainGap (Equiv.refl (Fin 3)) 0 s ∧
      plainGap (Equiv.refl (Fin 3)) 0 s ≤ clockGap (Equiv.refl (Fin 3)) β 0 s μ ∧
      clockGap (Equiv.refl (Fin 3)) β 0 s μ ≤
        34 * plainGap (Equiv.refl (Fin 3)) 0 s := by
  simpa only [div_one] using
    clockGap_comparison (Equiv.refl (Fin 3)) β 0 s 1 34 (by norm_num) (by norm_num)
      (ThreeLevelCollisionFace.collision_scaledStackBounds s hs) μ

/-- High face gap comparison for the stated finite source data. -/
theorem high_face_gap_comparison (β S : ℝ) (hS : 0 ≤ S)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < plainGap (Equiv.refl (Fin 3)) S 0 ∧
      plainGap (Equiv.refl (Fin 3)) S 0 ≤ clockGap (Equiv.refl (Fin 3)) β S 0 μ ∧
      clockGap (Equiv.refl (Fin 3)) β S 0 μ ≤
        34 * plainGap (Equiv.refl (Fin 3)) S 0 := by
  simpa only [div_one] using
    clockGap_comparison (Equiv.refl (Fin 3)) β S 0 1 34 (by norm_num) (by norm_num)
      (ThreeLevelHighCollisionFace.collision_scaledStackBounds S hS) μ

/-- Low face pairwise gap comparison for the stated finite source data. -/
theorem low_face_pairwise_gap_comparison (β s : ℝ) (hs : 0 ≤ s)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    clockGap (Equiv.refl (Fin 3)) β 0 s ν ≤
      34 * clockGap (Equiv.refl (Fin 3)) β 0 s μ := by
  simpa only [div_one] using
    clockGap_pairwise_comparison (Equiv.refl (Fin 3)) β 0 s 1 34 (by norm_num) (by norm_num)
      (ThreeLevelCollisionFace.collision_scaledStackBounds s hs) μ ν

/-- High face pairwise gap comparison for the stated finite source data. -/
theorem high_face_pairwise_gap_comparison (β S : ℝ) (hS : 0 ≤ S)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    clockGap (Equiv.refl (Fin 3)) β S 0 ν ≤
      34 * clockGap (Equiv.refl (Fin 3)) β S 0 μ := by
  simpa only [div_one] using
    clockGap_pairwise_comparison (Equiv.refl (Fin 3)) β S 0 1 34 (by norm_num) (by norm_num)
      (ThreeLevelHighCollisionFace.collision_scaledStackBounds S hS) μ ν

/-- Scalar clock gap eq plain for the stated finite source data. -/
theorem scalar_clock_gap_eq_plain (σ : Perm) (β : ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    clockGap σ β 0 0 μ = plainGap σ 0 0 := by
  simp only [clockGap, plainGap, clockEnergy_zero_spacings, plainEnergy_zero_spacings]

/-- Scalar clock gap positive for the stated finite source data. -/
theorem scalar_clock_gap_positive (β : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < clockGap (Equiv.refl (Fin 3)) β 0 0 μ := by
  have h := low_face_gap_comparison β 0 (by norm_num) μ
  exact h.1.trans_le h.2.1


/-- An explicit positive floor at a collision with remaining dimensionless gap x. -/
def collisionGapFloor (x : ℝ) : ℝ :=
  min (Real.exp (-x^2/4+x/2)) 1 / 60

/-- Collision Gap Floor pos for the stated finite source data. -/
theorem collisionGapFloor_pos (x : ℝ) : 0 < collisionGapFloor x :=
  div_pos (lt_min (Real.exp_pos _) zero_lt_one) (by norm_num)

/-- Collision Gap Floor eq low for the stated finite source data. -/
theorem collisionGapFloor_eq_low (s : ℝ) :
    collisionGapFloor s = gapScale 0 s / 60 := by
  rw [gapScale_eq_exp, collisionGapFloor]
  congr 1
  simp [min_comm]

/-- Collision Gap Floor eq high for the stated finite source data. -/
theorem collisionGapFloor_eq_high (S : ℝ) :
    collisionGapFloor S = gapScale S 0 / 60 := by
  rw [gapScale_eq_exp, collisionGapFloor]
  congr 1
  simp

/-- Collision Gap Floor small spacing for the stated finite source data. -/
theorem collisionGapFloor_small_spacing (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2) :
    collisionGapFloor x = 1/60 := by
  have he : 0 ≤ -x^2/4+x/2 := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hx2)]
  have h := Real.one_le_exp_iff.mpr he
  rw [collisionGapFloor, min_eq_right h]

/-- Low face plain gap lower for the stated finite source data. -/
theorem low_face_plain_gap_lower (s : ℝ) (hs : 0 ≤ s) :
    collisionGapFloor s ≤ plainGap (Equiv.refl (Fin 3)) 0 s := by
  rw [collisionGapFloor_eq_low]
  exact plainGap_lower_explicit _ 0 s 34 hs
    (ThreeLevelCollisionFace.collision_scaledStackBounds s hs)

/-- High face plain gap lower for the stated finite source data. -/
theorem high_face_plain_gap_lower (S : ℝ) (hS : 0 ≤ S) :
    collisionGapFloor S ≤ plainGap (Equiv.refl (Fin 3)) S 0 := by
  rw [collisionGapFloor_eq_high]
  exact plainGap_lower_explicit _ S 0 34 (by norm_num)
    (ThreeLevelHighCollisionFace.collision_scaledStackBounds S hS)

/-- Low face clock gap lower for the stated finite source data. -/
theorem low_face_clock_gap_lower (β s : ℝ) (hs : 0 ≤ s)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    collisionGapFloor s ≤ clockGap (Equiv.refl (Fin 3)) β 0 s μ :=
  (low_face_plain_gap_lower s hs).trans (low_face_gap_comparison β s hs μ).2.1

/-- High face clock gap lower for the stated finite source data. -/
theorem high_face_clock_gap_lower (β S : ℝ) (hS : 0 ≤ S)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    collisionGapFloor S ≤ clockGap (Equiv.refl (Fin 3)) β S 0 μ :=
  (high_face_plain_gap_lower S hS).trans (high_face_gap_comparison β S hS μ).2.1

/-- Both actual source premises are discharged: no finite certificate or
external population minimum remains in the factor-twenty conclusion. -/
theorem low_face_gap_comparison_twenty (β s : ℝ) (hs : 0 ≤ s)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < plainGap (Equiv.refl (Fin 3)) 0 s ∧
      plainGap (Equiv.refl (Fin 3)) 0 s ≤ clockGap (Equiv.refl (Fin 3)) β 0 s μ ∧
      clockGap (Equiv.refl (Fin 3)) β 0 s μ ≤
        20 * plainGap (Equiv.refl (Fin 3)) 0 s :=
  clockGap_comparison_twenty _ β 0 s 34
    (ThreeLevelCollisionFace.collision_scaledStackBounds s hs)
    (low_population_plainEnergy_le s hs) μ

/-- High face gap comparison twenty for the stated finite source data. -/
theorem high_face_gap_comparison_twenty (β S : ℝ) (hS : 0 ≤ S)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < plainGap (Equiv.refl (Fin 3)) S 0 ∧
      plainGap (Equiv.refl (Fin 3)) S 0 ≤ clockGap (Equiv.refl (Fin 3)) β S 0 μ ∧
      clockGap (Equiv.refl (Fin 3)) β S 0 μ ≤
        20 * plainGap (Equiv.refl (Fin 3)) S 0 :=
  clockGap_comparison_twenty _ β S 0 34
    (ThreeLevelHighCollisionFace.collision_scaledStackBounds S hS)
    (high_population_plainEnergy_le S hS) μ

/-- Low face pairwise gap twenty for the stated finite source data. -/
theorem low_face_pairwise_gap_twenty (β s : ℝ) (hs : 0 ≤ s)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    clockGap (Equiv.refl (Fin 3)) β 0 s ν ≤
      20 * clockGap (Equiv.refl (Fin 3)) β 0 s μ :=
  (low_face_gap_comparison_twenty β s hs ν).2.2.trans
    (mul_le_mul_of_nonneg_left (low_face_gap_comparison β s hs μ).2.1 (by norm_num))

/-- High face pairwise gap twenty for the stated finite source data. -/
theorem high_face_pairwise_gap_twenty (β S : ℝ) (hS : 0 ≤ S)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    clockGap (Equiv.refl (Fin 3)) β S 0 ν ≤
      20 * clockGap (Equiv.refl (Fin 3)) β S 0 μ :=
  (high_face_gap_comparison_twenty β S hS ν).2.2.trans
    (mul_le_mul_of_nonneg_left (high_face_gap_comparison β S hS μ).2.1 (by norm_num))

/-- Low face clock gap attained for the stated finite source data. -/
theorem low_face_clock_gap_attained (β s : ℝ) (hs : 0 ≤ s)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∃ X ∈ unitInputs (Equiv.refl (Fin 3)) 0 s,
      clockGap (Equiv.refl (Fin 3)) β 0 s μ = clockEnergy (Equiv.refl (Fin 3)) β 0 s μ X ∧
        ∀ Y ∈ unitInputs (Equiv.refl (Fin 3)) 0 s,
          clockEnergy (Equiv.refl (Fin 3)) β 0 s μ X ≤ clockEnergy (Equiv.refl (Fin 3)) β 0 s μ Y :=
  clockGap_attained _ β 0 s 1 34 (ThreeLevelCollisionFace.collision_scaledStackBounds s hs) μ

/-- High face clock gap attained for the stated finite source data. -/
theorem high_face_clock_gap_attained (β S : ℝ) (hS : 0 ≤ S)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∃ X ∈ unitInputs (Equiv.refl (Fin 3)) S 0,
      clockGap (Equiv.refl (Fin 3)) β S 0 μ = clockEnergy (Equiv.refl (Fin 3)) β S 0 μ X ∧
        ∀ Y ∈ unitInputs (Equiv.refl (Fin 3)) S 0,
          clockEnergy (Equiv.refl (Fin 3)) β S 0 μ X ≤ clockEnergy (Equiv.refl (Fin 3)) β S 0 μ Y :=
  clockGap_attained _ β S 0 1 34 (ThreeLevelHighCollisionFace.collision_scaledStackBounds S hS) μ

/-- Spectral clock Energy zero beta for the stated finite source data. -/
theorem spectral_clockEnergy_zero_beta (σ : Perm) (S s : ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Operator 4) :
    clockEnergy σ 0 S s μ X = plainEnergy σ S s X := by
  have he : physicalEnergies 0 S s = fun _ => 0 := by
    funext i
    change lowEnergies S s i / 0 = 0
    simp
  have ht (t : ℝ) : timeConjugation σ (fun _ => 0) t X = X := by
    simp [timeConjugation, timeUnitary, bohrPhase, population_one]
  simp [clockEnergy, he, ht]

/-- Spectral clock Gap zero beta for the stated finite source data. -/
theorem spectral_clockGap_zero_beta (σ : Perm) (S s : ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    clockGap σ 0 S s μ = plainGap σ S s := by
  simp only [clockGap, plainGap, spectral_clockEnergy_zero_beta]

/-- Clock Gap comparison twenty all beta for the stated finite source data. -/
theorem clockGap_comparison_twenty_all_beta (σ : Perm) (β S s B : ℝ)
    (hcert : ScaledStackBounds σ S s 1 B)
    (hpop : ∀ X : Operator 4, fastPart σ X = 0 →
      plainEnergy σ S s X ≤ (5/3 : ℝ) * invariantMass σ S s X)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < plainGap σ S s ∧
      plainGap σ S s ≤ clockGap σ β S s μ ∧
      clockGap σ β S s μ ≤ 20 * plainGap σ S s :=
  clockGap_comparison_twenty σ β S s B hcert hpop μ


/-- Low face gap comparison twenty all beta for the stated finite source data. -/
theorem low_face_gap_comparison_twenty_all_beta (β x : ℝ) (hx : 0 ≤ x)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < plainGap (Equiv.refl (Fin 3)) 0 x ∧
      plainGap (Equiv.refl (Fin 3)) 0 x ≤ clockGap (Equiv.refl (Fin 3)) β 0 x μ ∧
      clockGap (Equiv.refl (Fin 3)) β 0 x μ ≤
        20 * plainGap (Equiv.refl (Fin 3)) 0 x :=
  clockGap_comparison_twenty_all_beta _ β 0 x 34
    (ThreeLevelCollisionFace.collision_scaledStackBounds x hx)
    (low_population_plainEnergy_le x hx) μ


/-- High face gap comparison twenty all beta for the stated finite source data. -/
theorem high_face_gap_comparison_twenty_all_beta (β x : ℝ) (hx : 0 ≤ x)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < plainGap (Equiv.refl (Fin 3)) x 0 ∧
      plainGap (Equiv.refl (Fin 3)) x 0 ≤ clockGap (Equiv.refl (Fin 3)) β x 0 μ ∧
      clockGap (Equiv.refl (Fin 3)) β x 0 μ ≤
        20 * plainGap (Equiv.refl (Fin 3)) x 0 :=
  clockGap_comparison_twenty_all_beta _ β x 0 34
    (ThreeLevelHighCollisionFace.collision_scaledStackBounds x hx)
    (high_population_plainEnergy_le x hx) μ



end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionGap
