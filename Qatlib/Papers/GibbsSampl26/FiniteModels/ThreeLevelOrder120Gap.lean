/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120LowFace
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighFace
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120PopulationBounds
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelPopulationMetricBound
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelPopulationTraceComparison
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
# Actual order120 collision gaps and the two remaining physical splits

The complete low-face degree(6,3) and high-face degree(4,2) certificates are
discharged internally, together with the actual population energy estimate.
The resulting physical intervals have factor20 and explicit floor1/60.
Equal-Hamiltonian label swaps cover low210 and high102 without assuming
equality of their original population coordinates or mass matrices.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix MeasureTheory

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120Gap
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelClockRayleighGap
open ThreeLevelClockRayleighAttainment
open ThreeLevelOrder120 ThreeLevelOrder201 ThreeLevelOrder120PopulationBounds
open ThreeLevelPopulationMetricBound ThreeLevelCollisionRelabeling
open ThreeLevelPopulationTraceComparison

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
noncomputable section

/-- Low face gap comparison for the stated finite source data. -/
theorem low_face_gap_comparison (β s : ℝ) (hs : 0 ≤ s)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < plainGap order120 0 s ∧
      plainGap order120 0 s ≤ clockGap order120 β 0 s μ ∧
      clockGap order120 β 0 s μ ≤ 20 * plainGap order120 0 s :=
  ThreeLevelCollisionGap.clockGap_comparison_twenty_all_beta order120 β 0 s 34
    (ThreeLevelOrder120LowFace.collision_scaledStackBounds s hs)
    (low_population_plainEnergy_le s hs) μ

/-- Low face pairwise gap comparison for the stated finite source data. -/
theorem low_face_pairwise_gap_comparison (β s : ℝ) (hs : 0 ≤ s)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    clockGap order120 β 0 s ν ≤ 20 * clockGap order120 β 0 s μ :=
  (low_face_gap_comparison β s hs ν).2.2.trans
    (mul_le_mul_of_nonneg_left (low_face_gap_comparison β s hs μ).2.1
      (by norm_num))

/-- Low face plain gap lower for the stated finite source data. -/
theorem low_face_plain_gap_lower (s : ℝ) (hs : 0 ≤ s) :
    ThreeLevelCollisionGap.collisionGapFloor s ≤ plainGap order120 0 s := by
  rw [ThreeLevelCollisionGap.collisionGapFloor_eq_low]
  exact ThreeLevelPopulationMetricBound.plainGap_lower_explicit order120 0 s 34
    hs
    (ThreeLevelOrder120LowFace.collision_scaledStackBounds s hs)

/-- Low face clock gap lower for the stated finite source data. -/
theorem low_face_clock_gap_lower (β s : ℝ) (hs : 0 ≤ s)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ThreeLevelCollisionGap.collisionGapFloor s ≤ clockGap order120 β 0 s μ :=
  (low_face_plain_gap_lower s hs).trans
    (low_face_gap_comparison β s hs μ).2.1

/-- Low face clock gap attained for the stated finite source data. -/
theorem low_face_clock_gap_attained (β s : ℝ) (hs : 0 ≤ s)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∃ X ∈ unitInputs order120 0 s,
      clockGap order120 β 0 s μ = clockEnergy order120 β 0 s μ X ∧
        ∀ Y ∈ unitInputs order120 0 s,
          clockEnergy order120 β 0 s μ X ≤ clockEnergy order120 β 0 s μ Y :=
  clockGap_attained _ β 0 s 1 34
    (ThreeLevelOrder120LowFace.collision_scaledStackBounds s hs) μ

/-- High face gap comparison for the stated finite source data. -/
theorem high_face_gap_comparison (β S : ℝ) (hS : 0 ≤ S)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < plainGap order120 S 0 ∧
      plainGap order120 S 0 ≤ clockGap order120 β S 0 μ ∧
      clockGap order120 β S 0 μ ≤ 20 * plainGap order120 S 0 :=
  ThreeLevelCollisionGap.clockGap_comparison_twenty_all_beta order120 β S 0 34
    (ThreeLevelOrder120HighFace.collision_scaledStackBounds S hS)
    (high_population_plainEnergy_le S hS) μ

/-- High face pairwise gap comparison for the stated finite source data. -/
theorem high_face_pairwise_gap_comparison (β S : ℝ) (hS : 0 ≤ S)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    clockGap order120 β S 0 ν ≤ 20 * clockGap order120 β S 0 μ :=
  (high_face_gap_comparison β S hS ν).2.2.trans
    (mul_le_mul_of_nonneg_left (high_face_gap_comparison β S hS μ).2.1
      (by norm_num))

/-- High face plain gap lower for the stated finite source data. -/
theorem high_face_plain_gap_lower (S : ℝ) (hS : 0 ≤ S) :
    ThreeLevelCollisionGap.collisionGapFloor S ≤ plainGap order120 S 0 := by
  rw [ThreeLevelCollisionGap.collisionGapFloor_eq_high]
  exact ThreeLevelPopulationMetricBound.plainGap_lower_explicit order120 S 0 34
    (by norm_num)
    (ThreeLevelOrder120HighFace.collision_scaledStackBounds S hS)

/-- High face clock gap lower for the stated finite source data. -/
theorem high_face_clock_gap_lower (β S : ℝ) (hS : 0 ≤ S)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ThreeLevelCollisionGap.collisionGapFloor S ≤ clockGap order120 β S 0 μ :=
  (high_face_plain_gap_lower S hS).trans
    (high_face_gap_comparison β S hS μ).2.1

/-- High face clock gap attained for the stated finite source data. -/
theorem high_face_clock_gap_attained (β S : ℝ) (hS : 0 ≤ S)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∃ X ∈ unitInputs order120 S 0,
      clockGap order120 β S 0 μ = clockEnergy order120 β S 0 μ X ∧
        ∀ Y ∈ unitInputs order120 S 0,
          clockEnergy order120 β S 0 μ X ≤ clockEnergy order120 β S 0 μ Y :=
  clockGap_attained _ β S 0 1 34
    (ThreeLevelOrder120HighFace.collision_scaledStackBounds S hS) μ

end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120Gap
