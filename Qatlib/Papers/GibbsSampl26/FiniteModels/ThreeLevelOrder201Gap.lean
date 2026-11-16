/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201LowFace
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201HighFace
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201PopulationBounds
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201MetricBound
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
# Stronger physical collision gap intervals for order201

The two actual full source certificates and the population energy bound are
discharged internally. The complete quadratic forms retain factor34, while
the attained population trial gives probability-clock Rayleigh gap factor64/5.
The order-specific Hilbert--Schmidt metric supplies a positive1/42 floor.
The two degenerate label exchanges cover two additional ordered faces, using
only equality of the actual Hamiltonian, not equality of coordinate metrics.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix MeasureTheory

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201Gap
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelClockRayleighGap
open ThreeLevelClockRayleighAttainment
open ThreeLevelOrder201 ThreeLevelOrder201PopulationBounds
open ThreeLevelPopulationMetricBound ThreeLevelCollisionRelabeling
open ThreeLevelPopulationTraceComparison

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
noncomputable section

def order201GapFloor (x : ℝ) : ℝ :=
  min (Real.exp (-x^2/4+x/2)) 1 / 42

/-- Order201 Gap Floor pos for the stated finite source data. -/
theorem order201GapFloor_pos (x : ℝ) : 0 < order201GapFloor x :=
  div_pos (lt_min (Real.exp_pos _) zero_lt_one) (by norm_num)

/-- Order201 Gap Floor eq low for the stated finite source data. -/
theorem order201GapFloor_eq_low (s : ℝ) :
    order201GapFloor s = gapScale 0 s / 42 := by
  rw [gapScale_eq_exp, order201GapFloor]
  congr 1
  simp [min_comm]

/-- Order201 Gap Floor eq high for the stated finite source data. -/
theorem order201GapFloor_eq_high (S : ℝ) :
    order201GapFloor S = gapScale S 0 / 42 := by
  rw [gapScale_eq_exp, order201GapFloor]
  congr 1
  simp

/-- Order201 Gap Floor small spacing for the stated finite source data. -/
theorem order201GapFloor_small_spacing (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2) :
    order201GapFloor x = 1/42 := by
  have he : 0 ≤ -x^2/4+x/2 := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hx2)]
  rw [order201GapFloor, min_eq_right (Real.one_le_exp_iff.mpr he)]

/-- Low face gap comparison for the stated finite source data. -/
theorem low_face_gap_comparison (β s : ℝ) (hs : 0 ≤ s)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < plainGap order201 0 s ∧
      plainGap order201 0 s ≤ clockGap order201 β 0 s μ ∧
      clockGap order201 β 0 s μ ≤ (64/5 : ℝ) * plainGap order201 0 s :=
  clockGap_comparison_sixty_four_fifths order201 β 0 s 34
    (ThreeLevelOrder201LowFace.collision_scaledStackBounds s hs)
    (low_population_plainEnergy_le s hs) μ

/-- Low face pairwise gap comparison for the stated finite source data. -/
theorem low_face_pairwise_gap_comparison (β s : ℝ) (hs : 0 ≤ s)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    clockGap order201 β 0 s ν ≤ (64/5 : ℝ) * clockGap order201 β 0 s μ :=
  (low_face_gap_comparison β s hs ν).2.2.trans
    (mul_le_mul_of_nonneg_left (low_face_gap_comparison β s hs μ).2.1
      (by norm_num))

/-- Low face plain gap lower for the stated finite source data. -/
theorem low_face_plain_gap_lower (s : ℝ) (hs : 0 ≤ s) :
    order201GapFloor s ≤ plainGap order201 0 s := by
  rw [order201GapFloor_eq_low]
  exact ThreeLevelOrder201MetricBound.plainGap_lower_explicit 0 s 34
    hs
    (ThreeLevelOrder201LowFace.collision_scaledStackBounds s hs)

/-- Low face clock gap lower for the stated finite source data. -/
theorem low_face_clock_gap_lower (β s : ℝ) (hs : 0 ≤ s)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    order201GapFloor s ≤ clockGap order201 β 0 s μ :=
  (low_face_plain_gap_lower s hs).trans
    (low_face_gap_comparison β s hs μ).2.1

/-- Low face clock gap attained for the stated finite source data. -/
theorem low_face_clock_gap_attained (β s : ℝ) (hs : 0 ≤ s)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∃ X ∈ unitInputs order201 0 s,
      clockGap order201 β 0 s μ = clockEnergy order201 β 0 s μ X ∧
        ∀ Y ∈ unitInputs order201 0 s,
          clockEnergy order201 β 0 s μ X ≤ clockEnergy order201 β 0 s μ Y :=
  clockGap_attained _ β 0 s 1 34
    (ThreeLevelOrder201LowFace.collision_scaledStackBounds s hs) μ

/-- High face gap comparison for the stated finite source data. -/
theorem high_face_gap_comparison (β S : ℝ) (hS : 0 ≤ S)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < plainGap order201 S 0 ∧
      plainGap order201 S 0 ≤ clockGap order201 β S 0 μ ∧
      clockGap order201 β S 0 μ ≤ (64/5 : ℝ) * plainGap order201 S 0 :=
  clockGap_comparison_sixty_four_fifths order201 β S 0 34
    (ThreeLevelOrder201HighFace.collision_scaledStackBounds S hS)
    (high_population_plainEnergy_le S hS) μ

/-- High face pairwise gap comparison for the stated finite source data. -/
theorem high_face_pairwise_gap_comparison (β S : ℝ) (hS : 0 ≤ S)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    clockGap order201 β S 0 ν ≤ (64/5 : ℝ) * clockGap order201 β S 0 μ :=
  (high_face_gap_comparison β S hS ν).2.2.trans
    (mul_le_mul_of_nonneg_left (high_face_gap_comparison β S hS μ).2.1
      (by norm_num))

/-- High face plain gap lower for the stated finite source data. -/
theorem high_face_plain_gap_lower (S : ℝ) (hS : 0 ≤ S) :
    order201GapFloor S ≤ plainGap order201 S 0 := by
  rw [order201GapFloor_eq_high]
  exact ThreeLevelOrder201MetricBound.plainGap_lower_explicit S 0 34
    (by norm_num)
    (ThreeLevelOrder201HighFace.collision_scaledStackBounds S hS)

/-- High face clock gap lower for the stated finite source data. -/
theorem high_face_clock_gap_lower (β S : ℝ) (hS : 0 ≤ S)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    order201GapFloor S ≤ clockGap order201 β S 0 μ :=
  (high_face_plain_gap_lower S hS).trans
    (high_face_gap_comparison β S hS μ).2.1

/-- High face clock gap attained for the stated finite source data. -/
theorem high_face_clock_gap_attained (β S : ℝ) (hS : 0 ≤ S)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∃ X ∈ unitInputs order201 S 0,
      clockGap order201 β S 0 μ = clockEnergy order201 β S 0 μ X ∧
        ∀ Y ∈ unitInputs order201 S 0,
          clockEnergy order201 β S 0 μ X ≤ clockEnergy order201 β S 0 μ Y :=
  clockGap_attained _ β S 0 1 34
    (ThreeLevelOrder201HighFace.collision_scaledStackBounds S hS) μ

end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201Gap
