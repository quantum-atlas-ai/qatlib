/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionGap
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
# Population trials and the full-source trace cap

The population trial coefficient is retained as a parameter instead of fixed
at 5/3. Combining the attained population minimum with the actual six-source
16/15 trace trial gives the comparison factor max (12*C) (64/5). For C=1
this yields 64/5; for C=5/3 it recovers the established factor twenty.
The theorem requires the actual source certificate and the actual population
energy premise. It does not assert them for any new physical face.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix MeasureTheory

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelPopulationTraceComparison
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelClockRayleighGap
open ThreeLevelPopulationRayleigh

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

noncomputable section

def comparisonFactor (C : ℝ) : ℝ := max (12*C) (64/5)

/-- Comparison Factor pos for the stated finite source data. -/
theorem comparisonFactor_pos (C : ℝ) : 0 < comparisonFactor C :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 64/5) (le_max_right _ _)

/-- Comparison Factor one for the stated finite source data. -/
theorem comparisonFactor_one : comparisonFactor 1 = 64/5 := by
  norm_num [comparisonFactor]

/-- Comparison Factor five thirds for the stated finite source data. -/
theorem comparisonFactor_five_thirds : comparisonFactor (5/3) = 20 := by
  norm_num [comparisonFactor]

/-- Clock Gap le scaled population Minimum for the stated finite source data. -/
theorem clockGap_le_scaled_populationMinimum (σ : Perm) (β S s C : ℝ)
    (hpop : ∀ X : Operator 4, fastPart σ X = 0 →
      plainEnergy σ S s X ≤ C * invariantMass σ S s X)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    clockGap σ β S s μ ≤ C * populationMinimum σ S s := by
  obtain ⟨X, hX, he, _⟩ := populationMinimum_attained σ S s
  calc
    clockGap σ β S s μ ≤ clockEnergy σ β S s μ X :=
      clockGap_le σ β S s μ X hX.1
    _ = plainEnergy σ S s X :=
      clockEnergy_eq_plain_of_fastPart_zero σ β S s μ X hX.2
    _ ≤ C * invariantMass σ S s X := hpop X hX.2
    _ = C * populationMinimum σ S s := by rw [← he]

/-- Clock Gap le min population trace for the stated finite source data. -/
theorem clockGap_le_min_population_trace (σ : Perm) (β S s C : ℝ)
    (hpop : ∀ X : Operator 4, fastPart σ X = 0 →
      plainEnergy σ S s X ≤ C * invariantMass σ S s X)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    clockGap σ β S s μ ≤ min (C * populationMinimum σ S s) (16/15) :=
  le_min (clockGap_le_scaled_populationMinimum σ β S s C hpop μ)
    (clockGap_le_sixteen_fifteenths σ β S s μ)

/-- Clock Gap le factor plain Gap for the stated finite source data. -/
theorem clockGap_le_factor_plainGap (σ : Perm) (β S s B C : ℝ)
    (hC : 0 ≤ C)
    (hcert : ScaledStackBounds σ S s 1 B)
    (hpop : ∀ X : Operator 4, fastPart σ X = 0 →
      plainEnergy σ S s X ≤ C * invariantMass σ S s X)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    clockGap σ β S s μ ≤ comparisonFactor C * plainGap σ S s := by
  have hl := plainGap_lower σ S s B hcert
  have hp := (plainGap_pos σ S s 1 B (by norm_num) hcert).le
  by_cases hmin : populationMinimum σ S s ≤ 1
  · rw [min_eq_left hmin] at hl
    have hpopmin : populationMinimum σ S s ≤ 12 * plainGap σ S s := by linarith
    calc
      _ ≤ C * populationMinimum σ S s :=
        clockGap_le_scaled_populationMinimum σ β S s C hpop μ
      _ ≤ C * (12 * plainGap σ S s) := mul_le_mul_of_nonneg_left hpopmin hC
      _ = (12*C) * plainGap σ S s := by ring
      _ ≤ comparisonFactor C * plainGap σ S s :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hp
  · rw [min_eq_right (le_of_not_ge hmin)] at hl
    calc
      _ ≤ 16/15 := clockGap_le_sixteen_fifteenths σ β S s μ
      _ ≤ (64/5 : ℝ) * plainGap σ S s := by linarith
      _ ≤ comparisonFactor C * plainGap σ S s :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hp

/-- The zero-beta spectral convention is included; physical identification
with nonzero dimensionless spacings still requires beta different from zero. -/
theorem clockGap_comparison (σ : Perm) (β S s B C : ℝ) (hC : 0 ≤ C)
    (hcert : ScaledStackBounds σ S s 1 B)
    (hpop : ∀ X : Operator 4, fastPart σ X = 0 →
      plainEnergy σ S s X ≤ C * invariantMass σ S s X)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < plainGap σ S s ∧
      plainGap σ S s ≤ clockGap σ β S s μ ∧
      clockGap σ β S s μ ≤ comparisonFactor C * plainGap σ S s := by
  have hp := plainGap_pos σ S s 1 B (by norm_num) hcert
  refine ⟨hp, plainGap_le_clockGap σ β S s 1 B hcert μ, ?_⟩
  exact clockGap_le_factor_plainGap σ β S s B C hC hcert hpop μ


/-- Clock Gap pairwise comparison for the stated finite source data. -/
theorem clockGap_pairwise_comparison (σ : Perm) (β S s B C : ℝ) (hC : 0 ≤ C)
    (hcert : ScaledStackBounds σ S s 1 B)
    (hpop : ∀ X : Operator 4, fastPart σ X = 0 →
      plainEnergy σ S s X ≤ C * invariantMass σ S s X)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    clockGap σ β S s ν ≤ comparisonFactor C * clockGap σ β S s μ :=
  (clockGap_comparison σ β S s B C hC hcert hpop ν).2.2.trans
    (mul_le_mul_of_nonneg_left
      (plainGap_le_clockGap σ β S s 1 B hcert μ) (comparisonFactor_pos C).le)

/-- Clock Gap comparison sixty four fifths for the stated finite source data. -/
theorem clockGap_comparison_sixty_four_fifths (σ : Perm) (β S s B : ℝ)
    (hcert : ScaledStackBounds σ S s 1 B)
    (hpop : ∀ X : Operator 4, fastPart σ X = 0 →
      plainEnergy σ S s X ≤ invariantMass σ S s X)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < plainGap σ S s ∧
      plainGap σ S s ≤ clockGap σ β S s μ ∧
      clockGap σ β S s μ ≤ (64/5 : ℝ) * plainGap σ S s := by
  have h := clockGap_comparison σ β S s B 1 (by norm_num) hcert
    (by simpa only [one_mul] using hpop) μ
  simpa only [comparisonFactor_one] using h


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelPopulationTraceComparison
