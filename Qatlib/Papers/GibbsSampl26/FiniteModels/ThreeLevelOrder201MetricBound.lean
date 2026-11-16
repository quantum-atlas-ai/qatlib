/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelPopulationMetricBound
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrderCoordinates
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
# The sharper order201 Hilbert--Schmidt population metric

The actual ordered seed ranks are 2 and 1. A weighted complex Young inequality
bounds their whole Gram by 7/2, and actual Gibbs-orthogonal centering contracts
the Hilbert--Schmidt form. This improves the explicit normalized Rayleigh floor
to gapScale/42 whenever the actual full-source lower certificate is supplied.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201MetricBound
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelClockRayleighGap ThreeLevelPopulationRayleigh
open ThreeLevelPopulationMetricBound ThreeLevelOrder201
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
noncomputable section

/-- Norm Sq add le weighted for the stated finite source data. -/
theorem normSq_add_le_weighted (c d : ℂ) :
    Complex.normSq (c+d) ≤
      (3/2 : ℝ)*Complex.normSq c + 3*Complex.normSq d := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (c.re-2*d.re), sq_nonneg (c.im-2*d.im)]

/-- Hs Square seed Combination order201 for the stated finite source data. -/
theorem hsSquare_seedCombination_order201 (s : ℝ) (c d : ℂ) :
    hsSquare (c • seedOne order201 s+d • seedTwo order201) =
      2*Complex.normSq c + Complex.normSq (halfAmplitude s*c+d) := by
  have h1 : projectorRank (order201 1) = 2 := by decide
  have h2 : projectorRank (order201 2) = 1 := by decide
  rw [hsSquare_seedCombination, h1, h2]
  norm_num

/-- Hs Square seed Combination le seven halves for the stated finite source data. -/
theorem hsSquare_seedCombination_le_seven_halves (s : ℝ) (hs : 0 ≤ s) (c d : ℂ) :
    hsSquare (c • seedOne order201 s+d • seedTwo order201) ≤
      (7/2 : ℝ)*(Complex.normSq c+Complex.normSq d) := by
  have ha0 : 0 ≤ Real.exp (-s/2) := (Real.exp_pos _).le
  have ha1 : Real.exp (-s/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have ha2 : Real.exp (-s/2)^2 ≤ 1 := by nlinarith
  have hh := normSq_add_le_weighted ((Real.exp (-s/2) : ℂ)*c) d
  rw [Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two] at hh
  have hc := mul_le_mul_of_nonneg_right ha2 (Complex.normSq_nonneg c)
  rw [hsSquare_seedCombination_order201]
  change 2*Complex.normSq c+
    Complex.normSq ((Real.exp (-s/2) : ℂ)*c+d) ≤ _
  nlinarith [Complex.normSq_nonneg d]

/-- Hs Square centered seed Combination le seven halves for the stated finite source data. -/
theorem hsSquare_centered_seedCombination_le_seven_halves (S s : ℝ)
    (hs : 0 ≤ s) (c d : ℂ) :
    hsSquare (orthogonalCenter (c • seedOne order201 s+d • seedTwo order201)
      (gibbsRoot order201 (lowEnergies S s))) ≤
      (7/2 : ℝ)*(Complex.normSq c+Complex.normSq d) :=
  (hsSquare_center_le order201 (lowEnergies S s) _).trans
    (hsSquare_seedCombination_le_seven_halves s hs c d)

/-- Population hs Square le seven halves for the stated finite source data. -/
theorem population_hsSquare_le_seven_halves (S s : ℝ) (hs : 0 ≤ s)
    (X : Operator 4) (hf : fastPart order201 X = 0)
    (ho : hsInner (gibbsRoot order201 (lowEnergies S s)) X = 0) :
    hsSquare X ≤ (7/2 : ℝ) * (Complex.normSq (firstCoordinate order201 S X) +
      Complex.normSq (secondCoordinate order201 s X)) := by
  have hcx : orthogonalCenter X (gibbsRoot order201 (lowEnergies S s)) = X := by
    simp [orthogonalCenter, hsPair_eq_hsInner, ho]
  have he : X = orthogonalCenter
      (firstCoordinate order201 S X • seedOne order201 s + secondCoordinate order201 s X • seedTwo order201)
      (gibbsRoot order201 (lowEnergies S s)) := by
    rw [center_add, center_smul, center_smul]
    have h := actual_centered_decomposition order201 S s X
    rw [hcx, hf, add_zero] at h
    exact h
  calc
    hsSquare X = _ := congrArg hsSquare he
    _ ≤ _ := hsSquare_centered_seedCombination_le_seven_halves S s hs _ _

/-- Population Minimum lower explicit for the stated finite source data. -/
theorem populationMinimum_lower_explicit (S s : ℝ) (hs : 0 ≤ s) :
    min (Complex.normSq (smallAmplitude S)) (Complex.normSq (smallAmplitude s)) * 2 / 7 ≤
      populationMinimum order201 S s := by
  obtain ⟨X, hX, he, _⟩ := populationMinimum_attained order201 S s
  have hh := population_hsSquare_le_seven_halves S s hs X hX.2 hX.1.2
  rw [hX.1.1] at hh
  have hq : 0 ≤ min (Complex.normSq (smallAmplitude S))
      (Complex.normSq (smallAmplitude s)) :=
    le_min (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hm : min (Complex.normSq (smallAmplitude S)) (Complex.normSq (smallAmplitude s)) *
      (Complex.normSq (firstCoordinate order201 S X)+Complex.normSq (secondCoordinate order201 s X)) ≤
      invariantMass order201 S s X := by
    simp only [invariantMass, hX.2, hsSquare, hsInner_zero_left, Complex.zero_re,
      add_zero, Complex.normSq_mul]
    rw [mul_add]
    exact add_le_add
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (Complex.normSq_nonneg _))
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (Complex.normSq_nonneg _))
  have hh' := mul_le_mul_of_nonneg_left hh hq
  rw [he]
  nlinarith

/-- Gap Scale le seven halves population Minimum for the stated finite source data. -/
theorem gapScale_le_seven_halves_populationMinimum (S s : ℝ) (hs : 0 ≤ s) :
    gapScale S s ≤ (7/2 : ℝ) * populationMinimum order201 S s := by
  have h := populationMinimum_lower_explicit S s hs
  have hg := min_le_left
    (min (Complex.normSq (smallAmplitude S)) (Complex.normSq (smallAmplitude s))) (1:ℝ)
  change gapScale S s ≤ _ at hg
  linarith

/-- Plain Gap lower explicit for the stated finite source data. -/
theorem plainGap_lower_explicit (S s B : ℝ) (hs : 0 ≤ s)
    (hcert : ScaledStackBounds order201 S s 1 B) :
    gapScale S s / 42 ≤ plainGap order201 S s := by
  have hp := plainGap_lower order201 S s B hcert
  have hl := gapScale_le_seven_halves_populationMinimum S s hs
  have hu : gapScale S s ≤ 1 := min_le_right _ _
  have hm : gapScale S s * 2 / 7 ≤ min (populationMinimum order201 S s) 1 := by
    exact le_min (by linarith) (by linarith)
  linarith

/-- Clock Gap lower explicit for the stated finite source data. -/
theorem clockGap_lower_explicit (β S s B : ℝ) (hs : 0 ≤ s)
    (hcert : ScaledStackBounds order201 S s 1 B)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    gapScale S s / 42 ≤ clockGap order201 β S s μ :=
  (plainGap_lower_explicit S s B hs hcert).trans
    (plainGap_le_clockGap order201 β S s 1 B hcert μ)


/-- Invariant Mass lower explicit for the stated finite source data. -/
theorem invariantMass_lower_explicit (S s : ℝ) (hs : 0 ≤ s)
    (X : Operator 4) (ho : hsInner (gibbsRoot order201 (lowEnergies S s)) X = 0) :
    (gapScale S s * 2 / 7) * hsSquare X ≤ invariantMass order201 S s X := by
  have hl := gapScale_le_seven_halves_populationMinimum S s hs
  have hu : gapScale S s ≤ 1 := min_le_right _ _
  have hm : gapScale S s * 2 / 7 ≤ min (populationMinimum order201 S s) 1 :=
    le_min (by linarith) (by linarith)
  exact (mul_le_mul_of_nonneg_right hm (hsSquare_nonneg X)).trans
    (invariantMass_lower order201 S s X ho)

end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201MetricBound
