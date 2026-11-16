/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelPopulationRayleigh
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
# Explicit Hilbert--Schmidt population metric and gap floors

The two actual population seeds have a uniformly bounded Gram trace because
the original projectors have ranks 2,1,1 and the upper spacing is nonnegative.
Orthogonal centering is a contraction for the actual Hilbert--Schmidt form.
The intrinsic population Rayleigh minimum therefore has an explicit positive
amplitude floor. An actual lower stack certificate transfers that floor to the
full complex plain and probability-clock Rayleigh infima, with the original
physical normalization of one twelfth.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder
open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelPopulationMetricBound
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelClockRayleighGap ThreeLevelPopulationRayleigh
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
noncomputable section
/-- Hs Square center le for the stated finite source data. -/
theorem hsSquare_center_le (σ : Perm) (E : Fin 3 → ℝ) (X : Operator 4) :
    hsSquare (orthogonalCenter X (gibbsRoot σ E)) ≤ hsSquare X := by
  let g := gibbsRoot σ E
  let c := hsPair g X / hsPair g g
  have ho : hsInner (c • g) (orthogonalCenter X g) = 0 := by
    rw [hsInner_smul_left]
    have h := actual_center_orthogonal σ E X
    change hsInner g (orthogonalCenter X g) = 0 at h
    rw [h, mul_zero]
  have he : X = c • g + orthogonalCenter X g := by
    simp only [orthogonalCenter, c]
    abel
  have hn := hsSquare_nonneg (c • g)
  have hh := hsSquare_add_of_orthogonal (c • g) (orthogonalCenter X g) ho
  rw [← he] at hh
  linarith

/-- Norm Sq real mul add le for the stated finite source data. -/
theorem normSq_real_mul_add_le (a : ℝ) (c d : ℂ) :
    Complex.normSq ((a : ℂ) * c + d) ≤
      (a^2+1) * (Complex.normSq c + Complex.normSq d) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  nlinarith [sq_nonneg (c.re-a*d.re), sq_nonneg (c.im-a*d.im)]

/-- Hs Square population formula for the stated finite source data. -/
theorem hsSquare_population_formula (σ : Perm) (v : Fin 3 → ℂ) :
    hsSquare (population σ v) =
      ∑ i, (projectorRank (σ i) : ℝ) * Complex.normSq (v i) := by
  rw [hsSquare, hsInner_population_left, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsInner_projector_population, ← mul_assoc, Complex.star_def]
  rw [mul_comm ((starRingEnd ℂ) (v i)) (v i), Complex.mul_conj]
  simp [Complex.mul_re, mul_comm]
/-- Population rank bound for the stated finite source data. -/
theorem population_rank_bound (σ : Perm) :
    (projectorRank (σ 1) : ℝ) + 2 * (projectorRank (σ 2) : ℝ) ≤ 5 := by
  have h12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  generalize h1 : σ 1 = i at *
  generalize h2 : σ 2 = j at *
  fin_cases i <;> fin_cases j <;> norm_num [projectorRank] at *

/-- Seed Combination eq population for the stated finite source data. -/
theorem seedCombination_eq_population (σ : Perm) (s : ℝ) (c d : ℂ) :
    c • seedOne σ s + d • seedTwo σ =
      population σ ![0,c,halfAmplitude s*c+d] := by
  ext i j
  simp [population, seedOne, seedTwo, Fin.sum_univ_succ,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-- Hs Square seed Combination for the stated finite source data. -/
theorem hsSquare_seedCombination (σ : Perm) (s : ℝ) (c d : ℂ) :
    hsSquare (c • seedOne σ s + d • seedTwo σ) =
      (projectorRank (σ 1) : ℝ) * Complex.normSq c +
      (projectorRank (σ 2) : ℝ) * Complex.normSq (halfAmplitude s*c+d) := by
  rw [seedCombination_eq_population, hsSquare_population_formula]
  simp [Fin.sum_univ_succ]

/-- Hs Square seed Combination le five for the stated finite source data. -/
theorem hsSquare_seedCombination_le_five (σ : Perm) (s : ℝ) (hs : 0 ≤ s)
    (c d : ℂ) :
    hsSquare (c • seedOne σ s + d • seedTwo σ) ≤
      5 * (Complex.normSq c + Complex.normSq d) := by
  have ha0 : 0 ≤ Real.exp (-s/2) := (Real.exp_pos _).le
  have ha1 : Real.exp (-s/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have ha2 : Real.exp (-s/2)^2 ≤ 1 := by nlinarith
  have hc := Complex.normSq_nonneg c
  have hd := Complex.normSq_nonneg d
  have hr1 : 0 ≤ (projectorRank (σ 1) : ℝ) := Nat.cast_nonneg _
  have hr2 : 0 ≤ (projectorRank (σ 2) : ℝ) := Nat.cast_nonneg _
  have hh := normSq_real_mul_add_le (Real.exp (-s/2)) c d
  have hh' : Complex.normSq (halfAmplitude s*c+d) ≤
      2 * (Complex.normSq c+Complex.normSq d) := by
    change Complex.normSq ((Real.exp (-s/2) : ℂ)*c+d) ≤ _
    nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (add_nonneg hc hd)]
  rw [hsSquare_seedCombination]
  have hb := population_rank_bound σ
  calc
    _ ≤ (projectorRank (σ 1) : ℝ) * (Complex.normSq c+Complex.normSq d) +
        (projectorRank (σ 2) : ℝ) * (2 * (Complex.normSq c+Complex.normSq d)) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hd) hr1)
        (mul_le_mul_of_nonneg_left hh' hr2)
    _ = ((projectorRank (σ 1) : ℝ)+2*(projectorRank (σ 2) : ℝ)) *
        (Complex.normSq c+Complex.normSq d) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (add_nonneg hc hd)

/-- Hs Square centered seed Combination le five for the stated finite source data. -/
theorem hsSquare_centered_seedCombination_le_five (σ : Perm) (S s : ℝ)
    (hs : 0 ≤ s) (c d : ℂ) :
    hsSquare (orthogonalCenter (c • seedOne σ s + d • seedTwo σ)
      (gibbsRoot σ (lowEnergies S s))) ≤
      5 * (Complex.normSq c + Complex.normSq d) :=
  (hsSquare_center_le σ (lowEnergies S s) _).trans
    (hsSquare_seedCombination_le_five σ s hs c d)

/-- Population hs Square le five for the stated finite source data. -/
theorem population_hsSquare_le_five (σ : Perm) (S s : ℝ) (hs : 0 ≤ s)
    (X : Operator 4) (hf : fastPart σ X = 0)
    (ho : hsInner (gibbsRoot σ (lowEnergies S s)) X = 0) :
    hsSquare X ≤ 5 * (Complex.normSq (firstCoordinate σ S X) +
      Complex.normSq (secondCoordinate σ s X)) := by
  have hcx : orthogonalCenter X (gibbsRoot σ (lowEnergies S s)) = X := by
    simp [orthogonalCenter, hsPair_eq_hsInner, ho]
  have he : X = orthogonalCenter
      (firstCoordinate σ S X • seedOne σ s + secondCoordinate σ s X • seedTwo σ)
      (gibbsRoot σ (lowEnergies S s)) := by
    rw [center_add, center_smul, center_smul]
    have h := actual_centered_decomposition σ S s X
    rw [hcx, hf, add_zero] at h
    exact h
  calc
    hsSquare X = _ := congrArg hsSquare he
    _ ≤ _ := hsSquare_centered_seedCombination_le_five σ S s hs _ _

def gapScale (S s : ℝ) : ℝ :=
  min (min (Complex.normSq (smallAmplitude S)) (Complex.normSq (smallAmplitude s))) 1

/-- Gap Scale pos for the stated finite source data. -/
theorem gapScale_pos (S s : ℝ) : 0 < gapScale S s :=
  lt_min (lt_min (Complex.normSq_pos.mpr (smallAmplitude_ne_zero S))
    (Complex.normSq_pos.mpr (smallAmplitude_ne_zero s))) zero_lt_one

/-- Small Amplitude norm Sq for the stated finite source data. -/
theorem smallAmplitude_normSq (x : ℝ) :
    Complex.normSq (smallAmplitude x) = Real.exp (-x^2/4+x/2) := by
  rw [smallAmplitude, cexp, Complex.normSq_ofReal, ← Real.exp_add]
  congr 1
  ring

/-- Population Minimum lower explicit for the stated finite source data. -/
theorem populationMinimum_lower_explicit (σ : Perm) (S s : ℝ) (hs : 0 ≤ s) :
    min (Complex.normSq (smallAmplitude S)) (Complex.normSq (smallAmplitude s)) / 5 ≤
      populationMinimum σ S s := by
  obtain ⟨X, hX, he, _⟩ := populationMinimum_attained σ S s
  have hh := population_hsSquare_le_five σ S s hs X hX.2 hX.1.2
  rw [hX.1.1] at hh
  have hq : 0 ≤ min (Complex.normSq (smallAmplitude S))
      (Complex.normSq (smallAmplitude s)) :=
    le_min (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hm : min (Complex.normSq (smallAmplitude S)) (Complex.normSq (smallAmplitude s)) *
      (Complex.normSq (firstCoordinate σ S X)+Complex.normSq (secondCoordinate σ s X)) ≤
      invariantMass σ S s X := by
    simp only [invariantMass, hX.2, hsSquare, hsInner_zero_left, Complex.zero_re,
      add_zero, Complex.normSq_mul]
    rw [mul_add]
    exact add_le_add
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (Complex.normSq_nonneg _))
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (Complex.normSq_nonneg _))
  have hh' := mul_le_mul_of_nonneg_left hh hq
  rw [he]
  nlinarith

/-- Gap Scale le five population Minimum for the stated finite source data. -/
theorem gapScale_le_five_populationMinimum (σ : Perm) (S s : ℝ) (hs : 0 ≤ s) :
    gapScale S s ≤ 5 * populationMinimum σ S s := by
  have h := populationMinimum_lower_explicit σ S s hs
  have hg := min_le_left
    (min (Complex.normSq (smallAmplitude S)) (Complex.normSq (smallAmplitude s))) (1:ℝ)
  change gapScale S s ≤ _ at hg
  linarith

/-- Plain Gap lower explicit for the stated finite source data. -/
theorem plainGap_lower_explicit (σ : Perm) (S s B : ℝ) (hs : 0 ≤ s)
    (hcert : ScaledStackBounds σ S s 1 B) :
    gapScale S s / 60 ≤ plainGap σ S s := by
  have hp := plainGap_lower σ S s B hcert
  have hl := gapScale_le_five_populationMinimum σ S s hs
  have hu : gapScale S s ≤ 1 := min_le_right _ _
  have hm : gapScale S s / 5 ≤ min (populationMinimum σ S s) 1 := by
    exact le_min (by linarith) (by linarith)
  linarith

/-- Clock Gap lower explicit for the stated finite source data. -/
theorem clockGap_lower_explicit (σ : Perm) (β S s B : ℝ) (hs : 0 ≤ s)
    (hcert : ScaledStackBounds σ S s 1 B)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    gapScale S s / 60 ≤ clockGap σ β S s μ :=
  (plainGap_lower_explicit σ S s B hs hcert).trans
    (plainGap_le_clockGap σ β S s 1 B hcert μ)


/-- Gap Scale eq exp for the stated finite source data. -/
theorem gapScale_eq_exp (S s : ℝ) :
    gapScale S s =
      min (min (Real.exp (-S^2/4+S/2)) (Real.exp (-s^2/4+s/2))) 1 := by
  simp only [gapScale, smallAmplitude_normSq]

/-- Invariant Mass lower explicit for the stated finite source data. -/
theorem invariantMass_lower_explicit (σ : Perm) (S s : ℝ) (hs : 0 ≤ s)
    (X : Operator 4) (ho : hsInner (gibbsRoot σ (lowEnergies S s)) X = 0) :
    (gapScale S s / 5) * hsSquare X ≤ invariantMass σ S s X := by
  have hl := gapScale_le_five_populationMinimum σ S s hs
  have hu : gapScale S s ≤ 1 := min_le_right _ _
  have hm : gapScale S s / 5 ≤ min (populationMinimum σ S s) 1 :=
    le_min (by linarith) (by linarith)
  exact (mul_le_mul_of_nonneg_right hm (hsSquare_nonneg X)).trans
    (invariantMass_lower σ S s X ho)

end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelPopulationMetricBound
